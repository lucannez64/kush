//! The evaluator as a word-level machine over the MIR (FND-EVAL-MACHINE,
//! docs/mir-design.md section 9).
//!
//! A program's values are the words native code uses, with native's
//! layouts. Memory is a set of byte allocations; a pointer is the word
//! `(allocation + 1) << 32 | offset`, and every access is checked against a
//! live allocation. The call stack is explicit, so a task can later be a
//! stack of its own. Bodies are built without the loop passes: those are
//! code-generation choices, not semantics.
//!
//! The machine grows one node at a time. Until it covers a construct, it
//! stops with [`Stop::Unsupported`] and the tree evaluator stays the
//! reference.

use super::*;
use crate::Diagnostic;
use crate::eval::MemoryStats;
use std::io::{Read, Write};
use std::rc::Rc;

mod alloc;
mod buffers;

/// The words of a value.
type Words = Vec<i64>;

/// Why a run ended without a result.
#[derive(Debug)]
pub enum Stop {
    /// A Kush panic, or an error the evaluator reports (an exhausted
    /// computation budget), with the tree evaluator's message.
    Panic(Diagnostic),
    /// A construct the machine does not cover yet.
    Unsupported(String),
    /// The program broke a machine invariant (an access outside a live
    /// allocation, say). A checked program never does.
    Fault(String),
}

type Run<T> = std::result::Result<T, Stop>;

fn unsupported<T>(what: impl Into<String>) -> Run<T> {
    Err(Stop::Unsupported(what.into()))
}
/// A Kush panic with the tree evaluator's message.
fn panic_at<T>(span: Span, message: &str) -> Run<T> {
    Err(Stop::Panic(Diagnostic::new(span, message)))
}
fn fault<T>(what: impl Into<String>) -> Run<T> {
    Err(Stop::Fault(what.into()))
}

/// Code pointers live in their own range of words.
const CODE: i64 = 1 << 62;
/// A closure environment's first word: its drop glue, by index.
const DROP: i64 = 1 << 61;

struct Allocation {
    bytes: Vec<u8>,
    live: bool,
    /// From the runtime's allocator (counted in the stats), not a frame.
    heap: bool,
}

#[derive(Default)]
struct Memory {
    allocations: Vec<Allocation>,
    live_heap: usize,
    stats: MemoryStats,
}

impl Memory {
    fn allocate(&mut self, bytes: usize, heap: bool) -> i64 {
        let id = self.allocations.len();
        self.allocations.push(Allocation {
            bytes: vec![0; bytes],
            live: true,
            heap,
        });
        if heap {
            self.live_heap += 1;
            self.stats.allocations += 1;
            self.stats.peak_live = self.stats.peak_live.max(self.live_heap);
        }
        (id as i64 + 1) << 32
    }
    /// The allocation and offset a pointer names.
    fn locate(&self, pointer: i64, bytes: usize) -> Run<(usize, usize)> {
        if pointer & CODE != 0 || pointer >> 32 <= 0 {
            return fault(format!("access through the non-pointer word {pointer:#x}"));
        }
        let id = (pointer >> 32) as usize - 1;
        let offset = (pointer & 0xffff_ffff) as usize;
        let Some(allocation) = self.allocations.get(id) else {
            return fault(format!("access through a wild pointer {pointer:#x}"));
        };
        if !allocation.live {
            return fault(format!("access to freed allocation {id}"));
        }
        if offset + bytes > allocation.bytes.len() {
            return fault(format!(
                "access to bytes {offset}..{} of a {}-byte allocation",
                offset + bytes,
                allocation.bytes.len()
            ));
        }
        Ok((id, offset))
    }
    /// A runtime buffer of `bytes` bytes (`kush_buffer_alloc`): its
    /// allocation has the size the runtime's pool gives it, which growth
    /// may use without moving.
    fn allocate_buffer(&mut self, bytes: usize) -> i64 {
        self.allocate(physical(bytes), true)
    }
    /// `kush_buffer_grow`: the buffer at `pointer` with room for `bytes`
    /// bytes, in place when its allocation has it, else moved to a new one.
    /// `exact` sizes a new allocation as asked (fallible growth). Neither
    /// counts as an allocation or a free.
    fn grow(&mut self, pointer: i64, bytes: usize, exact: bool) -> Run<i64> {
        let (id, offset) = self.locate(pointer, 0)?;
        if offset != 0 {
            return fault(format!("growth of an interior pointer {pointer:#x}"));
        }
        let old = std::mem::take(&mut self.allocations[id].bytes);
        if bytes <= old.len() {
            self.allocations[id].bytes = old;
            return Ok(pointer);
        }
        let mut new = vec![0; if exact { bytes } else { physical(bytes) }];
        new[..old.len()].copy_from_slice(&old);
        self.allocations[id].live = false;
        self.allocations.push(Allocation {
            bytes: new,
            live: true,
            heap: true,
        });
        Ok((self.allocations.len() as i64) << 32)
    }
    fn load_bytes(&self, pointer: i64, count: usize) -> Run<Vec<u8>> {
        let (id, offset) = self.locate(pointer, count)?;
        Ok(self.allocations[id].bytes[offset..offset + count].to_vec())
    }
    fn store_bytes(&mut self, pointer: i64, bytes: &[u8]) -> Run<()> {
        let (id, offset) = self.locate(pointer, bytes.len())?;
        self.allocations[id].bytes[offset..offset + bytes.len()].copy_from_slice(bytes);
        Ok(())
    }
    fn free(&mut self, pointer: i64) -> Run<()> {
        let (id, offset) = self.locate(pointer, 0)?;
        if offset != 0 {
            return fault(format!("free of an interior pointer {pointer:#x}"));
        }
        let allocation = &mut self.allocations[id];
        allocation.live = false;
        allocation.bytes = Vec::new();
        if allocation.heap {
            self.live_heap -= 1;
            self.stats.deallocations += 1;
        }
        Ok(())
    }
    fn load(&self, pointer: i64, words: usize) -> Run<Words> {
        let (id, offset) = self.locate(pointer, words * 8)?;
        let bytes = &self.allocations[id].bytes[offset..offset + words * 8];
        Ok(bytes
            .as_chunks::<8>()
            .0
            .iter()
            .map(|word| i64::from_le_bytes(*word))
            .collect())
    }
    fn store(&mut self, pointer: i64, words: &[i64]) -> Run<()> {
        let (id, offset) = self.locate(pointer, words.len() * 8)?;
        let bytes = &mut self.allocations[id].bytes[offset..offset + words.len() * 8];
        for (chunk, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(words) {
            chunk.copy_from_slice(&word.to_le_bytes());
        }
        Ok(())
    }
}

/// Where a call's result goes in the caller.
struct Return {
    destination: LocalId,
    next: BlockId,
    unwind: Option<BlockId>,
}

struct Frame {
    body: Rc<Body>,
    block: BlockId,
    statement: usize,
    /// The words of each local without an address.
    locals: Vec<Words>,
    /// The stack allocation of each local whose address the body takes, or
    /// for a capture by reference, the caller's slot it goes through.
    homes: Vec<Option<i64>>,
    /// Which homes belong to this frame (the rest are borrowed).
    owned: Vec<bool>,
    /// Stack storage the frame made for values without an address (an
    /// array value a view looks at).
    temporaries: Vec<i64>,
    /// `None` for the entry function and a nested call.
    caller: Option<Return>,
}

struct Machine<'p, 'o> {
    program: &'p Executable,
    bodies: Vec<Option<Rc<Body>>>,
    memory: Memory,
    input: &'o mut dyn Read,
    output: &'o mut dyn Write,
    /// In check mode, the tree's host calls to replay: their effects
    /// (files, processes, clocks) happened once, on the tree.
    hosts: Option<std::collections::VecDeque<HostRecord>>,
    stack: Vec<Frame>,
    /// The panic a cleanup block runs for.
    unwinding: Option<Diagnostic>,
    fuel: usize,
    /// The capture types of each closure environment's drop glue, by the
    /// index its environment's first word names (`DROP | index`).
    closure_types: Vec<Vec<Type>>,
}

/// Run the program's entry function on the machine. Returns its result word
/// (zero for `Unit`) and the allocation stats a native build reports.
pub fn evaluate(program: &Executable, output: &mut dyn Write) -> Run<(i64, MemoryStats)> {
    evaluate_with_input(program, &mut std::io::empty(), output)
}

/// [`evaluate`] with standard input read from `input`.
pub fn evaluate_with_input(
    program: &Executable,
    input: &mut dyn Read,
    output: &mut dyn Write,
) -> Run<(i64, MemoryStats)> {
    run_program(program, input, output, None)
}

fn run_program(
    program: &Executable,
    input: &mut dyn Read,
    output: &mut dyn Write,
    hosts: Option<std::collections::VecDeque<HostRecord>>,
) -> Run<(i64, MemoryStats)> {
    let entry = program.entry().map_err(Stop::Panic)?;
    // The task runtime runs `main` as a task, whose allocations the stats
    // count (FND-EVAL-EFFECTS).
    if program.uses_tasks {
        return unsupported("the task runtime");
    }
    let mut machine = Machine {
        program,
        bodies: vec![None; program.functions.len()],
        memory: Memory::default(),
        input,
        hosts,
        output,
        stack: Vec::new(),
        unwinding: None,
        fuel: program.eval_fuel,
        closure_types: Vec::new(),
    };
    machine.memory.stats.fusions = program.fusions;
    machine.enter(entry, Vec::new(), None, None)?;
    let result = machine.run()?.first().copied().unwrap_or(0);
    if machine.memory.live_heap != 0 {
        return Err(Stop::Panic(Diagnostic::new(
            Span::default(),
            "internal ownership error: live owning allocations after normal program exit",
        )));
    }
    Ok((result, machine.memory.stats))
}

/// The outcome of one read or write: what it moved, or its error.
pub(crate) type IoOutcome<T> = std::result::Result<T, (std::io::ErrorKind, Option<i32>)>;

fn io_error((kind, code): (std::io::ErrorKind, Option<i32>)) -> std::io::Error {
    match code {
        Some(code) => std::io::Error::from_raw_os_error(code),
        None => kind.into(),
    }
}

/// What the tree evaluator's reads and writes did, call by call, for the
/// machine to replay.
#[derive(Default)]
pub(crate) struct Transcript {
    /// Each read's bytes or error.
    pub(crate) reads: Vec<IoOutcome<Vec<u8>>>,
    /// Each write's accepted count or error.
    pub(crate) writes: Vec<IoOutcome<usize>>,
    /// The bytes the writer accepted.
    pub(crate) written: Vec<u8>,
    /// Each host call's outcome.
    pub(crate) hosts: Vec<HostRecord>,
}

/// What one host call did on the tree evaluator: its result (`value` is
/// the error code, or a scalar payload), and for each argument that is a
/// byte buffer, its contents after the call (`None` when the call consumed
/// it, or for an argument that is not a buffer).
#[derive(Debug)]
pub(crate) struct HostRecord {
    pub(crate) ok: bool,
    pub(crate) value: i64,
    pub(crate) buffers: Vec<Option<Vec<u8>>>,
}

/// The tree's reads, call by call.
struct Replay(std::collections::VecDeque<IoOutcome<Vec<u8>>>);

impl Read for Replay {
    fn read(&mut self, buffer: &mut [u8]) -> std::io::Result<usize> {
        match self.0.pop_front() {
            None => Ok(0),
            Some(Err(error)) => Err(io_error(error)),
            Some(Ok(mut chunk)) => {
                let count = chunk.len().min(buffer.len());
                buffer[..count].copy_from_slice(&chunk[..count]);
                if count < chunk.len() {
                    chunk.drain(..count);
                    self.0.push_front(Ok(chunk));
                }
                Ok(count)
            }
        }
    }
}

/// A writer that accepts what the tree's writer accepted, call by call, and
/// keeps the accepted bytes. Past the tree's writes it accepts everything.
struct Echo {
    writes: std::collections::VecDeque<IoOutcome<usize>>,
    written: Vec<u8>,
}

impl Write for Echo {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        let accepted = match self.writes.pop_front() {
            None => bytes.len(),
            Some(Err(error)) => return Err(io_error(error)),
            Some(Ok(count)) => count.min(bytes.len()),
        };
        self.written.extend_from_slice(&bytes[..accepted]);
        Ok(accepted)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// `KUSH_MACHINE_CHECK`: run the machine on a program the tree evaluator ran
/// (`tree` is its outcome, `transcript` what its reads and writes did). A
/// difference is an error; a construct the machine does not cover is
/// appended, with the program's entry function, to the file
/// `KUSH_MACHINE_REPORT` names.
pub(crate) fn check(
    program: &Executable,
    transcript: Transcript,
    tree: &std::result::Result<(i64, MemoryStats), Diagnostic>,
) -> std::result::Result<(), Diagnostic> {
    let disagree = |what: String| {
        Err(Diagnostic::new(
            Span::default(),
            format!("the MIR machine disagrees with the tree evaluator: {what}"),
        ))
    };
    // Budgets count different steps; a fuel-limited run is not compared.
    if tree
        .as_ref()
        .is_err_and(|error| error.message.contains("budget exhausted"))
    {
        return Ok(());
    }
    let mut input = Replay(transcript.reads.into());
    let mut echo = Echo {
        writes: transcript.writes.into(),
        written: Vec::new(),
    };
    let tree_output = &transcript.written;
    let result = run_program(
        program,
        &mut input,
        &mut echo,
        Some(transcript.hosts.into()),
    );
    let output = echo.written;
    let machine = match result {
        Err(Stop::Unsupported(reason)) => {
            report(program, &reason);
            return Ok(());
        }
        Err(Stop::Panic(diagnostic)) if diagnostic.message.contains("budget exhausted") => {
            report(program, "the machine's computation budget");
            return Ok(());
        }
        Err(Stop::Fault(fault)) => return disagree(format!("the machine faulted: {fault}")),
        Err(Stop::Panic(diagnostic)) => Err(diagnostic),
        Ok(done) => Ok(done),
    };
    if output != *tree_output {
        return disagree(format!(
            "it printed {:?} where the tree printed {:?}",
            String::from_utf8_lossy(&output),
            String::from_utf8_lossy(tree_output)
        ));
    }
    match (tree, machine) {
        (Ok((tree_result, tree_stats)), Ok((result, stats))) => {
            if result != *tree_result {
                return disagree(format!("result {result} against {tree_result}"));
            }
            if stats.report() != tree_stats.report() {
                return disagree(format!(
                    "{} against {}",
                    stats.report(),
                    tree_stats.report()
                ));
            }
        }
        (Err(tree_error), Err(error)) if error.message == tree_error.message => {}
        (tree, machine) => return disagree(format!("{machine:?} against {tree:?}")),
    }
    Ok(())
}

fn report(program: &Executable, reason: &str) {
    let Some(path) = std::env::var_os("KUSH_MACHINE_REPORT") else {
        return;
    };
    let entry = program
        .entry()
        .ok()
        .map(|entry| program.functions[entry].name.clone())
        .unwrap_or_default();
    let line = format!("{entry}\t{reason}\n");
    let _ = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .and_then(|mut file| file.write_all(line.as_bytes()));
}

impl Machine<'_, '_> {
    fn body(&mut self, function: usize) -> Run<Rc<Body>> {
        if let Some(body) = &self.bodies[function] {
            return Ok(body.clone());
        }
        let body = Rc::new(build(self.program, function).map_err(|reason| {
            Stop::Unsupported(format!(
                "fn {}: {reason}",
                self.program.functions[function].name
            ))
        })?);
        self.bodies[function] = Some(body.clone());
        Ok(body)
    }
    fn width(&self, ty: Type) -> usize {
        self.program.width(ty)
    }

    /// Push a frame for `function` with its parameters' words.
    /// Push a frame for `function` with its parameters' words, and for a
    /// closure, its environment (native's function prologue).
    fn enter(
        &mut self,
        function: usize,
        args: Vec<Words>,
        caller: Option<Return>,
        environment: Option<i64>,
    ) -> Run<()> {
        let body = self.body(function)?;
        let program = self.program;
        let checked = &program.functions[function];
        let mut locals = body
            .locals
            .iter()
            .map(|local| vec![0; self.width(local.ty)])
            .collect::<Vec<_>>();
        let slot = |position: usize| {
            checked
                .parameter_slots
                .as_ref()
                .map_or(position, |slots| slots[position])
        };
        let mut homes = vec![None; body.locals.len()];
        let mut owned = vec![false; body.locals.len()];
        // A closure's captures come first: values from its environment, or
        // for a capture by reference, the caller's slot to go through.
        let captures = checked.closure.unwrap_or(0);
        let environment = environment.unwrap_or(0);
        if captures != 0 {
            let mut offset = 8;
            for position in 0..captures {
                let slot = slot(position);
                if checked.capture_refs.get(position).copied().unwrap_or(false) {
                    homes[slot] = Some(self.memory.load(environment + offset, 1)?[0]);
                    offset += 8;
                    continue;
                }
                let width = locals[slot].len();
                locals[slot] = self.memory.load(environment + offset, width)?;
                offset += (width * 8) as i64;
            }
            // A `once` environment is consumed by its call.
            if !checked.shared_environment {
                self.memory.free(environment)?;
            }
        }
        for (index, words) in args.into_iter().enumerate() {
            let slot = slot(captures + index);
            let width = locals[slot].len();
            locals[slot] = fit(words, width);
        }
        for local in loops::address_taken(&body) {
            if homes[local].is_some() {
                continue;
            }
            let home = self.memory.allocate(locals[local].len() * 8, false);
            self.memory.store(home, &locals[local])?;
            homes[local] = Some(home);
            owned[local] = true;
        }
        self.stack.push(Frame {
            body,
            block: 0,
            statement: 0,
            locals,
            homes,
            owned,
            temporaries: Vec::new(),
            caller,
        });
        Ok(())
    }

    /// Pop the top frame, releasing its locals' homes.
    fn leave(&mut self) -> Run<Frame> {
        let frame = self.stack.pop().expect("a frame to leave");
        for (home, owned) in frame.homes.iter().zip(&frame.owned) {
            if let (Some(home), true) = (home, owned) {
                self.memory.free(*home)?;
            }
        }
        for temporary in &frame.temporaries {
            self.memory.free(*temporary)?;
        }
        Ok(frame)
    }

    /// Run until a frame without a caller returns: the entry function, or
    /// a nested call. Returns its result's words.
    fn run(&mut self) -> Run<Words> {
        loop {
            if self.fuel == 0 {
                return Err(Stop::Panic(Diagnostic::new(
                    Span::default(),
                    "reference evaluator computation budget exhausted",
                )));
            }
            self.fuel -= 1;
            match self.step() {
                Ok(Some(result)) => return Ok(result),
                Ok(None) => {}
                Err(Raise::Panic(diagnostic, target)) => self.raise(diagnostic, target)?,
                Err(Raise::Stop(stop)) => return Err(stop),
            }
        }
    }

    /// Continue unwinding from the top frame at `target`, or out of it.
    fn raise(&mut self, diagnostic: Diagnostic, mut target: Option<BlockId>) -> Run<()> {
        loop {
            if let Some(block) = target {
                let frame = self.stack.last_mut().expect("a frame");
                frame.block = block;
                frame.statement = 0;
                self.unwinding = Some(diagnostic);
                return Ok(());
            }
            let frame = self.leave()?;
            match frame.caller {
                Some(caller) => target = caller.unwind,
                None => return Err(Stop::Panic(diagnostic)),
            }
        }
    }

    /// Call `function` from inside a statement (a `Vec.map` callback) and
    /// run it to its result. A panic leaves it as a [`Stop::Panic`].
    fn call_nested(&mut self, function: usize, args: Vec<Words>) -> Run<Words> {
        self.enter(function, args, None, None)?;
        self.run()
    }

    /// Run one statement or terminator. `Some` is the result of a frame
    /// without a caller.
    fn step(&mut self) -> std::result::Result<Option<Words>, Raise> {
        let frame = self.stack.last().expect("a frame");
        let body = frame.body.clone();
        let block = &body.blocks[frame.block];
        if let Some(statement) = block.statements.get(frame.statement) {
            let StatementKind::Assign(place, rvalue) = &statement.kind;
            let ty = body.place_ty(*place);
            let words = self
                .rvalue(&body, rvalue, ty, statement.span)
                .map_err(|stop| Raise::at(stop, block.unwind))?;
            self.store(*place, &words).map_err(Raise::Stop)?;
            self.stack.last_mut().expect("a frame").statement += 1;
            return Ok(None);
        }
        let span = block.terminator.span;
        match &block.terminator.kind {
            TerminatorKind::Goto(target) => self.jump(*target),
            TerminatorKind::Switch {
                value,
                targets,
                otherwise,
            } => {
                let word = self.operand(*value).map_err(Raise::Stop)?[0];
                let target = targets
                    .iter()
                    .find(|(case, _)| *case == word)
                    .map_or(*otherwise, |(_, target)| *target);
                self.jump(target);
            }
            TerminatorKind::Call {
                callee,
                args,
                destination,
                next,
                unwind,
            } => {
                let values = args
                    .iter()
                    .map(|arg| self.operand(*arg))
                    .collect::<Run<Vec<_>>>()
                    .map_err(Raise::Stop)?;
                match callee {
                    Callee::Function(index) => {
                        let caller = Return {
                            destination: *destination,
                            next: *next,
                            unwind: *unwind,
                        };
                        self.enter(*index, values, Some(caller), None)
                            .map_err(Raise::Stop)?;
                    }
                    Callee::PrintInt(kind) => {
                        writeln!(self.output, "{}", kind.decode(values[0][0])).map_err(|e| {
                            Raise::Stop(Stop::Panic(Diagnostic::new(
                                span,
                                format!("output failed: {e}"),
                            )))
                        })?;
                        self.finish_call(*destination, vec![0], *next)
                            .map_err(Raise::Stop)?;
                    }
                    Callee::Builtin { index, .. }
                        if matches!(
                            body.builtins.0[*index],
                            crate::executable::Target::DynCall { .. }
                                | crate::executable::Target::UnionBorrowCall { .. }
                        ) =>
                    {
                        let caller = Return {
                            destination: *destination,
                            next: *next,
                            unwind: *unwind,
                        };
                        match body.builtins.0[*index] {
                            crate::executable::Target::DynCall { spec, .. } => {
                                self.dyn_call(spec, values, caller)
                            }
                            crate::executable::Target::UnionBorrowCall { spec, .. } => {
                                self.union_call(spec, values, caller)
                            }
                            _ => unreachable!("matched above"),
                        }
                        .map_err(Raise::Stop)?;
                    }
                    Callee::Builtin { index, .. } => {
                        let target = body.builtins.0[*index];
                        let ty = body.locals[*destination].ty;
                        let types = args
                            .iter()
                            .map(|arg| body.operand_ty(*arg))
                            .collect::<Vec<_>>();
                        let words = self
                            .builtin(&target, &values.concat(), &types, ty, span)
                            .map_err(|stop| Raise::at(stop, *unwind))?;
                        self.finish_call(*destination, words, *next)
                            .map_err(Raise::Stop)?;
                    }
                    Callee::Indirect(callable) => {
                        // A `fn` value is its code word; a `once` or `multi`
                        // value adds its environment.
                        let words = self.operand(*callable).map_err(Raise::Stop)?;
                        let environment = match body.operand_ty(*callable) {
                            Type::Fn(_) => None,
                            Type::Multi(_) if words[1] != 0 => {
                                return Err(Raise::Stop(Stop::Unsupported(
                                    "a call through a capturing multi fn".into(),
                                )));
                            }
                            _ => Some(words[1]),
                        };
                        let function = code_function(words[0]).map_err(Raise::Stop)?;
                        let caller = Return {
                            destination: *destination,
                            next: *next,
                            unwind: *unwind,
                        };
                        self.enter(function, values, Some(caller), environment)
                            .map_err(Raise::Stop)?;
                    }
                }
            }
            TerminatorKind::Return(value) => {
                let words = self.operand(*value).map_err(Raise::Stop)?;
                let frame = self.leave().map_err(Raise::Stop)?;
                match frame.caller {
                    Some(caller) => {
                        self.finish_call(caller.destination, words, caller.next)
                            .map_err(Raise::Stop)?;
                    }
                    None => return Ok(Some(words)),
                }
            }
            TerminatorKind::Panic { unwind } => {
                // The tree evaluator reports `panic()` as it reports a failed
                // check.
                let diagnostic = Diagnostic::new(span, "panic: checked arithmetic failed");
                return Err(Raise::Panic(diagnostic, *unwind));
            }
            TerminatorKind::Drop {
                place,
                next,
                unwind,
            } => {
                let ty = body.place_ty(*place);
                let words = self.read(*place).map_err(Raise::Stop)?;
                self.drop_value(ty, &words)
                    .map_err(|stop| Raise::at(stop, *unwind))?;
                self.jump(*next);
            }
            TerminatorKind::Resume => {
                let diagnostic = self
                    .unwinding
                    .take()
                    .ok_or_else(|| Raise::Stop(Stop::Fault("resume without a panic".into())))?;
                let frame = self.leave().map_err(Raise::Stop)?;
                match frame.caller {
                    Some(caller) => return Err(Raise::Panic(diagnostic, caller.unwind)),
                    None => return Err(Raise::Stop(Stop::Panic(diagnostic))),
                }
            }
            TerminatorKind::Abort => {
                return Err(Raise::Stop(Stop::Unsupported("an abort".into())));
            }
            TerminatorKind::Unreachable => {
                return Err(Raise::Stop(Stop::Fault(
                    "reached an unreachable block".into(),
                )));
            }
        }
        Ok(None)
    }

    /// A builtin call on its arguments' words (native's `call_target`).
    fn builtin(
        &mut self,
        target: &crate::executable::Target,
        values: &[i64],
        types: &[Type],
        ty: Type,
        span: Span,
    ) -> Run<Words> {
        use crate::executable::Target;
        match *target {
            Target::Host(op, shape) => {
                self.host_replay(&format!("Host({op:?})"), shape, values, types, ty)
            }
            Target::Foreign(index) => self.foreign_call(index, values, types, ty, span),
            Target::Bytes(op) => self.bytes_call(op, values, span),
            Target::String(op) => self.string_call(op, values, ty, span),
            Target::Str(op) => self.str_call(op, values, ty, span),
            Target::Vec(op, element) => self.vec_call(op, element, values, ty, span),
            Target::Slice(op, element) => self.slice_call(op, element, values, span),
            Target::DynArray(op, element) => self.dyn_array_call(op, element, values, span),
            Target::Io(op, shape) => self.io_call(op, shape, values, ty),
            Target::AllocVec(op, element) => self.alloc_vec_call(op, element, values, ty, span),
            Target::Print | Target::PrintFloat(_) => {
                let text = match *target {
                    Target::PrintFloat(kind) => crate::float::format(kind, values[0]),
                    _ => values[0].to_string(),
                };
                writeln!(self.output, "{text}").map_err(|e| {
                    Stop::Panic(Diagnostic::new(span, format!("output failed: {e}")))
                })?;
                Ok(vec![0])
            }
            Target::Int(op, source, target) => {
                use crate::int::IntOp;
                let (present, word) = crate::int::builtin(op, source, target, values);
                Ok(match op {
                    IntOp::TryConvert { some_tag, none_tag }
                    | IntOp::Checked(_, some_tag, none_tag)
                    | IntOp::CharFromCode { some_tag, none_tag } => {
                        self.optional(ty, present.then_some(word), some_tag, none_tag)
                    }
                    _ => vec![word],
                })
            }
            Target::Float(op) => {
                use crate::float::FloatOp;
                let (present, word) = crate::float::builtin(op, values);
                Ok(match op {
                    FloatOp::TryFromInt {
                        some_tag, none_tag, ..
                    }
                    | FloatOp::TryToF32 {
                        some_tag, none_tag, ..
                    }
                    | FloatOp::TryToInt {
                        some_tag, none_tag, ..
                    } => self.optional(ty, present.then_some(word), some_tag, none_tag),
                    _ => vec![word],
                })
            }
            _ => unsupported(format!("the builtin {}", target_name(target))),
        }
    }

    /// A host call (filesystem, environment, clock, process, network) as the
    /// tree ran it in check mode: the recorded result, the recorded contents
    /// of its buffer arguments, and a free of each owned buffer it consumed.
    /// Outside check mode the machine does not run host calls yet.
    fn host_replay(
        &mut self,
        what: &str,
        shape: crate::runtime_types::ResultShape,
        values: &[i64],
        types: &[Type],
        ty: Type,
    ) -> Run<Words> {
        let Some(record) = self.hosts.as_mut().and_then(|hosts| hosts.pop_front()) else {
            return unsupported(format!("the builtin {what} outside check mode"));
        };
        let mut owned = 0;
        for (index, arg_ty) in types.iter().enumerate() {
            let buffer = |ty: Type| matches!(ty, Type::Bytes | Type::String);
            let (handle, is_owned) = match arg_ty.full() {
                ty if buffer(ty) => (values[index], true),
                Type::Ref(pointee) | Type::RefMut(pointee)
                    if buffer(self.program.pointees[pointee].full()) =>
                {
                    (self.memory.load(values[index], 1)?[0], false)
                }
                _ => continue,
            };
            match record.buffers.get(index).cloned().flatten() {
                Some(data) => {
                    let (_, capacity) = self.header(handle)?;
                    if data.len() as i64 > capacity {
                        return fault("a host call's buffer outgrew its capacity");
                    }
                    self.memory.store_bytes(handle + 16, &data)?;
                    self.memory.store(handle, &[data.len() as i64])?;
                    if is_owned {
                        owned = handle;
                    }
                }
                None if is_owned => self.memory.free(handle)?,
                None => {}
            }
        }
        // An ok payload is the owned buffer the call filled, or the recorded
        // scalar (zero for `Unit`).
        let words = if record.ok {
            let payload = if owned != 0 { owned } else { record.value };
            vec![shape.ok_tag as i64, payload]
        } else {
            vec![shape.err_tag as i64, record.value]
        };
        Ok(fit(words, self.width(ty)))
    }

    /// A foreign call: the `std.sys` shims as the tree runs them (replayed,
    /// except reads and writes of the standard streams, which go through
    /// the machine's own input and output). Any other foreign function
    /// stops the run, as on the tree.
    fn foreign_call(
        &mut self,
        index: usize,
        values: &[i64],
        types: &[Type],
        ty: Type,
        span: Span,
    ) -> Run<Words> {
        let program = self.program;
        let Some(function) = program.foreign_functions[index].as_ref() else {
            return fault("a call of an unchecked foreign function");
        };
        let symbol = function.symbol.as_str();
        let Some(shape) = function
            .fallible
            .filter(|_| symbol.starts_with("kush_sys_"))
        else {
            return panic_at(
                span,
                &format!(
                    "foreign C function '{symbol}' can only be executed by the native backend (kush build/run); the bounded reference interpreter rejects host FFI instead of guessing its behavior"
                ),
            );
        };
        let stream = matches!(
            symbol,
            "kush_sys_read" | "kush_sys_probe" | "kush_sys_write"
        ) && (0..=2).contains(&values[0]);
        if !stream {
            return self.host_replay(&format!("Foreign({symbol})"), shape, values, types, ty);
        }
        // The tree recorded this call too; the machine makes it itself.
        if let Some(hosts) = self.hosts.as_mut() {
            hosts.pop_front();
        }
        let fd = values[0];
        let positioned = symbol != "kush_sys_probe" && values[3] >= 0;
        let readable = fd == 0 && symbol != "kush_sys_write";
        let writable = fd == 1 && symbol == "kush_sys_write";
        let code = |result: std::io::Result<usize>| match result {
            Ok(count) => (0, count as i64),
            Err(error) => (
                error
                    .raw_os_error()
                    .filter(|code| *code > 0)
                    .map_or(5, i64::from),
                0,
            ),
        };
        let (status, value) = match symbol {
            "kush_sys_read" => {
                let (handle, length) = (values[1], values[2]);
                let (start, capacity) = self.header(handle)?;
                let status = if !readable {
                    9
                } else if positioned {
                    29
                } else if length < 0 {
                    22
                } else if length > capacity - start {
                    27
                } else {
                    let mut data = vec![0; length as usize];
                    let (status, received) = loop {
                        match self.input.read(&mut data) {
                            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                            result => break code(result),
                        }
                    };
                    self.memory
                        .store_bytes(handle + 16 + start, &data[..received as usize])?;
                    self.memory.store(handle, &[start + received])?;
                    status
                };
                if status != 0 {
                    self.memory.free(handle)?;
                }
                (status, handle)
            }
            "kush_sys_probe" if !readable => (9, 0),
            "kush_sys_probe" => loop {
                let mut probe = [0u8; 1];
                match self.input.read(&mut probe) {
                    Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                    result => break code(result),
                }
            },
            _ => {
                let handle = self.memory.load(values[1], 1)?[0];
                let data = self
                    .memory
                    .load_bytes(handle + 16, self.header(handle)?.0 as usize)?;
                let start = values[2];
                if !writable {
                    (9, 0)
                } else if positioned {
                    (29, 0)
                } else if start < 0 || start as usize > data.len() {
                    (22, 0)
                } else {
                    code(self.output.write(&data[start as usize..]))
                }
            }
        };
        let words = if status == 0 {
            vec![shape.ok_tag as i64, value]
        } else {
            vec![shape.err_tag as i64, status]
        };
        Ok(fit(words, self.width(ty)))
    }

    fn jump(&mut self, target: BlockId) {
        let frame = self.stack.last_mut().expect("a frame");
        frame.block = target;
        frame.statement = 0;
    }

    /// The callee returned `words` into `destination` of the top frame.
    fn finish_call(&mut self, destination: LocalId, words: Words, next: BlockId) -> Run<()> {
        self.store(Place::local(destination), &words)?;
        self.jump(next);
        Ok(())
    }

    // ---- places ----------------------------------------------------------

    /// The words of a local of the top frame.
    fn local(&self, local: LocalId) -> Run<Words> {
        let frame = self.stack.last().expect("a frame");
        match frame.homes[local] {
            Some(home) => self.memory.load(home, frame.locals[local].len()),
            None => Ok(frame.locals[local].clone()),
        }
    }
    fn read(&self, place: Place) -> Run<Words> {
        let frame = self.stack.last().expect("a frame");
        let ty = frame.body.place_ty(place);
        let width = self.width(ty);
        let offset = place.field.map_or(0, |field| field.offset);
        if place.deref {
            let pointer = self.local(place.local)?[0];
            return self.memory.load(pointer + (offset * 8) as i64, width);
        }
        let words = self.local(place.local)?;
        if place.field.is_none() || (offset == 0 && width == words.len()) {
            return Ok(words);
        }
        words
            .get(offset..offset + width)
            .map(<[i64]>::to_vec)
            .ok_or_else(|| Stop::Fault(format!("field {offset}+{width} of _{}", place.local)))
    }
    fn store(&mut self, place: Place, words: &[i64]) -> Run<()> {
        let frame = self.stack.last().expect("a frame");
        let ty = frame.body.place_ty(place);
        let width = self.width(ty);
        let words = fit(words.to_vec(), width);
        let offset = place.field.map_or(0, |field| field.offset);
        if place.deref {
            let pointer = self.local(place.local)?[0];
            return self.memory.store(pointer + (offset * 8) as i64, &words);
        }
        let mut current = self.local(place.local)?;
        if place.field.is_none() || (offset == 0 && width == current.len()) {
            current = fit(words, current.len());
        } else {
            let Some(target) = current.get_mut(offset..offset + width) else {
                return fault(format!("field {offset}+{width} of _{}", place.local));
            };
            target.copy_from_slice(&words);
        }
        let frame = self.stack.last_mut().expect("a frame");
        match frame.homes[place.local] {
            Some(home) => self.memory.store(home, &current),
            None => {
                frame.locals[place.local] = current;
                Ok(())
            }
        }
    }
    /// The address of a place: its local's home, or the pointer it goes
    /// through, plus its field's offset.
    fn address(&self, place: Place) -> Run<i64> {
        let offset = (place.field.map_or(0, |field| field.offset) * 8) as i64;
        if place.deref {
            return Ok(self.local(place.local)?[0] + offset);
        }
        let frame = self.stack.last().expect("a frame");
        match frame.homes[place.local] {
            Some(home) => Ok(home + offset),
            None => fault(format!(
                "the address of _{}, which has no home",
                place.local
            )),
        }
    }
    fn operand(&self, operand: Operand) -> Run<Words> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.read(place),
            Operand::Constant(value, ty) => Ok(fit(vec![value], self.width(ty).max(1))),
        }
    }
    fn scalar(&self, operand: Operand) -> Run<i64> {
        Ok(self.operand(operand)?.first().copied().unwrap_or(0))
    }

    // ---- values ----------------------------------------------------------

    fn rvalue(&mut self, body: &Body, rvalue: &Rvalue, ty: Type, span: Span) -> Run<Words> {
        let panic = || Stop::Panic(Diagnostic::new(span, "panic: checked arithmetic failed"));
        Ok(match rvalue {
            Rvalue::Use(operand) => self.operand(*operand)?,
            Rvalue::Unary(op, operand) => {
                let operand_ty = body.operand_ty(*operand);
                let n = self.scalar(*operand)?;
                vec![match (op, operand_ty.float_kind(), operand_ty.int_kind()) {
                    (UnOp::Neg, Some(kind), _) => crate::float::negate(kind, n),
                    (UnOp::Neg, None, Some(kind)) => {
                        kind.encode(-kind.decode(n)).ok_or_else(panic)?
                    }
                    (UnOp::Neg, None, None) => n.checked_neg().ok_or_else(panic)?,
                    (UnOp::Not, _, Some(kind)) => crate::int::not(kind, n),
                    (UnOp::Not, _, None) => i64::from(n == 0),
                }]
            }
            Rvalue::Binary(op, left, right) => {
                let left_ty = body.operand_ty(*left);
                let right_ty = body.operand_ty(*right);
                let (a, b) = (self.scalar(*left)?, self.scalar(*right)?);
                let kind = op.kind();
                let comparison = matches!(
                    op,
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
                );
                vec![if let Some(float) = left_ty.float_kind() {
                    if comparison {
                        i64::from(crate::float::compare(float, &kind, a, b))
                    } else {
                        crate::float::binary(float, &kind, a, b)
                    }
                } else if let Some(int) = left_ty.int_kind() {
                    if comparison {
                        i64::from(crate::int::compare(int, &kind, a, b))
                    } else {
                        let shift = right_ty.int_kind().map_or(0, |k| k.decode(b));
                        crate::int::binary(int, &kind, a, b, shift).ok_or_else(panic)?
                    }
                } else {
                    match op {
                        BinOp::Add => a.checked_add(b).ok_or_else(panic)?,
                        BinOp::Sub => a.checked_sub(b).ok_or_else(panic)?,
                        BinOp::Mul => a.checked_mul(b).ok_or_else(panic)?,
                        BinOp::Div => a.checked_div(b).ok_or_else(panic)?,
                        BinOp::Rem => a.checked_rem(b).ok_or_else(panic)?,
                        BinOp::BitAnd => a & b,
                        BinOp::BitOr => a | b,
                        BinOp::BitXor => a ^ b,
                        BinOp::Lt => i64::from(a < b),
                        BinOp::Le => i64::from(a <= b),
                        BinOp::Gt => i64::from(a > b),
                        BinOp::Ge => i64::from(a >= b),
                        BinOp::Eq => i64::from(a == b),
                        BinOp::Ne => i64::from(a != b),
                        BinOp::Shl | BinOp::Shr => {
                            return unsupported("a shift of a non-integer");
                        }
                    }
                }]
            }
            Rvalue::Int(op, source, target, operands) => {
                let words = operands
                    .iter()
                    .map(|operand| self.scalar(*operand))
                    .collect::<Run<Vec<_>>>()?;
                vec![crate::int::builtin(*op, *source, *target, &words).1]
            }
            Rvalue::Aggregate(aggregate, tag, operands) => {
                let mut payload = Vec::new();
                for operand in operands {
                    payload.extend(self.operand(*operand)?);
                }
                self.encode_variant(*aggregate, *tag, payload)
            }
            Rvalue::BoxNew(operand) => {
                let words = self.operand(*operand)?;
                let pointer = self.memory.allocate(words.len().max(1) * 8, true);
                self.memory.store(pointer, &words)?;
                vec![pointer]
            }
            Rvalue::BoxTake(operand) => {
                let pointer = self.scalar(*operand)?;
                let words = self.memory.load(pointer, self.width(ty))?;
                self.memory.free(pointer)?;
                words
            }
            Rvalue::Ref(place) => vec![self.address(*place)?],
            Rvalue::FnValue { function, captures } => {
                self.fn_value(body, *function, captures, ty)?
            }
            Rvalue::Coerce(operand, index) => {
                let values = self.operand(*operand)?;
                let (to, coercion) = body.coercions.0[*index].clone();
                self.coerce(&values, to, &coercion)?
            }
            Rvalue::StructEq(left, right, negated) => {
                let ty = body.operand_ty(*left);
                let (left, right) = (self.operand(*left)?, self.operand(*right)?);
                vec![i64::from(self.struct_eq(ty, &left, &right) != *negated)]
            }
            Rvalue::Bytes(data) => vec![self.bytes_from(data)?],
            Rvalue::Buffer(vector, word) => {
                let handle = self.scalar(*vector)?;
                let offset = match word {
                    BufferWord::Length => 0,
                    BufferWord::Capacity => 8,
                };
                self.memory.load(handle + offset, 1)?
            }
            Rvalue::ByteAt(handle, index) => {
                let address = self.scalar(*handle)? + 16 + self.scalar(*index)?;
                vec![i64::from(self.memory.load_bytes(address, 1)?[0])]
            }
            Rvalue::ElementAddress(base, index) => {
                vec![self.element_address(body, *base, *index, span)?]
            }
            Rvalue::View {
                source,
                start,
                end,
                element,
                check,
                text,
            } => self.view(body, *source, *start, *end, *element, *check, *text, span)?,
            Rvalue::Array(op, operands) => {
                let words = operands
                    .iter()
                    .map(|operand| self.operand(*operand))
                    .collect::<Run<Vec<_>>>()?;
                self.array_op(*op, &words, span)?
            }
            Rvalue::Alloc(op, operands) => self.alloc_op(body, *op, operands, ty, span)?,
            Rvalue::Map(op, operands) => {
                let handle = self.scalar(operands[0])?;
                let callbacks = operands[1..]
                    .iter()
                    .map(|callback| self.scalar(*callback))
                    .collect::<Run<Vec<_>>>()?;
                vec![self.vec_map(op, handle, &callbacks)?]
            }
            other => return unsupported(rvalue_name(other)),
        })
    }

    /// A call on a trait object (native's `dyn_call`): the receiver's member
    /// selects the method. An owned receiver's payload moves out of its
    /// allocation into the call; a borrowed one passes the payload pointer.
    fn dyn_call(&mut self, spec: usize, mut values: Vec<Words>, caller: Return) -> Run<()> {
        let program = self.program;
        let spec = &program.dyn_calls[spec];
        let members = program
            .dyn_members
            .get(spec.object)
            .cloned()
            .unwrap_or_default();
        let owned = spec.mode == crate::executable::ReceiverMode::Owned;
        let (member, pointer) = if owned {
            (values[0][0], values[0][1])
        } else {
            let object = self.memory.load(values[0][0], 2)?;
            (object[0], object[1])
        };
        let Some(entry) = usize::try_from(member)
            .ok()
            .and_then(|index| members.get(index))
        else {
            return fault(format!("a trait object of unregistered member {member}"));
        };
        let function = *entry
            .methods
            .get(&spec.key)
            .expect("a checked member registers every object-safe method");
        values[0] = if owned {
            let payload = self.memory.load(pointer, self.width(entry.member))?;
            self.memory.free(pointer)?;
            payload
        } else {
            vec![pointer]
        };
        self.enter(function, values, Some(caller), None)
    }

    /// A borrowed call on a closed-world union object (native's
    /// `union_borrow_call`): the tag behind the reference selects the
    /// member's method, which gets the payload's address.
    fn union_call(&mut self, spec: usize, mut values: Vec<Words>, caller: Return) -> Run<()> {
        let program = self.program;
        let spec = &program.union_calls[spec];
        let pointer = values[0][0];
        let tag = self.memory.load(pointer, 1)?[0];
        let Some((_, _, function)) = spec
            .members
            .iter()
            .find(|(member_tag, _, _)| *member_tag as i64 == tag)
        else {
            return fault(format!("a union object of unregistered tag {tag}"));
        };
        values[0] = vec![pointer + 8];
        self.enter(*function, values, Some(caller), None)
    }

    /// A function value (native's `mir_fn_value`): its code word, and for a
    /// `once` or `multi` value an environment word, a heap environment
    /// `[drop glue, captures...]` when it captures.
    fn fn_value(
        &mut self,
        body: &Body,
        function: usize,
        captures: &[Capture],
        ty: Type,
    ) -> Run<Words> {
        let code = CODE | function as i64;
        if captures.is_empty() {
            return Ok(match ty {
                Type::Once(_) | Type::Multi(_) => vec![code, 0],
                _ => vec![code],
            });
        }
        if matches!(ty, Type::Multi(_)) {
            return unsupported("a capturing multi fn");
        }
        let types = captures
            .iter()
            .map(|capture| match capture {
                Capture::Value(operand) => body.operand_ty(*operand).full(),
                Capture::Address(local) => body.locals[*local].ty.full(),
            })
            .collect::<Vec<_>>();
        let mut words = Vec::new();
        for capture in captures {
            match capture {
                Capture::Value(operand) => words.extend(self.operand(*operand)?),
                Capture::Address(local) => words.push(self.address(Place::local(*local))?),
            }
        }
        // An address capture is one word whatever the local's type: native
        // sizes the environment by the capture types, so it does too.
        let bytes = 8 + types.iter().map(|ty| self.width(*ty) * 8).sum::<usize>();
        let environment = self.memory.allocate(bytes.max(8 + words.len() * 8), true);
        let drop = self.closure_drop(types);
        self.memory.store(environment, &[drop])?;
        self.memory.store(environment + 8, &words)?;
        Ok(vec![code, environment])
    }

    /// The drop glue word of an environment with these capture types.
    fn closure_drop(&mut self, types: Vec<Type>) -> i64 {
        let index = match self.closure_types.iter().position(|known| *known == types) {
            Some(index) => index,
            None => {
                self.closure_types.push(types);
                self.closure_types.len() - 1
            }
        };
        DROP | index as i64
    }

    /// A representation change (native's `coerce_values` and
    /// `nested_coercion_words`).
    fn coerce(
        &mut self,
        values: &[i64],
        to: Type,
        coercion: &crate::executable::Coercion,
    ) -> Run<Words> {
        use crate::executable::Coercion;
        let width = self.width(to);
        Ok(match coercion {
            Coercion::Inject { tag } => {
                let mut out = vec![*tag as i64];
                out.extend(values.iter().take(width.saturating_sub(1)));
                fit(out, width)
            }
            Coercion::Repack { map } => {
                let Some(target) = usize::try_from(values[0]).ok().and_then(|tag| map.get(tag))
                else {
                    return fault(format!("a union tag {} outside its repack", values[0]));
                };
                let mut out = vec![*target as i64];
                out.extend(values.iter().skip(1).take(width.saturating_sub(1)));
                fit(out, width)
            }
            Coercion::Struct {
                source,
                kept,
                drops,
            } => {
                let target_id = to.layout().expect("a structural target layout");
                let target_fields = self.program.enums[target_id].variants[0].fields.clone();
                let source_id = source.layout().expect("a structural source layout");
                let source_fields = self.program.enums[source_id].variants[0].fields.clone();
                let mut offsets = Vec::with_capacity(source_fields.len());
                let mut offset = self.program.enums[source_id].tag_words();
                for field in &source_fields {
                    offsets.push(offset);
                    offset += self.width(*field);
                }
                let mut out = vec![0];
                for (target, source, nested) in kept {
                    let start = offsets[*source];
                    let field = &values[start..start + self.width(source_fields[*source])];
                    match nested {
                        Some(nested) => {
                            out.extend(self.coerce(field, target_fields[*target], nested)?);
                        }
                        None => out.extend_from_slice(field),
                    }
                }
                for (source, ty) in drops {
                    let start = offsets[*source];
                    let field = values[start..start + self.width(*ty)].to_vec();
                    self.drop_value(*ty, &field)?;
                }
                fit(out, width)
            }
            Coercion::DynBox {
                member,
                member_type,
            } => {
                let payload = &values[..self.width(*member_type).min(values.len())];
                let pointer = self.memory.allocate(payload.len().max(1) * 8, true);
                self.memory.store(pointer, payload)?;
                vec![*member as i64, pointer]
            }
            Coercion::DynUpcast { from, to } => {
                let source = self
                    .program
                    .dyn_members
                    .get(*from)
                    .cloned()
                    .unwrap_or_default();
                let target = self
                    .program
                    .dyn_members
                    .get(*to)
                    .cloned()
                    .unwrap_or_default();
                let mapped = usize::try_from(values[0])
                    .ok()
                    .and_then(|index| source.get(index))
                    .and_then(|entry| {
                        target
                            .iter()
                            .position(|candidate| candidate.member == entry.member)
                    })
                    .unwrap_or(0);
                vec![mapped as i64, values[1]]
            }
            Coercion::Callable {
                function,
                capture,
                target,
            } => {
                let code = CODE | *function as i64;
                if !matches!(target, Type::Once(_)) {
                    return Ok(vec![code]);
                }
                let Some(capture) = capture else {
                    return Ok(vec![code, 0]);
                };
                let width = self.width(*capture);
                let environment = self.memory.allocate(8 + width * 8, true);
                let drop = self.closure_drop(vec![capture.full()]);
                self.memory.store(environment, &[drop])?;
                self.memory
                    .store(environment + 8, &values[..width.min(values.len())])?;
                vec![code, environment]
            }
        })
    }

    /// Native's `struct_eq_words`: field by field, a word per scalar field.
    fn struct_eq(&self, ty: Type, left: &[i64], right: &[i64]) -> bool {
        let Some(layout) = ty.layout() else {
            return left.first() == right.first();
        };
        let definition = &self.program.enums[layout];
        let mut offset = definition.tag_words();
        for field in &definition.variants[0].fields {
            let width = self.width(*field);
            if width > 0 {
                let (a, b) = (
                    &left[offset..offset + width],
                    &right[offset..offset + width],
                );
                let equal = if field.layout().is_some() {
                    self.struct_eq(*field, a, b)
                } else {
                    a[0] == b[0]
                };
                if !equal {
                    return false;
                }
            }
            offset += width;
        }
        true
    }

    /// An enum or record value's words (native's `encode_variant`).
    fn encode_variant(&self, ty: Type, tag: usize, payload: Words) -> Words {
        let layout = ty.layout().expect("an enum constructor's layout");
        let definition = &self.program.enums[layout];
        if let Some(niche) = definition.niche() {
            return match niche.decoder(tag) {
                crate::layout_cert::Decoder::Equal(constant) => vec![constant],
                crate::layout_cert::Decoder::NotEqual(_) => payload,
            };
        }
        let mut words = Vec::with_capacity(definition.words);
        if definition.tag_words() != 0 {
            words.push(tag as i64);
        }
        words.extend(payload);
        fit(words, self.width(ty))
    }

    /// Run a value's drop glue (native's `synthesize_drops`).
    fn drop_value(&mut self, ty: Type, words: &[i64]) -> Run<()> {
        let ty = ty.full();
        if !self.program.owns(ty) {
            return Ok(());
        }
        match ty {
            Type::Box(pointee) => {
                let pointee = self.program.pointees[pointee];
                if self.program.owns(pointee) {
                    let fields = self.memory.load(words[0], self.width(pointee))?;
                    self.drop_value(pointee, &fields)?;
                }
                self.memory.free(words[0])
            }
            Type::Bytes | Type::String => self.memory.free(words[0]),
            Type::Arena => self.arena_release(words[0]),
            Type::AllocatorContext => self.context_release(words[0]),
            Type::AllocBox(pointee) => {
                let pointee = self.program.pointees[pointee];
                if self.program.owns(pointee) {
                    let block = self.memory.load(words[0] + 24, 1)?[0];
                    let fields = self.memory.load(block + 16, self.width(pointee))?;
                    self.drop_value(pointee, &fields)?;
                }
                self.alloc_box_release(words[0])
            }
            Type::AllocVec(element) => {
                let element = self.program.pointees[element];
                if self.program.owns(element) {
                    let width = self.width(element);
                    let [length, .., block] = self.memory.load(words[0], 8)?[..] else {
                        unreachable!("eight words")
                    };
                    for index in 0..length {
                        let address = block + 16 + index * (width * 8) as i64;
                        let item = self.memory.load(address, width)?;
                        self.drop_value(element, &item)?;
                    }
                }
                self.alloc_vec_release(words[0])
            }
            Type::ArenaBox(pointee) => {
                let pointee = self.program.pointees[pointee];
                if self.program.owns(pointee) {
                    let fields = self.memory.load(words[0], self.width(pointee))?;
                    self.drop_value(pointee, &fields)?;
                }
                self.arena_box_release(words[0])
            }
            Type::Vec(element) => {
                let element = self.program.pointees[element];
                if self.program.owns(element) {
                    let width = self.width(element);
                    let length = self.memory.load(words[0], 1)?[0];
                    for index in 0..length {
                        let address = words[0] + 16 + index * (width * 8) as i64;
                        let item = self.memory.load(address, width)?;
                        self.drop_value(element, &item)?;
                    }
                }
                self.memory.free(words[0])
            }
            Type::Enum(index) => {
                let definition = &self.program.enums[index];
                if self.program.unwind_functions.contains_key(&index) {
                    return unsupported("the unwind cleanup of a linear type");
                }
                if definition.foreign.is_some() {
                    return unsupported("a foreign resource");
                }
                if let Some((element, capacity)) = definition.dynamic_array {
                    let width = self.width(element);
                    let length = usize::try_from(words[0]).unwrap_or(0).min(capacity);
                    for slot in (0..length).rev() {
                        let start = 1 + slot * width;
                        self.drop_value(element, &words[start..start + width])?;
                    }
                    return Ok(());
                }
                let tag = match definition.niche() {
                    Some(niche) => {
                        let empty = (0..definition.variants.len()).find(|tag| {
                            matches!(niche.decoder(*tag),
                                crate::layout_cert::Decoder::Equal(constant) if constant == words[0])
                        });
                        match empty {
                            Some(tag) => tag,
                            None => (0..definition.variants.len())
                                .find(|tag| {
                                    matches!(
                                        niche.decoder(*tag),
                                        crate::layout_cert::Decoder::NotEqual(_)
                                    )
                                })
                                .expect("a niche's payload variant"),
                        }
                    }
                    None if definition.tag_words() == 0 => 0,
                    None => words[0] as usize,
                };
                let mut offset = definition.tag_words();
                let fields = definition.variants[tag].fields.clone();
                for field in fields {
                    let width = self.width(field);
                    self.drop_value(field, &words[offset..offset + width])?;
                    offset += width;
                }
                Ok(())
            }
            Type::Once(_) => {
                // The environment's drop glue: its captures, then itself.
                let environment = words[1];
                if environment == 0 {
                    return Ok(());
                }
                let drop = self.memory.load(environment, 1)?[0];
                let Some(types) = usize::try_from(drop & !DROP)
                    .ok()
                    .filter(|_| drop & DROP != 0)
                    .and_then(|index| self.closure_types.get(index).cloned())
                else {
                    return fault(format!("an environment without drop glue: {drop:#x}"));
                };
                let mut offset = 8;
                for ty in types {
                    let width = self.width(ty);
                    let capture = self.memory.load(environment + offset, width)?;
                    self.drop_value(ty, &capture)?;
                    offset += (width * 8) as i64;
                }
                self.memory.free(environment)
            }
            Type::Union(index) => {
                let members = &self.program.unions[index].members;
                let Some(member) = usize::try_from(words[0])
                    .ok()
                    .and_then(|tag| members.get(tag))
                    .copied()
                else {
                    return fault(format!("a union tag {} outside its members", words[0]));
                };
                let width = self.width(member);
                self.drop_value(member, &words[1..1 + width])
            }
            Type::DynObj(object) => {
                let members = self
                    .program
                    .dyn_members
                    .get(object)
                    .cloned()
                    .unwrap_or_default();
                if let Some(entry) = usize::try_from(words[0])
                    .ok()
                    .and_then(|index| members.get(index))
                    && self.program.owns(entry.member)
                {
                    let payload = self.memory.load(words[1], self.width(entry.member))?;
                    self.drop_value(entry.member, &payload)?;
                }
                self.memory.free(words[1])
            }
            other => unsupported(format!("dropping a {other:?}")),
        }
    }
}

/// A run stopped at a statement or terminator: a panic, which unwinds to
/// the given block (or out of the frame), or a stop.
enum Raise {
    Panic(Diagnostic, Option<BlockId>),
    Stop(Stop),
}

impl Raise {
    /// A Kush panic unwinds; any other error (a fatal abort, an exhausted
    /// budget, a rejected foreign call) ends the run, as on the tree.
    fn at(stop: Stop, unwind: Option<BlockId>) -> Self {
        match stop {
            Stop::Panic(diagnostic) if diagnostic.message.starts_with("panic") => {
                Raise::Panic(diagnostic, unwind)
            }
            other => Raise::Stop(other),
        }
    }
}

/// The function a code word names.
fn code_function(word: i64) -> Run<usize> {
    if word & CODE != 0 && word & DROP == 0 {
        Ok((word & !CODE) as usize)
    } else {
        fault(format!("a call through the non-code word {word:#x}"))
    }
}

/// The bytes the runtime's allocator hands out for a request: a 16-byte
/// size class up to its pool limit, the exact size above it.
fn physical(bytes: usize) -> usize {
    if bytes <= 1024 {
        bytes.max(1).next_multiple_of(16)
    } else {
        bytes
    }
}

/// `words` padded with zeros or cut to `width` words.
fn fit(mut words: Words, width: usize) -> Words {
    words.resize(width, 0);
    words
}

fn target_name(target: &crate::executable::Target) -> String {
    variant_path(&format!("{target:?}"))
}

fn rvalue_name(rvalue: &Rvalue) -> String {
    format!("the rvalue {}", variant_path(&format!("{rvalue:?}")))
}

/// A debug form's variant and the variant of its first field: `Alloc(ArenaNew`
/// of `Alloc(ArenaNew, [...])`.
fn variant_path(text: &str) -> String {
    let word_end = |text: &str| {
        text.find(|c: char| !c.is_alphanumeric())
            .unwrap_or(text.len())
    };
    let outer = word_end(text);
    match text[outer..].strip_prefix('(') {
        Some(rest) if rest.starts_with(|c: char| c.is_ascii_uppercase()) => {
            format!("{}({}", &text[..outer], &rest[..word_end(rest)])
        }
        _ => text[..outer].to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(source: &str) -> (String, Run<(i64, MemoryStats)>) {
        let program = crate::executable::check(source).expect("the test program checks");
        let mut output = Vec::new();
        let result = evaluate(&program, &mut output);
        (String::from_utf8(output).unwrap(), result)
    }

    #[test]
    fn scalar_programs_print_and_panic_as_the_tree_evaluator() {
        let (output, result) = run(
            "fn fib(n: i64) -> i64 { if n < 2 { n } else { fib(n - 1) + fib(n - 2) } }
            fn main() -> Unit ! {io} {
                let mut i = 0;
                while i < 6 { print_i64(fib(i)); i = i + 1; }
            }",
        );
        assert_eq!(output, "0\n1\n1\n2\n3\n5\n");
        assert!(result.is_ok());
        let (output, result) =
            run("fn main() -> Unit ! {io} { print_i64(1); print_i64(9223372036854775807 + 1); }");
        assert_eq!(output, "1\n");
        let Err(Stop::Panic(diagnostic)) = result else {
            panic!("an overflow panics: {result:?}");
        };
        assert_eq!(diagnostic.message, "panic: checked arithmetic failed");
    }

    #[test]
    fn boxes_are_allocated_and_freed_once() {
        let (output, result) = run("enum List { Nil, Cons(i64, Box<List>) }
            fn sum(list: List) -> i64 {
                match list { Nil => 0, Cons(head, tail) => head + sum(Box.take(tail)) }
            }
            fn main() -> Unit ! {io, alloc} {
                let list = List.Cons(1, Box.new(List.Cons(2, Box.new(List.Nil))));
                print_i64(sum(list));
            }");
        assert_eq!(output, "3\n");
        let (_, stats) = result.expect("the program runs");
        assert_eq!(stats.allocations, 2);
        assert_eq!(stats.deallocations, 2);
    }
}
