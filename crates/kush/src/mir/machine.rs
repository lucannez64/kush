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
use std::io::Write;
use std::rc::Rc;

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
fn fault<T>(what: impl Into<String>) -> Run<T> {
    Err(Stop::Fault(what.into()))
}

/// Code pointers live in their own range of words.
const CODE: i64 = 1 << 62;

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
    /// The stack allocation of each local whose address the body takes.
    homes: Vec<Option<i64>>,
    /// `None` for the entry function.
    caller: Option<Return>,
}

struct Machine<'p, 'o> {
    program: &'p Executable,
    bodies: Vec<Option<Rc<Body>>>,
    memory: Memory,
    output: &'o mut dyn Write,
    stack: Vec<Frame>,
    /// The panic a cleanup block runs for.
    unwinding: Option<Diagnostic>,
    fuel: usize,
}

/// Run the program's entry function on the machine. Returns its result word
/// (zero for `Unit`) and the allocation stats a native build reports.
pub fn evaluate(program: &Executable, output: &mut dyn Write) -> Run<(i64, MemoryStats)> {
    let entry = program.entry().map_err(Stop::Panic)?;
    let mut machine = Machine {
        program,
        bodies: vec![None; program.functions.len()],
        memory: Memory::default(),
        output,
        stack: Vec::new(),
        unwinding: None,
        fuel: program.eval_fuel,
    };
    machine.memory.stats.fusions = program.fusions;
    machine.enter(entry, Vec::new(), None)?;
    let result = machine.run()?;
    if machine.memory.live_heap != 0 {
        return Err(Stop::Panic(Diagnostic::new(
            Span::default(),
            "internal ownership error: live owning allocations after normal program exit",
        )));
    }
    Ok((result, machine.memory.stats))
}

/// `KUSH_MACHINE_CHECK`: run the machine on a program the tree evaluator ran
/// (`tree` is its outcome, `tree_output` what it printed). A difference is
/// an error; a construct the machine does not cover is appended, with the
/// program's entry function, to the file `KUSH_MACHINE_REPORT` names.
pub(crate) fn check(
    program: &Executable,
    tree_output: &[u8],
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
    let mut output = Vec::new();
    let machine = match evaluate(program, &mut output) {
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
    if output != tree_output {
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
    fn enter(&mut self, function: usize, args: Vec<Words>, caller: Option<Return>) -> Run<()> {
        let body = self.body(function)?;
        let mut locals = body
            .locals
            .iter()
            .map(|local| vec![0; self.width(local.ty)])
            .collect::<Vec<_>>();
        let slots = self.program.functions[function].parameter_slots.clone();
        for (position, words) in args.into_iter().enumerate() {
            let slot = slots.as_ref().map_or(position, |slots| slots[position]);
            let width = locals[slot].len();
            locals[slot] = fit(words, width);
        }
        let taken = loops::address_taken(&body);
        let mut homes = vec![None; body.locals.len()];
        for local in taken {
            let home = self.memory.allocate(locals[local].len() * 8, false);
            self.memory.store(home, &locals[local])?;
            homes[local] = Some(home);
        }
        self.stack.push(Frame {
            body,
            block: 0,
            statement: 0,
            locals,
            homes,
            caller,
        });
        Ok(())
    }

    /// Pop the top frame, releasing its locals' homes.
    fn leave(&mut self) -> Run<Frame> {
        let frame = self.stack.pop().expect("a frame to leave");
        for home in frame.homes.iter().flatten() {
            self.memory.free(*home)?;
        }
        Ok(frame)
    }

    fn run(&mut self) -> Run<i64> {
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

    /// Run one statement or terminator. `Some` is the entry function's
    /// result.
    fn step(&mut self) -> std::result::Result<Option<i64>, Raise> {
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
                        self.enter(*index, values, Some(caller))
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
                    Callee::Builtin { index, .. } => {
                        let target = body.builtins.0[*index];
                        return Err(Raise::Stop(Stop::Unsupported(format!(
                            "the builtin {}",
                            target_name(&target)
                        ))));
                    }
                    Callee::Indirect(_) => {
                        return Err(Raise::Stop(Stop::Unsupported("an indirect call".into())));
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
                    None => return Ok(Some(words.first().copied().unwrap_or(0))),
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
            Rvalue::StructEq(..) => return unsupported("structural equality"),
            other => return unsupported(rvalue_name(other)),
        })
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
    fn at(stop: Stop, unwind: Option<BlockId>) -> Self {
        match stop {
            Stop::Panic(diagnostic) => Raise::Panic(diagnostic, unwind),
            other => Raise::Stop(other),
        }
    }
}

/// `words` padded with zeros or cut to `width` words.
fn fit(mut words: Words, width: usize) -> Words {
    words.resize(width, 0);
    words
}

fn target_name(target: &crate::executable::Target) -> String {
    let text = format!("{target:?}");
    let end = text
        .find(|c: char| !c.is_alphanumeric())
        .unwrap_or(text.len());
    text[..end].to_string()
}

fn rvalue_name(rvalue: &Rvalue) -> String {
    let text = format!("{rvalue:?}");
    let end = text
        .find(|c: char| !c.is_alphanumeric())
        .unwrap_or(text.len());
    format!("the rvalue {}", &text[..end])
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
