//! Effect handlers, aborts and the continuation stack on the machine
//! (FND-EVAL-EFFECTS), as kush.c runs them:
//!
//! - The handler stack holds `(operation, code, environment, once,
//!   consumed)` frames. A `perform` calls the innermost frame for its
//!   operation; a `once` frame hands over its environment, a reusable one
//!   (`once == 2`) a fresh copy. A redirect frame (operation -1) sends the
//!   lookup below the depth it records.
//! - An abort stores its payload in the handling frame's buffer and sets
//!   the abort word; functions then return dummies (`Abort`) until the
//!   handler's activation clears it.
//! - Environments of `multi fn` tokens live on the continuation stack:
//!   64 KiB chunks (counted allocations) with one spare kept. kush.c counts
//!   chunks; the tree evaluator counts each environment, so check mode does
//!   not compare the stats of a run that pushed one.

use super::*;

/// A continuation-stack chunk's header bytes before its data.
const KCHUNK_HEADER: i64 = 32;
const KCHUNK: i64 = 64 * 1024;

#[derive(Clone, Copy)]
pub(super) struct HandlerFrame {
    operation: i64,
    code: i64,
    environment: i64,
    once: i64,
    consumed: bool,
    /// An abort frame (its code is the payload buffer).
    abort: bool,
}

/// The continuation stack: its chunks, innermost last, as `(allocation,
/// capacity)`, the top (an address in the last chunk, 0 when empty), and a
/// released chunk kept for reuse.
#[derive(Default)]
pub(super) struct KStack {
    chunks: Vec<(i64, i64)>,
    top: i64,
    spare: Option<(i64, i64)>,
}

const NO_HANDLER: &str = "no dynamically active handler for this operation";

impl Machine<'_, '_> {
    pub(super) fn runtime_op(
        &mut self,
        body: &Body,
        op: RuntimeOp,
        operands: &[Operand],
        span: Span,
    ) -> Run<Words> {
        let words = operands
            .iter()
            .map(|operand| self.operand(*operand))
            .collect::<Run<Vec<_>>>()?;
        Ok(match op {
            RuntimeOp::HandlerDepth => vec![self.handlers.len() as i64],
            RuntimeOp::HandlerRestore => {
                let depth = words[0][0].max(0) as usize;
                while self.handlers.len() > depth {
                    self.pop_handler()?;
                }
                vec![0]
            }
            RuntimeOp::HandlerPush {
                operation,
                reusable,
            } => {
                let (environment, once) = match body.operand_ty(operands[0]) {
                    Type::Once(_) => (
                        words[0].get(1).copied().unwrap_or(0),
                        if reusable { 2 } else { 1 },
                    ),
                    _ => (0, 0),
                };
                self.handlers.push(HandlerFrame {
                    operation: operation as i64,
                    code: words[0][0],
                    environment,
                    once,
                    consumed: false,
                    abort: false,
                });
                vec![0]
            }
            RuntimeOp::HandlerPop => {
                if !self.handlers.is_empty() {
                    self.pop_handler()?;
                }
                vec![0]
            }
            RuntimeOp::HandlerRedirect => {
                let (target, before) = (words[0][0], self.handlers.len() as i64);
                if before > target {
                    self.handlers.push(HandlerFrame {
                        operation: -1,
                        code: target,
                        environment: 0,
                        once: 1,
                        consumed: true,
                        abort: false,
                    });
                }
                vec![before]
            }
            RuntimeOp::Perform { .. } => {
                return fault("a perform outside statement_flow");
            }
            RuntimeOp::AbortBuffer { words } => {
                let buffer = self.memory.allocate(words.max(1) * 8, false);
                self.stack
                    .last_mut()
                    .expect("a frame")
                    .temporaries
                    .push(buffer);
                vec![buffer]
            }
            RuntimeOp::AbortHandlerPush { operation } => {
                self.handlers.push(HandlerFrame {
                    operation: operation as i64,
                    code: words[0][0],
                    environment: 0,
                    once: 0,
                    consumed: false,
                    abort: true,
                });
                vec![0]
            }
            RuntimeOp::AbortRaise { operation } => {
                let Some((buffer, ..)) = self.lookup(operation as i64)? else {
                    return panic_at(span, NO_HANDLER);
                };
                self.memory.store(buffer, &words[0])?;
                self.abort_word = buffer;
                vec![0]
            }
            RuntimeOp::AbortWord => vec![self.abort_word],
            RuntimeOp::AbortClear => {
                self.abort_word = 0;
                vec![0]
            }
            RuntimeOp::ContinuationMark => vec![self.kstack.top],
            RuntimeOp::ContinuationRestore => {
                self.kstack_restore(words[0][0])?;
                vec![0]
            }
        })
    }

    /// `perform`: call the innermost handler frame for `operation` with the
    /// payload and the resume value, as a frame on the stack (the handler
    /// may suspend the task).
    pub(super) fn perform(
        &mut self,
        operation: usize,
        payload: Words,
        resume: Words,
        span: Span,
    ) -> Run<Flow> {
        let Some((code, environment, once)) = self.lookup(operation as i64)? else {
            return panic_at(span, NO_HANDLER);
        };
        Ok(Flow::Call {
            function: code_function(code)?,
            args: vec![payload, resume],
            environment: (once != 0).then_some(environment),
            then: None,
            catch: None,
        })
    }

    /// The frames a spawned task inherits: the innermost visible ones that
    /// are copyable `fn` handlers, down to the first that is not (a
    /// capturing, `once` or abort frame is a task boundary).
    pub(super) fn inheritable_handlers(&self) -> Vec<HandlerFrame> {
        let mut inherited = Vec::new();
        let mut index = self.handlers.len();
        while index > 0 {
            index -= 1;
            let frame = self.handlers[index];
            if frame.operation == -1 {
                index = frame.code.max(0) as usize;
                continue;
            }
            if frame.environment != 0 || frame.once != 0 || frame.abort {
                break;
            }
            inherited.push(frame);
        }
        inherited.reverse();
        inherited
    }

    /// Pop the innermost handler frame, dropping an environment it still
    /// owns.
    pub(super) fn pop_handler(&mut self) -> Run<()> {
        let frame = self.handlers.pop().expect("a handler frame");
        if frame.environment != 0 {
            self.drop_environment(frame.environment)?;
        }
        Ok(())
    }

    /// `kush_handler_lookup`: the innermost frame for `operation`, as
    /// `(code, environment, once)`. A consumed `once` frame still answers
    /// for its operation, with nothing.
    fn lookup(&mut self, operation: i64) -> Run<Option<(i64, i64, i64)>> {
        let mut index = self.handlers.len();
        while index > 0 {
            index -= 1;
            let frame = self.handlers[index];
            if frame.operation == -1 {
                index = frame.code.max(0) as usize;
                continue;
            }
            if frame.operation != operation {
                continue;
            }
            if frame.consumed {
                return Ok(None);
            }
            return Ok(Some(match frame.once {
                2 => {
                    // A reusable handler keeps its environment; each call
                    // owns a fresh copy.
                    let bytes = self.memory.size(frame.environment)?;
                    let copy = self.memory.allocate(bytes, true);
                    let data = self.memory.load_bytes(frame.environment, bytes)?;
                    self.memory.store_bytes(copy, &data)?;
                    (frame.code, copy, 1)
                }
                1 => {
                    let frame = &mut self.handlers[index];
                    frame.consumed = true;
                    let environment = std::mem::take(&mut frame.environment);
                    (frame.code, environment, 1)
                }
                _ => (frame.code, frame.environment, 0),
            }));
        }
        Ok(None)
    }

    // ---- the continuation stack ------------------------------------------

    /// `kush_kstack_push`: a word-aligned environment of `bytes` bytes.
    pub(super) fn kstack_push(&mut self, bytes: i64) -> Run<i64> {
        self.continuations = true;
        let need = (bytes + 15) & !15;
        let room = self.kstack.chunks.last().map_or(0, |(chunk, capacity)| {
            chunk + KCHUNK_HEADER + capacity - self.kstack.top
        });
        if self.kstack.chunks.is_empty() || room < need {
            let fresh = match self.kstack.spare.take() {
                Some(spare) if need <= KCHUNK => spare,
                spare => {
                    self.kstack.spare = spare;
                    let capacity = need.max(KCHUNK);
                    let chunk = self
                        .memory
                        .allocate((KCHUNK_HEADER + capacity) as usize, true);
                    (chunk, capacity)
                }
            };
            self.kstack.chunks.push(fresh);
            self.kstack.top = fresh.0 + KCHUNK_HEADER;
        }
        let environment = self.kstack.top;
        self.kstack.top += need;
        Ok(environment)
    }

    /// `kush_kstack_restore`: release everything pushed since `mark`.
    fn kstack_restore(&mut self, mark: i64) -> Run<()> {
        let inside = |(chunk, capacity): (i64, i64)| {
            (chunk + KCHUNK_HEADER..=chunk + KCHUNK_HEADER + capacity).contains(&mark)
        };
        while let Some(&chunk) = self.kstack.chunks.last() {
            if inside(chunk) {
                break;
            }
            self.kstack.chunks.pop();
            self.release_kchunk(chunk)?;
            // The previous chunk is full up to its end, as far as a mark in
            // it is concerned.
            self.kstack.top = self
                .kstack
                .chunks
                .last()
                .map_or(0, |(chunk, capacity)| chunk + KCHUNK_HEADER + capacity);
        }
        let Some(&chunk) = self.kstack.chunks.last() else {
            if mark != 0 {
                return fault("a continuation mark above the stack");
            }
            return Ok(());
        };
        if mark > self.kstack.top {
            return fault("a continuation mark above the top");
        }
        self.kstack.top = mark;
        if mark == chunk.0 + KCHUNK_HEADER && self.kstack.chunks.len() == 1 {
            // Empty: give the chunk back so a finished program owns nothing.
            self.kstack.chunks.pop();
            self.kstack.top = 0;
            self.release_kchunk(chunk)?;
        }
        Ok(())
    }

    fn release_kchunk(&mut self, chunk: (i64, i64)) -> Run<()> {
        if self.kstack.spare.is_none() && chunk.1 == KCHUNK {
            self.kstack.spare = Some(chunk);
            return Ok(());
        }
        self.memory.free(chunk.0)
    }

    /// Free the spare chunk at the end of a run (`kush_kstack_drain`).
    pub(super) fn kstack_drain(&mut self) -> Run<()> {
        match self.kstack.spare.take() {
            Some((chunk, _)) => self.memory.free(chunk),
            None => Ok(()),
        }
    }
}
