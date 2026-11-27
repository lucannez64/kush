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
//!   64 KiB chunks (counted allocations, as kush.c counts them) with one
//!   spare kept.

use super::*;

/// A continuation-stack chunk's header bytes before its data.
const KCHUNK_HEADER: i64 = 32;
const KCHUNK: i64 = 64 * 1024;

#[derive(Clone, Copy)]
pub(super) struct HandlerFrame {
    code: i64,
    environment: i64,
    once: i64,
    consumed: bool,
    /// The activation's cell id (0 for abort frames).
    cell: i64,
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

/// What a perform takes from a frame: `(code, environment, once)`, or
/// nothing for a consumed `once` frame.
type Taken = Option<(i64, i64, i64)>;

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
            RuntimeOp::HandlerPush { reusable, .. } => {
                let (environment, once) = match body.operand_ty(operands[0]) {
                    Type::Once(_) => (
                        words[0].get(1).copied().unwrap_or(0),
                        if reusable { 2 } else { 1 },
                    ),
                    _ => (0, 0),
                };
                let cell = self.next_cell;
                self.next_cell += 1;
                self.handlers.push(HandlerFrame {
                    code: words[0][0],
                    environment,
                    once,
                    consumed: false,
                    cell,
                });
                vec![cell]
            }
            // A noncapturing handler's cell is its code word (bit `CODE`
            // set, unlike frame ids).
            RuntimeOp::HandlerCell => vec![words[0][0]],
            RuntimeOp::HandlerPop => {
                if !self.handlers.is_empty() {
                    self.pop_handler()?;
                }
                vec![0]
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
            RuntimeOp::AbortHandlerPush { .. } => {
                self.handlers.push(HandlerFrame {
                    code: words[0][0],
                    environment: 0,
                    once: 0,
                    consumed: false,
                    cell: 0,
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
            RuntimeOp::AbortRaiseAt => {
                self.memory.store(words[0][0], &words[1])?;
                self.abort_word = words[0][0];
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
        cell: i64,
        span: Span,
    ) -> Run<Flow> {
        let taken = if cell == 0 {
            self.lookup(operation as i64)?
        } else {
            self.take_cell(cell)?
        };
        let Some((code, environment, once)) = taken else {
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

    /// The frames a spawned task inherits: none. A task reaches its handlers
    /// through the cells its body captured (FND-HANDLERS-ONE-DELETE).
    pub(super) fn inheritable_handlers(&self) -> Vec<HandlerFrame> {
        Vec::new()
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

    /// `kush_handler_lookup`: a perform without a capability finds nothing;
    /// performs reach handlers through cells (FND-HANDLERS-ONE-DELETE).
    fn lookup(&mut self, _operation: i64) -> Run<Option<(i64, i64, i64)>> {
        Ok(None)
    }

    /// `kush_handler_take`: what a perform takes from `frame`, as
    /// `(code, environment, once)`, and the frame afterwards. A consumed
    /// `once` frame answers with nothing.
    fn take(&mut self, mut frame: HandlerFrame) -> Run<(Taken, HandlerFrame)> {
        if frame.consumed {
            return Ok((None, frame));
        }
        let taken = match frame.once {
            2 => {
                // A reusable handler keeps its environment; each call owns
                // a fresh copy.
                let bytes = self.memory.size(frame.environment)?;
                let copy = self.memory.allocate(bytes, true);
                let data = self.memory.load_bytes(frame.environment, bytes)?;
                self.memory.store_bytes(copy, &data)?;
                (frame.code, copy, 1)
            }
            1 => {
                frame.consumed = true;
                (frame.code, std::mem::take(&mut frame.environment), 1)
            }
            _ => (frame.code, frame.environment, 0),
        };
        Ok((Some(taken), frame))
    }

    /// `kush_handler_perform` with a cell: the frame of that activation, in
    /// this task or (for a capability a spawned task carries) another. A
    /// task does not get another task's capturing handler (decision D3).
    fn take_cell(&mut self, cell: i64) -> Run<Option<(i64, i64, i64)>> {
        if cell & CODE != 0 {
            return Ok(Some((cell, 0, 0)));
        }
        if let Some(index) = self.handlers.iter().rposition(|frame| frame.cell == cell) {
            let (taken, frame) = self.take(self.handlers[index])?;
            self.handlers[index] = frame;
            return Ok(taken);
        }
        for task in 0..self.tasks.len() {
            if let Some(index) = self.tasks[task]
                .handlers
                .iter()
                .rposition(|frame| frame.cell == cell)
            {
                if self.tasks[task].handlers[index].once != 0 {
                    return Ok(None);
                }
                let (taken, frame) = self.take(self.tasks[task].handlers[index])?;
                self.tasks[task].handlers[index] = frame;
                return Ok(taken);
            }
        }
        Ok(None)
    }

    // ---- the continuation stack ------------------------------------------

    /// `kush_kstack_push`: a word-aligned environment of `bytes` bytes.
    pub(super) fn kstack_push(&mut self, bytes: i64) -> Run<i64> {
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
