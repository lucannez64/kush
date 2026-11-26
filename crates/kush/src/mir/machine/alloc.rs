//! Box reuse, fallible allocation and arenas on the machine
//! (FND-EVAL-RUNTIME), with kush.c's layouts:
//!
//! - An arena is a counted allocation `[references, chunks, strategy]`.
//!   Its chunks are physical storage (not counted) `[next, used,
//!   capacity, padding, data...]`, and each payload follows an 8-byte
//!   header holding its arena. Every arena box holds a reference; the last
//!   release frees the chunks and the arena.
//! - A fallible operation's result is `[tag, payload...]`, as native's
//!   `try_result` builds it.

use super::*;
use crate::runtime_types::ResultShape;

/// The machine has no allocation budget (`KUSH_MACHINE_CHECK` compares only
/// runs without one), so a fallible request within the limits succeeds.
const BYTES_LIMIT: i64 = 16 * 1024 * 1024;

/// An arena chunk's header bytes before its data.
const CHUNK_HEADER: i64 = 32;

impl Machine<'_, '_> {
    pub(super) fn alloc_op(
        &mut self,
        body: &Body,
        op: AllocOp,
        operands: &[Operand],
        ty: Type,
    ) -> Run<Words> {
        let words = operands
            .iter()
            .map(|operand| self.operand(*operand))
            .collect::<Run<Vec<_>>>()?;
        let types = operands
            .iter()
            .map(|operand| body.operand_ty(*operand))
            .collect::<Vec<_>>();
        let width = self.width(ty);
        Ok(match op {
            AllocOp::ArenaNew => vec![self.arena_new(0)?],
            AllocOp::ArenaNewWith => vec![self.arena_new(words[0][0])?],
            AllocOp::ArenaAlloc | AllocOp::ArenaTryAlloc { .. } => {
                let handle = self.memory.load(words[0][0], 1)?[0];
                let bytes = (self.width(types[1]) * 8) as i64;
                let pointer = self.arena_alloc(handle, bytes)?;
                self.memory.store(pointer, &words[1])?;
                match op {
                    AllocOp::ArenaTryAlloc { shape } => self.try_words(ty, shape, true, &[pointer]),
                    _ => vec![pointer],
                }
            }
            AllocOp::ArenaBoxRead => {
                let pointer = self.memory.load(words[0][0], 1)?[0];
                self.memory.load(pointer, width)?
            }
            AllocOp::ArenaBoxTake => {
                let pointer = words[0][0];
                let payload = self.memory.load(pointer, width)?;
                self.arena_box_release(pointer)?;
                payload
            }
            AllocOp::BoxReuse { grow } => {
                let pointer = words[0][0];
                let Type::Box(old) = types[0] else {
                    return fault("Box.reuse of a non-box");
                };
                let old = self.program.pointees[old];
                let previous = self.memory.load(pointer, self.width(old))?;
                self.drop_value(old, &previous)?;
                let new_bytes = self.width(types[1]) * 8;
                let pointer = if grow && new_bytes > previous.len() * 8 {
                    self.memory.grow(pointer, new_bytes, false)?
                } else {
                    pointer
                };
                self.memory.store(pointer, &words[1])?;
                self.memory.stats.reuses += 1;
                vec![pointer]
            }
            AllocOp::BoxWrite => {
                let pointer = self.memory.load(words[0][0], 1)?[0];
                self.memory.store(pointer, &words[1])?;
                vec![0]
            }
            AllocOp::BoxTryNew { shape } => {
                let pointer = self.memory.allocate(words[0].len().max(1) * 8, true);
                self.memory.store(pointer, &words[0])?;
                self.try_words(ty, shape, true, &[pointer])
            }
            AllocOp::BoxTryReuse { shape } => {
                let pointer = words[0][0];
                let Type::Box(old) = types[0] else {
                    return fault("Box.try_reuse of a non-box");
                };
                let old = self.program.pointees[old];
                let previous = self.memory.load(pointer, self.width(old))?;
                let grown = self.memory.grow(pointer, self.width(types[1]) * 8, true)?;
                self.drop_value(old, &previous)?;
                self.memory.store(grown, &words[1])?;
                self.memory.stats.reuses += 1;
                self.try_words(ty, shape, true, &[grown])
            }
            AllocOp::BytesTryWithCapacity { shape } => {
                let requested = words[0][0];
                if (0..=BYTES_LIMIT).contains(&requested) {
                    let handle = self.memory.allocate_buffer(16 + requested as usize);
                    self.memory.store(handle, &[0, requested])?;
                    self.try_words(ty, shape, true, &[handle])
                } else {
                    self.try_words(ty, shape, false, &[requested])
                }
            }
            other => return unsupported(format!("the rvalue Alloc({other:?})")),
        })
    }

    /// A fallible operation's result words: the ok or error tag, then the
    /// payload, padded to the result's width.
    fn try_words(&self, ty: Type, shape: ResultShape, ok: bool, payload: &[i64]) -> Words {
        let tag = if ok { shape.ok_tag } else { shape.err_tag };
        let mut words = vec![tag as i64];
        words.extend_from_slice(payload);
        fit(words, self.width(ty))
    }

    // ---- arenas ------------------------------------------------------------

    /// `kush_arena_create`: a new arena with an optional strategy code word.
    fn arena_new(&mut self, strategy: i64) -> Run<i64> {
        let arena = self.memory.allocate(24, true);
        self.memory.store(arena, &[1, 0, strategy])?;
        Ok(arena)
    }

    /// `kush_arena_alloc`: room for `bytes` bytes after an arena header, in
    /// the current chunk or a fresh one.
    fn arena_alloc(&mut self, arena: i64, bytes: i64) -> Run<i64> {
        let need = (bytes + 8 + 15) & !15;
        let [references, mut chunk, strategy] = self.memory.load(arena, 3)?[..] else {
            unreachable!("three words")
        };
        let (used, capacity) = if chunk == 0 {
            (0, 0)
        } else {
            let header = self.memory.load(chunk + 8, 2)?;
            (header[0], header[1])
        };
        let mut used = used;
        if chunk == 0 || capacity - used < need {
            let capacity = self.chunk_capacity(strategy, need, capacity)?;
            let total = ((CHUNK_HEADER + capacity + 15) & !15) as usize;
            let fresh = self.memory.allocate(total, false);
            self.memory.store(fresh, &[chunk, 0, capacity, 0])?;
            chunk = fresh;
            used = 0;
        }
        let start = chunk + CHUNK_HEADER + used;
        self.memory.store(chunk + 8, &[used + need])?;
        self.memory.store(start, &[arena])?;
        self.memory.store(arena, &[references + 1, chunk])?;
        Ok(start + 8)
    }

    /// `kush_arena_chunk_capacity`: the default 4 KiB minimum, or what the
    /// user's strategy chooses (never below `need`). A panic in the strategy
    /// aborts, as in the native runtime.
    fn chunk_capacity(&mut self, strategy: i64, need: i64, current: i64) -> Run<i64> {
        if strategy == 0 {
            return Ok(need.max(4096));
        }
        let function = code_function(strategy)?;
        let chosen = match self.call_nested(function, vec![vec![need], vec![current]]) {
            Ok(words) => words[0],
            Err(Stop::Panic(error)) if error.message.starts_with("panic") => {
                return Err(Stop::Panic(Diagnostic::new(
                    error.span,
                    format!(
                        "fatal: an arena strategy panicked, which aborts the process ({})",
                        error.message
                    ),
                )));
            }
            Err(other) => return Err(other),
        };
        Ok(if chosen < 0 { need } else { chosen.max(need) })
    }

    /// Drop one reference to an arena; the last frees its chunks and it.
    pub(super) fn arena_release(&mut self, arena: i64) -> Run<()> {
        let [references, mut chunk] = self.memory.load(arena, 2)?[..] else {
            unreachable!("two words")
        };
        if references <= 0 {
            return fault("an arena released more often than it is held");
        }
        if references > 1 {
            return self.memory.store(arena, &[references - 1]);
        }
        while chunk != 0 {
            let next = self.memory.load(chunk, 1)?[0];
            self.memory.free(chunk)?;
            chunk = next;
        }
        self.memory.free(arena)
    }

    /// `kush_arena_box_release`: the payload's header names its arena.
    pub(super) fn arena_box_release(&mut self, payload: i64) -> Run<()> {
        let arena = self.memory.load(payload - 8, 1)?[0];
        self.arena_release(arena)
    }
}
