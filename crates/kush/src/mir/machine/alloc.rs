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

/// Where a container's blocks come from: an allocator value's alloc, free
/// and optional realloc code words, or an allocator context (whose state
/// and method functions it holds: `[references, state, spec, alloc, free,
/// grow]`). A block is a `Bytes` the allocator hands out.
#[derive(Clone, Copy)]
struct Binding {
    alloc: i64,
    free: i64,
    realloc: i64,
    context: i64,
}

impl Binding {
    /// The binding of an `Allocator` or `AllocatorContext` operand.
    fn of(ty: Type, words: &[i64]) -> Self {
        match ty {
            Type::AllocatorContext => Binding {
                alloc: 0,
                free: 0,
                realloc: 0,
                context: words[0],
            },
            _ => Binding {
                alloc: words[0],
                free: words[1],
                realloc: words[2],
                context: 0,
            },
        }
    }
    /// The binding an allocator vector records: `[length, capacity, width,
    /// alloc, free, realloc, context, block]`.
    fn of_vec(fields: &[i64]) -> Self {
        Binding {
            alloc: fields[3],
            free: fields[4],
            realloc: fields[5],
            context: fields[6],
        }
    }
}

/// A panic in a runtime bookkeeping callback (an allocator release, an
/// arena strategy) aborts instead of unwinding, as in the native runtime:
/// its message no longer starts with "panic", so nothing catches it.
fn no_unwind(result: Run<Words>, context: &str) -> Run<Words> {
    match result {
        Err(Stop::Panic(error)) if error.message.starts_with("panic") => {
            Err(Stop::Panic(Diagnostic::new(
                error.span,
                format!(
                    "fatal: {context} panicked, which aborts the process ({})",
                    error.message
                ),
            )))
        }
        other => other,
    }
}

impl Machine<'_, '_> {
    pub(super) fn alloc_op(
        &mut self,
        body: &Body,
        op: AllocOp,
        operands: &[Operand],
        ty: Type,
        span: Span,
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
            AllocOp::AllocatorNew => {
                let realloc = words.get(2).map_or(0, |realloc| realloc[0]);
                vec![words[0][0], words[1][0], realloc]
            }
            AllocOp::ContextNew { spec } => {
                let Some(checked) = self.program.allocator_contexts.get(spec).copied() else {
                    return fault("an allocator context of an unknown spec");
                };
                let state = self
                    .memory
                    .allocate(self.width(checked.state).max(1) * 8, true);
                self.memory.store(state, &words[0])?;
                let context = self.memory.allocate(48, true);
                self.memory.store(
                    context,
                    &[
                        1,
                        state,
                        spec as i64,
                        checked.alloc as i64,
                        checked.free as i64,
                        checked.grow as i64,
                    ],
                )?;
                vec![context]
            }
            AllocOp::ContextShare => {
                let context = self.memory.load(words[0][0], 1)?[0];
                let references = self.memory.load(context, 1)?[0];
                self.memory.store(context, &[references + 1])?;
                vec![context]
            }
            AllocOp::BoxNew | AllocOp::AllocBoxTryNew { .. } => {
                let binding = Binding::of(types[0], &words[0]);
                let bytes = (self.width(types[1]) * 8) as i64;
                let Some(block) = self.block_alloc(binding, bytes)? else {
                    if let AllocOp::AllocBoxTryNew { shape } = op {
                        // Nothing retained the context: drop the operation's
                        // reference before handing the payload back.
                        self.context_release(binding.context)?;
                        return Ok(self.try_words(ty, shape, false, &words[1]));
                    }
                    return panic_at(
                        span,
                        &format!("panic: allocator refused a {bytes}-byte block"),
                    );
                };
                self.memory.store(block + 16, &words[1])?;
                let handle = self.memory.allocate(32, true);
                self.memory.store(
                    handle,
                    &[binding.alloc, binding.free, binding.context, block],
                )?;
                match op {
                    AllocOp::AllocBoxTryNew { shape } => self.try_words(ty, shape, true, &[handle]),
                    _ => vec![handle],
                }
            }
            AllocOp::BoxRead => {
                let handle = self.memory.load(words[0][0], 1)?[0];
                let block = self.memory.load(handle + 24, 1)?[0];
                self.memory.load(block + 16, width)?
            }
            AllocOp::BoxTake => {
                let handle = words[0][0];
                let block = self.memory.load(handle + 24, 1)?[0];
                let payload = self.memory.load(block + 16, width)?;
                self.alloc_box_release(handle)?;
                payload
            }
            AllocOp::VecNew { element } => {
                let binding = Binding::of(types[0], &words[0]);
                let capacity = words.get(1).map_or(0, |capacity| capacity[0]);
                if capacity < 0 {
                    return panic_at(span, "panic: negative AllocVec capacity");
                }
                let element_width = self.width(element) as i64;
                let handle = self.memory.allocate(64, true);
                let mut block = 0;
                if capacity > 0 {
                    let Some(bytes) = capacity
                        .checked_mul(element_width * 8)
                        .filter(|bytes| *bytes <= i64::MAX - 16)
                    else {
                        return panic_at(span, "panic: AllocVec capacity overflow");
                    };
                    let Some(fresh) = self.block_alloc(binding, bytes)? else {
                        return panic_at(
                            span,
                            &format!("panic: allocator refused a {bytes}-byte block"),
                        );
                    };
                    block = fresh;
                }
                self.memory.store(
                    handle,
                    &[
                        0,
                        capacity,
                        element_width,
                        binding.alloc,
                        binding.free,
                        binding.realloc,
                        binding.context,
                        block,
                    ],
                )?;
                vec![handle]
            }
        })
    }

    // ---- user allocators ---------------------------------------------------

    /// `kush_alloc_block_try`: a block of at least `bytes` bytes from the
    /// allocator, or `None` when it hands back a smaller one (released
    /// through the same allocator).
    fn block_alloc(&mut self, binding: Binding, bytes: i64) -> Run<Option<i64>> {
        let block = if binding.context != 0 {
            let [_, state, _, alloc, ..] = self.memory.load(binding.context, 6)?[..] else {
                unreachable!("six words")
            };
            self.call_nested(self.code(alloc as usize), vec![vec![state], vec![bytes]])?[0]
        } else {
            let alloc = code_function(binding.alloc)?;
            self.call_nested(alloc, vec![vec![bytes]])?[0]
        };
        if self.memory.load(block + 8, 1)?[0] < bytes {
            self.block_release(binding, block)?;
            return Ok(None);
        }
        Ok(Some(block))
    }

    /// `kush_alloc_block_release`: hand a block back to its allocator. A
    /// panic in the release callback aborts.
    fn block_release(&mut self, binding: Binding, block: i64) -> Run<()> {
        if block == 0 {
            return Ok(());
        }
        let released = if binding.context != 0 {
            let [_, state, _, _, free, _] = self.memory.load(binding.context, 6)?[..] else {
                unreachable!("six words")
            };
            self.call_nested(self.code(free as usize), vec![vec![state], vec![block]])
        } else {
            let free = code_function(binding.free)?;
            self.call_nested(free, vec![vec![block]])
        };
        no_unwind(released, "an allocator release callback").map(drop)
    }

    /// `kush_alloc_block_grow`: the growth hook resizes a block. It sees the
    /// block's first `old` bytes zeroed (as its length); the live bytes are
    /// restored into the block it returns.
    fn block_grow(
        &mut self,
        binding: Binding,
        block: i64,
        old: i64,
        bytes: i64,
        span: Span,
    ) -> Run<i64> {
        let saved = self.memory.load_bytes(block + 16, old as usize)?;
        self.memory
            .store_bytes(block + 16, &vec![0; old as usize])?;
        self.memory.store(block, &[old])?;
        let grown = if binding.context != 0 {
            let [_, state, _, _, _, grow] = self.memory.load(binding.context, 6)?[..] else {
                unreachable!("six words")
            };
            self.call_nested(
                self.code(grow as usize),
                vec![vec![state], vec![block], vec![old], vec![bytes]],
            )?[0]
        } else {
            let realloc = code_function(binding.realloc)?;
            self.call_nested(realloc, vec![vec![block], vec![old], vec![bytes]])?[0]
        };
        if self.memory.load(grown + 8, 1)?[0] < bytes {
            return panic_at(
                span,
                &format!(
                    "panic: allocator growth hook returned a block smaller than {bytes} bytes"
                ),
            );
        }
        self.memory.store_bytes(grown + 16, &saved)?;
        Ok(grown)
    }

    /// `kush_alloc_context_release`: drop one reference; the last drops the
    /// state value and frees it and the context.
    pub(super) fn context_release(&mut self, context: i64) -> Run<()> {
        if context == 0 {
            return Ok(());
        }
        let [references, state, spec] = self.memory.load(context, 3)?[..] else {
            unreachable!("three words")
        };
        if references <= 0 {
            return fault("an allocator context released more often than it is held");
        }
        if references > 1 {
            return self.memory.store(context, &[references - 1]);
        }
        let state_ty = self.program.allocator_contexts[spec as usize].state;
        let value = self.memory.load(state, self.width(state_ty))?;
        self.drop_value(state_ty, &value)?;
        self.memory.free(state)?;
        self.memory.free(context)
    }

    /// `kush_alloc_box_release`: the block back to its allocator, the
    /// context reference, then the box.
    pub(super) fn alloc_box_release(&mut self, handle: i64) -> Run<()> {
        let [alloc, free, context, block] = self.memory.load(handle, 4)?[..] else {
            unreachable!("four words")
        };
        let binding = Binding {
            alloc,
            free,
            realloc: 0,
            context,
        };
        self.block_release(binding, block)?;
        self.context_release(context)?;
        self.memory.free(handle)
    }

    /// `kush_alloc_vec_release`: the vector's block and context, then it.
    pub(super) fn alloc_vec_release(&mut self, handle: i64) -> Run<()> {
        let fields = self.memory.load(handle, 8)?;
        let binding = Binding::of_vec(&fields);
        self.block_release(binding, fields[7])?;
        self.context_release(binding.context)?;
        self.memory.free(handle)
    }

    pub(super) fn alloc_vec_call(
        &mut self,
        op: crate::executable::AllocVecOp,
        element: Type,
        values: &[i64],
        ty: Type,
        span: Span,
    ) -> Run<Words> {
        use crate::executable::AllocVecOp;
        let width = self.width(element);
        let stride = (width * 8) as i64;
        let handle = match op {
            AllocVecOp::Len | AllocVecOp::Get => self.memory.load(values[0], 1)?[0],
            _ => values[0],
        };
        let fields = self.memory.load(handle, 8)?;
        let (length, block) = (fields[0], fields[7]);
        let slot = |index: i64| block + 16 + index * stride;
        let index_of = |index: i64| (0..length).contains(&index).then_some(index);
        Ok(match op {
            AllocVecOp::Len => vec![length],
            AllocVecOp::Get => {
                let Some(index) = index_of(values[1]) else {
                    return panic_at(span, "panic: AllocVec index out of bounds");
                };
                self.memory.load(slot(index), width)?
            }
            AllocVecOp::Set => {
                let Some(index) = index_of(values[1]) else {
                    return panic_at(span, "panic: AllocVec index out of bounds");
                };
                let old = self.memory.load(slot(index), width)?;
                self.memory.store(slot(index), &values[2..2 + width])?;
                self.drop_value(element, &old)?;
                vec![handle]
            }
            AllocVecOp::Push | AllocVecOp::TryPush => {
                let item = &values[1..1 + width];
                let try_push = matches!(op, AllocVecOp::TryPush);
                if length == fields[1] && !self.alloc_vec_grow(handle, try_push, span)? {
                    let Some(shape) = ty.layout().and_then(|id| self.program.enums[id].result)
                    else {
                        return fault("AllocVec.try_push without a Result");
                    };
                    // The vector and the element come back, as a pair.
                    let mut payload = vec![0, handle];
                    payload.extend_from_slice(item);
                    return Ok(self.try_words(ty, shape, false, &payload));
                }
                let block = self.memory.load(handle + 56, 1)?[0];
                self.memory.store(block + 16 + length * stride, item)?;
                self.memory.store(handle, &[length + 1])?;
                match op {
                    AllocVecOp::TryPush => {
                        let Some(shape) = ty.layout().and_then(|id| self.program.enums[id].result)
                        else {
                            return fault("AllocVec.try_push without a Result");
                        };
                        self.try_words(ty, shape, true, &[handle])
                    }
                    _ => vec![handle],
                }
            }
            AllocVecOp::Pop => {
                if length == 0 {
                    return panic_at(span, "panic: AllocVec is empty");
                }
                let item = self.memory.load(slot(length - 1), width)?;
                self.memory.store(handle, &[length - 1])?;
                let mut out = vec![0, handle];
                out.extend(item);
                out
            }
            AllocVecOp::Clear => {
                for index in (0..length).rev() {
                    let item = self.memory.load(slot(index), width)?;
                    self.drop_value(element, &item)?;
                }
                self.memory.store(handle, &[0])?;
                vec![handle]
            }
        })
    }

    /// Double a full allocator vector's capacity: through its growth hook
    /// when it has one and a block, else into a fresh block (always fresh
    /// for a fallible push). `false` when a fallible push was refused.
    fn alloc_vec_grow(&mut self, handle: i64, fallible: bool, span: Span) -> Run<bool> {
        let fields = self.memory.load(handle, 8)?;
        let [length, capacity, width, .., block] = fields[..] else {
            unreachable!("eight words")
        };
        let binding = Binding::of_vec(&fields);
        let next = if capacity == 0 { 4 } else { capacity * 2 };
        let Some(bytes) = next
            .checked_mul(width * 8)
            .filter(|bytes| *bytes <= i64::MAX - 16)
        else {
            return panic_at(span, "panic: AllocVec capacity overflow");
        };
        let live = length * width * 8;
        let can_grow = block != 0 && (binding.context != 0 || binding.realloc != 0);
        let grown = if can_grow && !fallible {
            self.block_grow(binding, block, live, bytes, span)?
        } else {
            let Some(fresh) = self.block_alloc(binding, bytes)? else {
                if fallible {
                    return Ok(false);
                }
                return panic_at(
                    span,
                    &format!("panic: allocator refused a {bytes}-byte block"),
                );
            };
            if live != 0 {
                let data = self.memory.load_bytes(block + 16, live as usize)?;
                self.memory.store_bytes(fresh + 16, &data)?;
            }
            self.block_release(binding, block)?;
            fresh
        };
        self.memory.store(handle + 8, &[next])?;
        self.memory.store(handle + 56, &[grown])?;
        self.memory.stats.buffer_growths += 1;
        Ok(true)
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
        let chosen = no_unwind(
            self.call_nested(function, vec![vec![need], vec![current]]),
            "an arena strategy",
        )?[0];
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
