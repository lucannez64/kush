//! Byte buffers, vectors, text and views on the machine
//! (FND-EVAL-BUFFERS), with native's layouts:
//!
//! - `Bytes` and `String` are a handle to `[length, capacity, bytes...]`
//!   (`KushBytes`); a vector is a handle to `[length, capacity, elements...]`
//!   (`KushVec`), each element `width` words.
//! - A view (`&[T]`, `&str`) is the four words `[data, length, stride,
//!   byte flag]`: the stride is in bytes, and the flag marks a view over a
//!   byte buffer, whose elements are single bytes.
//! - A runtime-length inline array is `[length, slots...]`.
//!
//! Growth follows kush.c: a buffer's allocation has the size class the
//! runtime would give it, and growth that fits it keeps the allocation.

use super::*;
use crate::executable::{BytesOp, DynArrayOp, SliceOp, StrOp, StringOp, VecOp};

/// The evaluator's storage limits: past them a run ends with "budget
/// exhausted" (native code has no such limit).
const BYTES_LIMIT: usize = 16 * 1024 * 1024;
const VEC_LIMIT: usize = 1 << 20;

/// A view's descriptor words.
#[derive(Clone, Copy)]
struct View {
    data: i64,
    length: i64,
    stride: i64,
    bytes: bool,
}

impl View {
    fn of(words: &[i64]) -> Self {
        View {
            data: words[0],
            length: words[1],
            stride: words[2],
            bytes: words[3] != 0,
        }
    }
    fn words(self) -> Words {
        vec![self.data, self.length, self.stride, i64::from(self.bytes)]
    }
}

/// The index when it is in `0..length`.
fn within(index: i64, length: i64) -> Option<i64> {
    (0..length).contains(&index).then_some(index)
}

impl Machine<'_, '_> {
    // ---- buffers -----------------------------------------------------------

    /// A new buffer of `bytes` bytes with its header `[0, capacity]`.
    fn new_buffer(&mut self, bytes: usize, capacity: i64) -> Run<i64> {
        let handle = self.memory.allocate_buffer(bytes);
        self.memory.store(handle, &[0, capacity])?;
        Ok(handle)
    }
    pub(super) fn header(&self, handle: i64) -> Run<(i64, i64)> {
        let words = self.memory.load(handle, 2)?;
        Ok((words[0], words[1]))
    }
    /// A new `Bytes` holding a copy of `data` (`kush_bytes_from`).
    pub(super) fn bytes_from(&mut self, data: &[u8]) -> Run<i64> {
        let handle = self.new_buffer(16 + data.len(), data.len() as i64)?;
        self.memory.store_bytes(handle + 16, data)?;
        self.memory.store(handle, &[data.len() as i64])?;
        Ok(handle)
    }
    /// The bytes of a `Bytes` or `String` handle.
    pub(super) fn buffer_data(&self, handle: i64) -> Run<Vec<u8>> {
        let (length, _) = self.header(handle)?;
        self.memory.load_bytes(handle + 16, length as usize)
    }

    pub(super) fn bytes_call(&mut self, op: BytesOp, values: &[i64], span: Span) -> Run<Words> {
        let handle = if op.borrowed() {
            self.memory.load(values[0], 1)?[0]
        } else {
            values[0]
        };
        Ok(vec![match op {
            BytesOp::WithCapacity => {
                let Ok(capacity) = usize::try_from(values[0]) else {
                    return panic_at(span, "panic: negative byte buffer capacity");
                };
                if capacity > BYTES_LIMIT {
                    return panic_at(
                        span,
                        "reference byte-buffer capacity budget exhausted (16 MiB)",
                    );
                }
                self.new_buffer(16 + capacity, capacity as i64)?
            }
            BytesOp::Len => self.header(handle)?.0,
            BytesOp::Capacity => self.header(handle)?.1,
            BytesOp::Get => {
                let (length, _) = self.header(handle)?;
                let Some(index) = within(values[1], length) else {
                    return panic_at(span, "panic: byte buffer index out of bounds");
                };
                i64::from(self.memory.load_bytes(handle + 16 + index, 1)?[0])
            }
            BytesOp::Copy => {
                let data = self.buffer_data(handle)?;
                self.bytes_from(&data)?
            }
            BytesOp::Clear => {
                self.memory.store(handle, &[0])?;
                handle
            }
            BytesOp::Push | BytesOp::PushReserved => {
                // The buffer was moved into the push: a failing push frees it.
                let Ok(byte) = u8::try_from(values[1]) else {
                    self.memory.free(handle)?;
                    return panic_at(span, "panic: byte value must be in 0..255");
                };
                let (length, capacity) = self.header(handle)?;
                let mut handle = handle;
                if length == capacity {
                    if op == BytesOp::PushReserved {
                        self.memory.free(handle)?;
                        return panic_at(span, "panic: reserved byte buffer is full");
                    }
                    let next = if capacity == 0 { 8 } else { capacity * 2 };
                    if next as usize > BYTES_LIMIT {
                        return panic_at(
                            span,
                            "reference byte-buffer capacity budget exhausted (16 MiB)",
                        );
                    }
                    handle = self.memory.grow(handle, 16 + next as usize, false)?;
                    self.memory.store(handle + 8, &[next])?;
                    self.memory.stats.buffer_growths += 1;
                }
                self.memory.store_bytes(handle + 16 + length, &[byte])?;
                self.memory.store(handle, &[length + 1])?;
                handle
            }
        }])
    }

    pub(super) fn string_call(
        &mut self,
        op: StringOp,
        values: &[i64],
        ty: Type,
        span: Span,
    ) -> Run<Words> {
        let handle = if op.borrowed() {
            self.memory.load(values[0], 1)?[0]
        } else {
            values[0]
        };
        Ok(match op {
            StringOp::Len => vec![self.header(handle)?.0],
            StringOp::ScalarLen => {
                let data = self.buffer_data(handle)?;
                vec![scalar_count(&data)]
            }
            StringOp::ByteAt => {
                let (length, _) = self.header(handle)?;
                let Some(index) = within(values[1], length) else {
                    return panic_at(span, "panic: string byte index out of bounds");
                };
                vec![i64::from(
                    self.memory.load_bytes(handle + 16 + index, 1)?[0],
                )]
            }
            StringOp::ScalarAt { some_tag, none_tag } => {
                let data = self.buffer_data(handle)?;
                self.optional(ty, scalar_at(&data, values[1]), some_tag, none_tag)
            }
            StringOp::FromUtf8 { ok_tag, err_tag } => {
                let valid = std::str::from_utf8(&self.buffer_data(handle)?).is_ok();
                let tag = if valid { ok_tag } else { err_tag };
                fit(vec![tag as i64, handle], self.width(ty))
            }
            StringOp::AsBytes => {
                let data = self.buffer_data(handle)?;
                vec![self.bytes_from(&data)?]
            }
            StringOp::IntoBytes => vec![handle],
        })
    }

    /// `Some(code)` or `None` of an `Option<Char>` result.
    pub(super) fn optional(&self, ty: Type, code: Option<i64>, some: usize, none: usize) -> Words {
        match code {
            Some(code) => self.encode_variant(ty, some, vec![code]),
            None => self.encode_variant(ty, none, Vec::new()),
        }
    }

    pub(super) fn str_call(
        &mut self,
        op: StrOp,
        values: &[i64],
        ty: Type,
        span: Span,
    ) -> Run<Words> {
        let (data, length) = (values[0], values[1]);
        let text = self.memory.load_bytes(data, length as usize)?;
        Ok(match op {
            StrOp::Len => vec![length],
            StrOp::ScalarLen => vec![scalar_count(&text)],
            StrOp::ByteAt => {
                let Some(index) = within(values[4], length) else {
                    return panic_at(span, "panic: text byte index out of bounds");
                };
                vec![i64::from(text[index as usize])]
            }
            StrOp::ScalarAt { some_tag, none_tag } => {
                self.optional(ty, scalar_at(&text, values[4]), some_tag, none_tag)
            }
            StrOp::ToString => vec![self.bytes_from(&text)?],
            StrOp::AsciiUpper | StrOp::AsciiLower => {
                let mut text = text;
                if op == StrOp::AsciiUpper {
                    text.make_ascii_uppercase();
                } else {
                    text.make_ascii_lowercase();
                }
                self.memory.store_bytes(data, &text)?;
                vec![0]
            }
            StrOp::SetScalar => {
                let Some(index) = usize::try_from(values[4])
                    .ok()
                    .filter(|index| *index < text.len() && text[*index] & 0xC0 != 0x80)
                else {
                    return panic_at(
                        span,
                        "panic: Str.set_scalar offset is not a scalar boundary inside the view",
                    );
                };
                let Some(scalar) = u32::try_from(values[5]).ok().and_then(char::from_u32) else {
                    return fault("Str.set_scalar of an invalid Char");
                };
                let Some(old) = std::str::from_utf8(&text[index..])
                    .ok()
                    .and_then(|rest| rest.chars().next())
                else {
                    return fault("Str.set_scalar on invalid text");
                };
                if old.len_utf8() != scalar.len_utf8() {
                    return panic_at(
                        span,
                        "panic: Str.set_scalar needs a scalar with the same UTF-8 width as the one it replaces",
                    );
                }
                let mut encoded = [0; 4];
                let encoded = scalar.encode_utf8(&mut encoded);
                self.memory
                    .store_bytes(data + index as i64, encoded.as_bytes())?;
                vec![0]
            }
        })
    }

    // ---- vectors -----------------------------------------------------------

    pub(super) fn vec_call(
        &mut self,
        op: VecOp,
        element: Type,
        values: &[i64],
        ty: Type,
        span: Span,
    ) -> Run<Words> {
        let width = self.width(element);
        let stride = (width * 8) as i64;
        let slot = |handle: i64, index: i64| handle + 16 + index * stride;
        let borrowed = |machine: &Self| machine.memory.load(values[0], 1).map(|words| words[0]);
        Ok(match op {
            VecOp::WithCapacity => {
                let Ok(capacity) = usize::try_from(values[0]) else {
                    return panic_at(span, "panic: negative vector capacity");
                };
                if capacity > VEC_LIMIT {
                    return panic_at(
                        span,
                        "reference vector capacity budget exhausted (1Mi elements)",
                    );
                }
                vec![self.new_buffer(16 + capacity * width * 8, capacity as i64)?]
            }
            VecOp::Len => vec![self.header(borrowed(self)?)?.0],
            VecOp::Get | VecOp::At => {
                let handle = borrowed(self)?;
                let (length, _) = self.header(handle)?;
                let Some(index) = within(values[1], length) else {
                    return panic_at(span, "panic: vector index out of bounds");
                };
                self.memory.load(slot(handle, index), width)?
            }
            VecOp::Push => vec![self.vec_push(values[0], &values[1..1 + width], span)?],
            VecOp::PushBorrowed => {
                let handle = borrowed(self)?;
                let grown = self.vec_push(handle, &values[1..1 + width], span)?;
                self.memory.store(values[0], &[grown])?;
                vec![0]
            }
            VecOp::Set | VecOp::SetBorrowed | VecOp::SetProved => {
                let handle = if op == VecOp::Set {
                    values[0]
                } else {
                    borrowed(self)?
                };
                let (length, _) = self.header(handle)?;
                let Some(index) = within(values[1], length) else {
                    return panic_at(span, "panic: vector index out of bounds");
                };
                let old = self.memory.load(slot(handle, index), width)?;
                self.memory
                    .store(slot(handle, index), &values[2..2 + width])?;
                self.drop_value(element, &old)?;
                vec![if op == VecOp::Set { handle } else { 0 }]
            }
            VecOp::Clear | VecOp::ClearBorrowed => {
                let handle = if op == VecOp::Clear {
                    values[0]
                } else {
                    borrowed(self)?
                };
                let (length, _) = self.header(handle)?;
                for index in (0..length).rev() {
                    let item = self.memory.load(slot(handle, index), width)?;
                    self.drop_value(element, &item)?;
                }
                self.memory.store(handle, &[0])?;
                vec![if op == VecOp::Clear { handle } else { 0 }]
            }
            VecOp::Reserve | VecOp::ReserveBorrowed => {
                let handle = if op == VecOp::Reserve {
                    values[0]
                } else {
                    borrowed(self)?
                };
                let Ok(additional) = usize::try_from(values[1]) else {
                    return panic_at(span, "panic: negative vector reserve");
                };
                let (length, capacity) = self.header(handle)?;
                let Some(needed) = (length as usize).checked_add(additional) else {
                    return panic_at(span, "panic: vector reserve length overflow");
                };
                if needed > VEC_LIMIT {
                    return panic_at(
                        span,
                        "reference vector capacity budget exhausted (1Mi elements)",
                    );
                }
                let mut grown = handle;
                if needed as i64 > capacity {
                    grown = self.memory.grow(handle, 16 + needed * width * 8, false)?;
                    self.memory.store(grown + 8, &[needed as i64])?;
                    self.memory.stats.buffer_growths += 1;
                }
                if op == VecOp::Reserve {
                    vec![grown]
                } else {
                    self.memory.store(values[0], &[grown])?;
                    vec![0]
                }
            }
            VecOp::TryReserve { ok_tag, err_tag } => {
                // A request within the limits succeeds when it fits the
                // capacity or the allocation, or the allocation budget allows
                // a growth.
                let handle = values[0];
                let (length, capacity) = self.header(handle)?;
                let usable = self.memory.size(handle)?;
                let request = usize::try_from(values[1])
                    .ok()
                    .and_then(|additional| (length as usize).checked_add(additional))
                    .filter(|needed| *needed <= VEC_LIMIT)
                    .and_then(|needed| {
                        needed
                            .checked_mul(width * 8)
                            .and_then(|bytes| bytes.checked_add(16))
                            .filter(|bytes| *bytes <= i64::MAX as usize)
                            .map(|bytes| (needed, bytes))
                    });
                let success = request.is_some_and(|(needed, bytes)| {
                    needed as i64 <= capacity || bytes <= usable || self.try_charge()
                });
                let mut owner = handle;
                if success
                    && let Some((needed, bytes)) = request
                    && needed as i64 > capacity
                {
                    owner = self.memory.grow(handle, bytes, true)?;
                    self.memory.store(owner + 8, &[needed as i64])?;
                    self.memory.stats.buffer_growths += 1;
                }
                let tag = if success { ok_tag } else { err_tag };
                fit(vec![tag as i64, owner], self.width(ty))
            }
            VecOp::ReplaceBorrowed => {
                let old = borrowed(self)?;
                self.memory.store(values[0], &[values[1]])?;
                vec![old]
            }
        })
    }

    /// `kush_vec_push`: append an item, doubling the capacity when full.
    fn vec_push(&mut self, handle: i64, item: &[i64], span: Span) -> Run<i64> {
        let (length, capacity) = self.header(handle)?;
        let stride = (item.len() * 8) as i64;
        let mut handle = handle;
        if length == capacity {
            let next = if capacity == 0 { 4 } else { capacity * 2 };
            if next as usize > VEC_LIMIT {
                return panic_at(
                    span,
                    "reference vector capacity budget exhausted (1Mi elements)",
                );
            }
            handle = self
                .memory
                .grow(handle, 16 + next as usize * item.len() * 8, false)?;
            self.memory.store(handle + 8, &[next])?;
            self.memory.stats.buffer_growths += 1;
        }
        self.memory.store(handle + 16 + length * stride, item)?;
        self.memory.store(handle, &[length + 1])?;
        Ok(handle)
    }

    /// `Vec.map` in place (native's `vec_map`): restride once when the
    /// elements widen or narrow, then apply the callbacks to each element.
    /// The callbacks run as frames on the stack, one at a time.
    pub(super) fn vec_map(&mut self, op: &MapOp, handle: i64, callbacks: Vec<i64>) -> Run<Flow> {
        let source = self.width(op.source);
        let target = self.width(op.target);
        let mut handle = handle;
        let stride = if op.grow {
            let (length, capacity) = self.header(handle)?;
            let grown = self
                .memory
                .grow(handle, 16 + capacity as usize * target * 8, false)?;
            if grown != handle {
                self.memory.stats.buffer_growths += 1;
            }
            handle = grown;
            if source != target {
                let at = |index: i64, width: usize| handle + 16 + index * (width * 8) as i64;
                let indices: Box<dyn Iterator<Item = i64>> = if target > source {
                    Box::new((0..length).rev())
                } else {
                    Box::new(0..length)
                };
                for index in indices {
                    let words = self.memory.load(at(index, source), source)?;
                    self.memory.store(at(index, target), &words)?;
                }
            }
            target
        } else {
            source
        };
        let (length, _) = self.header(handle)?;
        map_step(
            self,
            Mapping {
                handle,
                length,
                index: 0,
                pending: false,
                callback: 0,
                callbacks,
                current: Vec::new(),
                source,
                stride,
                target,
            },
        )
    }

    // ---- views -------------------------------------------------------------

    /// One element of a view: its words, or a byte of a byte-backed view.
    fn view_element(&self, view: View, index: i64, width: usize) -> Run<Words> {
        let address = view.data + index * view.stride;
        if width == 1 && view.bytes {
            return Ok(vec![i64::from(self.memory.load_bytes(address, 1)?[0])]);
        }
        self.memory.load(address, width)
    }

    pub(super) fn slice_call(
        &mut self,
        op: SliceOp,
        element: Type,
        values: &[i64],
        span: Span,
    ) -> Run<Words> {
        let view = View::of(values);
        let width = self.width(element);
        if op == SliceOp::Len {
            return Ok(vec![view.length]);
        }
        let index = values[4];
        if let SliceOp::TryGet {
            some_tag,
            none_tag,
            option,
        } = op
        {
            let option = Type::Enum(option);
            return Ok(match within(index, view.length) {
                Some(index) => {
                    let payload = self.view_element(view, index, width)?;
                    self.encode_variant(option, some_tag, payload)
                }
                None => self.encode_variant(option, none_tag, Vec::new()),
            });
        }
        let checked = op != SliceOp::At;
        let Some(index) = (if checked {
            within(index, view.length)
        } else {
            (index >= 0).then_some(index)
        }) else {
            return panic_at(span, "panic: slice index out of bounds");
        };
        let address = view.data + index * view.stride;
        Ok(match op {
            SliceOp::Get | SliceOp::At => self.view_element(view, index, width)?,
            SliceOp::Set => {
                if width == 1 && view.bytes {
                    let Ok(byte) = u8::try_from(values[5]) else {
                        return panic_at(span, "panic: byte value out of range");
                    };
                    self.memory.store_bytes(address, &[byte])?;
                } else {
                    self.memory.store(address, &values[5..5 + width])?;
                }
                vec![0]
            }
            // One thread runs at a time on the machine, so an atomic
            // operation is a plain access.
            SliceOp::AtomicLoad => self.memory.load(address, 1)?,
            SliceOp::AtomicStore => {
                self.memory.store(address, &[values[5]])?;
                vec![0]
            }
            SliceOp::AtomicFetchAdd | SliceOp::AtomicSwap => {
                let old = self.memory.load(address, 1)?[0];
                let new = if op == SliceOp::AtomicSwap {
                    values[5]
                } else {
                    old.wrapping_add(values[5])
                };
                self.memory.store(address, &[new])?;
                vec![old]
            }
            SliceOp::AtomicCompareExchange => {
                let old = self.memory.load(address, 1)?[0];
                let hit = old == values[5];
                if hit {
                    self.memory.store(address, &[values[6]])?;
                }
                vec![i64::from(hit)]
            }
            SliceOp::ChannelSend | SliceOp::ChannelRecv { .. } | SliceOp::ChannelClose => {
                return unsupported("a channel operation");
            }
            SliceOp::Len | SliceOp::TryGet { .. } => unreachable!("handled above"),
        })
    }

    pub(super) fn dyn_array_call(
        &mut self,
        op: DynArrayOp,
        element: Type,
        values: &[i64],
        span: Span,
    ) -> Run<Words> {
        let pointer = values[0];
        let length = self.memory.load(pointer, 1)?[0];
        Ok(match op {
            DynArrayOp::Len => vec![length],
            DynArrayOp::Get => {
                let Some(index) = within(values[1], length) else {
                    return panic_at(span, "panic: DynArray index out of bounds");
                };
                let width = self.width(element);
                self.memory
                    .load(pointer + 8 + index * (width * 8) as i64, width)?
            }
        })
    }

    /// A view rvalue (native's `view_source` and `finish_view`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn view(
        &mut self,
        body: &Body,
        source: ViewSource,
        start: Option<Operand>,
        end: Option<Operand>,
        element: Type,
        check: bool,
        text: bool,
        span: Span,
    ) -> Run<Words> {
        let base_ty = source.ty(body);
        let stride = (self.width(element) * 8) as i64;
        let array_length = |machine: &Self| {
            base_ty
                .layout()
                .and_then(|id| machine.program.enums[id].array)
                .map(|(_, length)| length as i64)
        };
        let base = match source {
            ViewSource::DynArray(place) => {
                let location = self.address(place)?;
                View {
                    data: location + 8,
                    length: self.memory.load(location, 1)?[0],
                    stride,
                    bytes: false,
                }
            }
            ViewSource::Array(local) => {
                let Some(length) = array_length(self) else {
                    return fault("a view of a local that is not an array");
                };
                View {
                    data: self.address(Place::local(local))? + 8,
                    length,
                    stride,
                    bytes: false,
                }
            }
            ViewSource::Value(operand) => {
                let values = self.operand(operand)?;
                if let Some(length) = array_length(self) {
                    // An array value has no address: the view looks at a
                    // copy that lives as long as the frame.
                    let copy = self.memory.allocate(values.len().max(1) * 8, false);
                    self.memory.store(copy, &values)?;
                    self.stack
                        .last_mut()
                        .expect("a frame")
                        .temporaries
                        .push(copy);
                    View {
                        data: copy + 8,
                        length,
                        stride,
                        bytes: false,
                    }
                } else {
                    match base_ty {
                        Type::Ref(pointee) | Type::RefMut(pointee) => {
                            let handle = self.memory.load(values[0], 1)?[0];
                            let length = self.header(handle)?.0;
                            let bytes = matches!(
                                self.program.pointees[pointee],
                                Type::Bytes | Type::String
                            );
                            View {
                                data: handle + 16,
                                length,
                                stride: if bytes { 1 } else { stride },
                                bytes,
                            }
                        }
                        _ => View::of(&values),
                    }
                }
            }
        };
        let start = match start {
            Some(start) => self.scalar(start)?,
            None => 0,
        };
        let end = match end {
            Some(end) => self.scalar(end)?,
            None => base.length,
        };
        if start < 0 || end < 0 || (check && (start > end || end > base.length)) {
            return panic_at(span, "panic: slice range out of bounds");
        }
        if text && check {
            let data = self.memory.load_bytes(base.data, base.length as usize)?;
            let boundary = |index: i64| index == base.length || data[index as usize] & 0xC0 != 0x80;
            if !boundary(start) || !boundary(end) {
                return panic_at(
                    span,
                    "panic: text range is not on Unicode scalar boundaries",
                );
            }
        }
        let (stride, bytes) = if text {
            (1, true)
        } else {
            (base.stride, base.bytes)
        };
        Ok(View {
            data: base.data + start * stride,
            length: end - start,
            stride,
            bytes,
        }
        .words())
    }

    /// The address of an element after its bound check.
    pub(super) fn element_address(
        &mut self,
        body: &Body,
        base: ElementBase,
        index: Operand,
        span: Span,
    ) -> Run<i64> {
        let index = self.scalar(index)?;
        match base {
            ElementBase::Slice(view) => {
                let view = View::of(&self.operand(view)?);
                if within(index, view.length).is_none() {
                    return panic_at(span, "panic: slice index out of bounds");
                }
                if view.bytes {
                    return panic_at(
                        span,
                        "panic: a byte-backed slice element has no word-sized address",
                    );
                }
                Ok(view.data + index * view.stride)
            }
            ElementBase::Stored(place) => {
                let ty = body.place_ty(place);
                if let Type::Vec(element) = ty {
                    let handle = self.read(place)?[0];
                    let (length, _) = self.header(handle)?;
                    if within(index, length).is_none() {
                        return panic_at(span, "panic: index out of bounds");
                    }
                    let width = self.width(self.program.pointees[element]);
                    return Ok(handle + 16 + index * (width * 8) as i64);
                }
                let Some((element, length)) =
                    ty.layout().and_then(|id| self.program.enums[id].array)
                else {
                    return fault("an element address of a non-array place");
                };
                if within(index, length as i64).is_none() {
                    return panic_at(span, "panic: index out of bounds");
                }
                let stride = (self.width(element) * 8) as i64;
                Ok(self.address(place)? + 8 + index * stride)
            }
        }
    }

    // ---- runtime-length inline arrays -----------------------------------

    pub(super) fn array_op(&mut self, op: ArrayOp, words: &[Words], span: Span) -> Run<Words> {
        Ok(match op {
            ArrayOp::New { element, capacity } => vec![0; 1 + self.width(element) * capacity],
            ArrayOp::Push { element, capacity } => {
                let width = self.width(element);
                let mut array = words[0].clone();
                let length = array[0];
                if length < 0 || length as usize >= capacity {
                    return panic_at(span, "panic: DynArray capacity exceeded");
                }
                let start = 1 + length as usize * width;
                array[start..start + width].copy_from_slice(&words[1][..width]);
                array[0] = length + 1;
                array
            }
            ArrayOp::Fill { element, capacity } => {
                let width = self.width(element);
                let length = words[0][0];
                if length < 0 || length as usize > capacity {
                    return panic_at(
                        span,
                        "panic: runtime array length out of range for its capacity",
                    );
                }
                let mut array = vec![0; 1 + width * capacity];
                array[0] = length;
                for slot in 0..length as usize {
                    let start = 1 + slot * width;
                    array[start..start + width].copy_from_slice(&words[1][..width]);
                }
                array
            }
            ArrayOp::Set { element, .. } => {
                let width = self.width(element);
                let mut array = words[0].clone();
                let Some(position) = within(words[1][0], array[0]) else {
                    return panic_at(span, "panic: DynArray index out of bounds");
                };
                let start = 1 + position as usize * width;
                array[start..start + width].copy_from_slice(&words[2][..width]);
                array
            }
            ArrayOp::Pop { element, .. } => {
                let width = self.width(element);
                let mut array = words[0].clone();
                if array[0] <= 0 {
                    return panic_at(span, "panic: DynArray is empty");
                }
                let next = array[0] - 1;
                array[0] = next;
                let start = 1 + next as usize * width;
                let item = array[start..start + width].to_vec();
                array[start..start + width].fill(0);
                // The tuple `(array, element)`, after its constructor tag.
                let mut out = vec![0];
                out.extend(array);
                out.extend(item);
                out
            }
            ArrayOp::Equal {
                element,
                capacity,
                negate,
            } => {
                let width = self.width(element);
                let (left, right) = (&words[0], &words[1]);
                let mut equal = left[0] == right[0];
                for slot in 0..capacity {
                    if !equal || left[0] <= slot as i64 {
                        break;
                    }
                    for word in 0..width {
                        let (a, b) = (
                            left[1 + slot * width + word],
                            right[1 + slot * width + word],
                        );
                        let same = match element.float_kind() {
                            Some(kind) => {
                                crate::float::compare(kind, &crate::lexer::Kind::EqEq, a, b)
                            }
                            None => a == b,
                        };
                        equal &= same;
                    }
                }
                vec![i64::from(equal != negate)]
            }
            ArrayOp::Suffix {
                element,
                suffix,
                index,
                ..
            } => {
                let width = self.width(element);
                let slot = (words[0][0] - suffix as i64 + index as i64) as usize;
                words[0][1 + slot * width..1 + (slot + 1) * width].to_vec()
            }
            ArrayOp::Rest {
                element,
                capacity,
                prefix,
                suffix,
            } => {
                let width = self.width(element);
                let length = words[0][0];
                let mut tail = vec![0; 1 + width * capacity];
                tail[0] = length - (prefix + suffix) as i64;
                for position in 0..capacity.saturating_sub(prefix + suffix) {
                    let source = prefix + position;
                    if length > (source + suffix) as i64 {
                        tail[1 + position * width..1 + (position + 1) * width].copy_from_slice(
                            &words[0][1 + source * width..1 + (source + 1) * width],
                        );
                    }
                }
                tail
            }
            ArrayOp::SuffixAddress {
                element,
                suffix,
                index,
            } => {
                let pointer = words[0][0];
                let length = self.memory.load(pointer, 1)?[0];
                let stride = (self.width(element) * 8) as i64;
                vec![pointer + 8 + (length + index as i64 - suffix as i64) * stride]
            }
            ArrayOp::RestView {
                element,
                prefix,
                suffix,
            } => {
                let pointer = words[0][0];
                let length = self.memory.load(pointer, 1)?[0];
                let stride = (self.width(element) * 8) as i64;
                View {
                    data: pointer + 8 + prefix as i64 * stride,
                    length: length - (prefix + suffix) as i64,
                    stride,
                    bytes: false,
                }
                .words()
            }
        })
    }
}

/// The number of Unicode scalars in UTF-8 text.
fn scalar_count(data: &[u8]) -> i64 {
    data.iter().filter(|byte| **byte & 0xC0 != 0x80).count() as i64
}

/// The code point of scalar `index` of UTF-8 text.
fn scalar_at(data: &[u8], index: i64) -> Option<i64> {
    let index = usize::try_from(index).ok()?;
    let text = std::str::from_utf8(data).ok()?;
    text.chars().nth(index).map(|ch| i64::from(u32::from(ch)))
}

// ---- standard I/O ----------------------------------------------------------

/// Linux errno values the I/O builtins report.
const EIO: i64 = 5;
const EFBIG: i64 = 27;

fn io_error_code(error: &std::io::Error) -> i64 {
    error
        .raw_os_error()
        .filter(|code| *code > 0)
        .map_or(EIO, i64::from)
}

impl Machine<'_, '_> {
    /// One read or write attempt costs a step: a reader that keeps being
    /// interrupted exhausts the budget instead of looping forever.
    fn spend_io(&mut self) -> Run<()> {
        if self.fuel == 0 {
            return panic_at(
                Span::default(),
                "reference I/O computation budget exhausted",
            );
        }
        self.fuel -= 1;
        Ok(())
    }

    /// Standard input and output (native's `kush_io_*`, as the tree runs
    /// them): a read fills the owned buffer it consumes, without growing
    /// it, and frees it on failure; a write sends a borrowed buffer.
    pub(super) fn io_call(
        &mut self,
        op: crate::executable::IoOp,
        shape: Option<crate::runtime_types::ResultShape>,
        values: &[i64],
        ty: Type,
    ) -> Run<Words> {
        use crate::executable::IoOp;
        let (status, value) = match op {
            IoOp::Stdin => return Ok(vec![0]),
            IoOp::Stdout => return Ok(vec![1]),
            IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk => {
                let handle = values[1];
                let (length, capacity) = self.header(handle)?;
                let (mut length, capacity) = (length as usize, capacity as usize);
                let mut data = self.memory.load_bytes(handle + 16, capacity)?;
                let line = matches!(op, IoOp::ReadLine);
                let chunk = matches!(op, IoOp::ReadChunk);
                let mut probe = [0u8; 1];
                let status = loop {
                    self.spend_io()?;
                    let full = length == capacity;
                    if full && chunk {
                        break EFBIG;
                    }
                    let target = if full {
                        &mut probe[..]
                    } else {
                        &mut data[length..if line { length + 1 } else { capacity }]
                    };
                    match self.input.read(target) {
                        Ok(0) => break 0,
                        Ok(_) if full => break EFBIG,
                        Ok(count) => {
                            length += count;
                            if chunk || (line && data[length - 1] == b'\n') {
                                break 0;
                            }
                        }
                        Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                        Err(error) => break io_error_code(&error),
                    }
                };
                if status == 0 {
                    self.memory.store_bytes(handle + 16, &data[..length])?;
                    self.memory.store(handle, &[length as i64])?;
                } else {
                    self.memory.free(handle)?;
                }
                (status, handle)
            }
            IoOp::Write => {
                let handle = self.memory.load(values[1], 1)?[0];
                let data = self.buffer_data(handle)?;
                let mut offset = 0;
                let status = loop {
                    if offset == data.len() {
                        break 0;
                    }
                    self.spend_io()?;
                    match self.output.write(&data[offset..]) {
                        Ok(0) => break EIO,
                        Ok(count) => offset += count,
                        Err(error) if error.kind() == std::io::ErrorKind::Interrupted => {}
                        Err(error) => break io_error_code(&error),
                    }
                };
                (status, 0)
            }
        };
        let Some(shape) = shape else {
            return fault("an I/O result without its shape");
        };
        let words = if status == 0 {
            vec![shape.ok_tag as i64, value]
        } else {
            vec![shape.err_tag as i64, status]
        };
        Ok(fit(words, self.width(ty)))
    }
}

/// Where a `Vec.map` is: with `pending`, element `index` is `current`,
/// about to go through callback `callback` (past the last one: stored).
struct Mapping {
    handle: i64,
    length: i64,
    index: i64,
    pending: bool,
    callback: usize,
    callbacks: Vec<i64>,
    current: Words,
    /// The elements' widths before and after, and the stride they are
    /// read at, in words.
    source: usize,
    stride: usize,
    target: usize,
}

/// Run a `Vec.map` until its next callback call, or to its end.
fn map_step(machine: &mut Machine<'_, '_>, mut state: Mapping) -> Run<Flow> {
    loop {
        if state.pending {
            if state.callback < state.callbacks.len() {
                let function = code_function(state.callbacks[state.callback])?;
                let args = vec![std::mem::take(&mut state.current)];
                return Ok(Flow::Call {
                    function,
                    args,
                    environment: None,
                    then: Some(Box::new(move |machine, result| {
                        state.current = result;
                        state.callback += 1;
                        map_step(machine, state)
                    })),
                    catch: None,
                });
            }
            let slot = state.handle + 16 + state.index * (state.target * 8) as i64;
            machine.memory.store(slot, &state.current)?;
            state.index += 1;
            state.pending = false;
        }
        if state.index >= state.length {
            return Ok(Flow::Done(vec![state.handle]));
        }
        let slot = state.handle + 16 + state.index * (state.stride * 8) as i64;
        state.current = machine.memory.load(slot, state.source)?;
        state.callback = 0;
        state.pending = true;
    }
}
