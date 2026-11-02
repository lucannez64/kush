//! Cranelift AOT code generation for the checked scalar IR. The C shim only
//! supplies process entry, standard-stream I/O, allocation, byte operations, and abort;
//! user functions are CLIF.
use crate::float::FloatKind;
use crate::grades::Grade;
use crate::int::IntKind;
use crate::{
    Diagnostic, Span,
    executable::{
        self as ex, AllocVecOp, BytesOp, Coercion, DynArrayOp, Executable, Expr, ExprKind, IoOp,
        Pattern, ReceiverMode, SliceOp, StrOp, StringOp, Target, Type, VecOp,
    },
    lexer::Kind,
};
use cranelift_codegen::{
    ir::{
        self, AbiParam, InstBuilder, TrapCode, Value, condcodes::FloatCC, condcodes::IntCC,
        types::I64,
    },
    settings::{self, Configurable},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

type Result<T> = std::result::Result<T, Diagnostic>;
fn error(message: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::new(Span::default(), message.to_string())
}
const RUNTIME: &str = r#"
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <signal.h>
#include <stdio.h>
#include <math.h>
#include <locale.h>
extern int64_t kush_entry(void);
_Noreturn void kush_panic(void) {
    static const char message[] = "panic: checked arithmetic, memory, or I/O failure\n";
    (void)write(2, message, sizeof(message) - 1);
    abort();
}
int64_t kush_print_i64(int64_t value) {
    char buffer[32];
    char *end = buffer + sizeof(buffer), *p = end;
    uint64_t magnitude = value < 0 ? UINT64_C(0) - (uint64_t)value : (uint64_t)value;
    *--p = '\n';
    do { *--p = (char)('0' + magnitude % 10); magnitude /= 10; } while (magnitude != 0);
    if (value < 0) *--p = '-';
    while (p < end) {
        ssize_t count = write(1, p, (size_t)(end - p));
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) kush_panic();
        p += count;
    }
    return 0;
}
int64_t kush_print_u64(uint64_t magnitude) {
    char buffer[32];
    char *end = buffer + sizeof(buffer), *p = end;
    *--p = '\n';
    do { *--p = (char)('0' + magnitude % 10); magnitude /= 10; } while (magnitude != 0);
    while (p < end) {
        ssize_t count = write(1, p, (size_t)(end - p));
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) kush_panic();
        p += count;
    }
    return 0;
}
/* ---- IEEE-754 helpers ----------------------------------------------------
   Float values cross the generated/native boundary as raw bits in one word:
   f64 uses all 64 bits and f32 uses the low 32 bits. The C side performs only
   the conversions that need careful range checks; arithmetic and comparisons
   are emitted directly as hardware instructions by Cranelift. */
static double kush_f64_of_bits(int64_t bits) {
    uint64_t raw = (uint64_t)bits; double value; memcpy(&value, &raw, sizeof(value)); return value;
}
static int64_t kush_bits_of_f64(double value) {
    uint64_t raw; int64_t bits; memcpy(&raw, &value, sizeof(raw)); memcpy(&bits, &raw, sizeof(bits)); return bits;
}
static float kush_f32_of_bits(int64_t bits) {
    uint32_t raw = (uint32_t)(uint64_t)bits; float value; memcpy(&value, &raw, sizeof(value)); return value;
}
int64_t kush_float_from_int(int64_t value, int64_t is_signed) {
    double result = is_signed ? (double)value : (double)(uint64_t)value;
    return kush_bits_of_f64(result);
}
int64_t kush_int_exact_in_float(int64_t value, int64_t is_signed, int64_t mantissa) {
    uint64_t magnitude = is_signed
        ? (value < 0 ? (uint64_t)0 - (uint64_t)value : (uint64_t)value)
        : (uint64_t)value;
    if (magnitude == 0) return 1;
    int bits = 64 - __builtin_clzll(magnitude);
    if ((uint64_t)bits <= (uint64_t)mantissa) return 1;
    return (int64_t)(__builtin_ctzll(magnitude) >= bits - (int)mantissa);
}
/* target: 0 i8, 1 i16, 2 i32, 3 i64, 4 u8, 5 u16, 6 u32, 7 u64 */
static int kush_float_int_bounds(int64_t target, double *low, double *high) {
    int signed_target = target < 4;
    int bits = 8 << (int)(target & 3);
    if (signed_target) {
        *low = -ldexp(1.0, bits - 1);
        *high = ldexp(1.0, bits - 1);
    } else {
        *low = 0.0;
        *high = ldexp(1.0, bits);
    }
    return signed_target;
}
int64_t kush_float_int_present(int64_t bits, int64_t target) {
    double value = kush_f64_of_bits(bits), low, high;
    if (!isfinite(value)) return 0;
    int signed_target = kush_float_int_bounds(target, &low, &high);
    double truncated = trunc(value);
    if (signed_target) return truncated >= low && truncated < high;
    return truncated >= 0.0 && truncated < high;
}
int64_t kush_float_to_int(int64_t bits, int64_t target) {
    if (!kush_float_int_present(bits, target)) return 0;
    double truncated = trunc(kush_f64_of_bits(bits));
    if (target < 4) return (int64_t)truncated;
    uint64_t raw = (uint64_t)truncated; int64_t result;
    memcpy(&result, &raw, sizeof(result)); return result;
}
int64_t kush_float_rem(int64_t left, int64_t right, int64_t is_f32) {
    if (is_f32) {
        float x = kush_f32_of_bits(left), y = kush_f32_of_bits(right);
        float result = fmodf(x, y);
        uint32_t raw; memcpy(&raw, &result, sizeof(raw)); return (int64_t)raw;
    }
    double result = fmod(kush_f64_of_bits(left), kush_f64_of_bits(right));
    return kush_bits_of_f64(result);
}
/* Convert the shortest `%e` spelling into plain decimal notation, matching
   Rust's `Display` for f32/f64. The caller has excluded zero and non-finite
   values. */
static void kush_plain_decimal(const char *scientific, char *out, size_t capacity) {
    char body[512];
    size_t used = 0;
    const char *p = scientific;
    if (*p == '-') { if (used + 1 < sizeof(body)) body[used++] = *p; ++p; }
    const char *exponent_at = strchr(p, 'e');
    int exponent = exponent_at ? (int)strtol(exponent_at + 1, NULL, 10) : 0;
    char digits[64];
    int count = 0;
    for (const char *q = p; q < exponent_at && count < (int)sizeof(digits); ++q) {
        if (*q >= '0' && *q <= '9') digits[count++] = *q;
    }
    int point = exponent + 1;
    if (point <= 0) {
        body[used++] = '0'; body[used++] = '.';
        for (int i = 0; i < -point && used + 1 < sizeof(body); ++i) body[used++] = '0';
        for (int i = 0; i < count && used + 1 < sizeof(body); ++i) body[used++] = digits[i];
    } else if (point >= count) {
        for (int i = 0; i < count && used + 1 < sizeof(body); ++i) body[used++] = digits[i];
        for (int i = 0; i < point - count && used + 1 < sizeof(body); ++i) body[used++] = '0';
    } else {
        for (int i = 0; i < point && used + 1 < sizeof(body); ++i) body[used++] = digits[i];
        if (used + 1 < sizeof(body)) body[used++] = '.';
        for (int i = point; i < count && used + 1 < sizeof(body); ++i) body[used++] = digits[i];
    }
    body[used] = 0;
    snprintf(out, capacity, "%s", body);
}
static void kush_format_float(double value, int is_f32, char *out, size_t capacity) {
    if (isnan(value)) { snprintf(out, capacity, "NaN"); return; }
    if (isinf(value)) { snprintf(out, capacity, value < 0.0 ? "-inf" : "inf"); return; }
    if (value == 0.0) { snprintf(out, capacity, signbit(value) ? "-0" : "0"); return; }
    int maximum = is_f32 ? 9 : 17;
    char candidate[64] = "";
    for (int digits = 1; digits <= maximum; ++digits) {
        snprintf(candidate, sizeof(candidate), "%.*e", digits - 1, value);
        if (is_f32) {
            float parsed = strtof(candidate, NULL);
            float original = (float)value;
            if (memcmp(&parsed, &original, sizeof(original)) == 0) break;
        } else {
            double parsed = strtod(candidate, NULL);
            if (memcmp(&parsed, &value, sizeof(value)) == 0) break;
        }
    }
    kush_plain_decimal(candidate, out, capacity);
}
static void kush_write_line(const char *text, size_t length) {
    size_t at = 0;
    while (at < length) {
        ssize_t count = write(1, text + at, length - at);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) kush_panic();
        at += (size_t)count;
    }
}
int64_t kush_print_f64(int64_t bits) {
    char line[512], decimal[512];
    kush_format_float(kush_f64_of_bits(bits), 0, decimal, sizeof(decimal));
    int length = snprintf(line, sizeof(line) - 1, "%s\n", decimal);
    if (length < 0) kush_panic();
    kush_write_line(line, (size_t)length);
    return 0;
}
int64_t kush_print_f32(int64_t bits) {
    char line[512], decimal[512];
    kush_format_float((double)kush_f32_of_bits(bits), 1, decimal, sizeof(decimal));
    int length = snprintf(line, sizeof(line) - 1, "%s\n", decimal);
    if (length < 0) kush_panic();
    kush_write_line(line, (size_t)length);
    return 0;
}
static uint64_t kush_live_allocations = 0;
static uint64_t kush_allocations = 0;
static uint64_t kush_deallocations = 0;
static uint64_t kush_peak_live = 0;
static uint64_t kush_buffer_growths = 0;
static uint64_t kush_reuses = 0;
static void kush_note_allocation(void) {
    ++kush_live_allocations; ++kush_allocations;
    if (kush_live_allocations > kush_peak_live) kush_peak_live = kush_live_allocations;
}
static void kush_note_deallocation(void) {
    if (kush_live_allocations == 0) kush_panic();
    --kush_live_allocations; ++kush_deallocations;
}
/* ---- Bounded size-class pool for small native allocations ----------------
   Every native allocation carries a 32-byte header in front of its payload.
   The header size is a multiple of the 16-byte alignment requested from the
   system allocator, so payloads stay 16-byte aligned. `usable` records the
   payload capacity in bytes, `magic` checks the live-block invariant for valid
   allocation handles, and `next` links retained blocks. The marker is not a
   general detector for invalid pointers or stale handles after block reuse. Requests up to
   KUSH_POOL_MAX bytes use 16-byte size classes; a freed block returns to its
   class only while the retained total (header plus padded payload) stays at or
   below KUSH_POOL_RETAIN_CAP. Pooling is a physical optimization only: the
   logical counters still count one kush_alloc/kush_free call, so
   allocation-stats stays byte-identical. Headers also let buffer growth copy
   exactly the live capacity. All retained storage is drained back to the
   system on a normal exit. */
#define KUSH_ALLOC_ALIGN ((uint64_t)16)
#define KUSH_POOL_MAX ((uint64_t)1024)
#define KUSH_POOL_CLASSES ((size_t)(KUSH_POOL_MAX / KUSH_ALLOC_ALIGN))
#define KUSH_POOL_RETAIN_CAP ((uint64_t)1024 * 1024)
#define KUSH_ALLOC_MAGIC UINT64_C(0x4b555348414c4c4f)
typedef struct KushAllocHeader KushAllocHeader;
struct KushAllocHeader {
    uint64_t magic;
    uint64_t usable;
    uint64_t pooled;
    KushAllocHeader *next;
};
_Static_assert(sizeof(KushAllocHeader) % KUSH_ALLOC_ALIGN == 0,
               "allocation header must preserve 16-byte payload alignment");
static KushAllocHeader *kush_pool_lists[KUSH_POOL_CLASSES];
static uint64_t kush_pool_retained = 0;
static uint64_t kush_pool_peak_retained = 0;
static uint64_t kush_pool_hits = 0;
static uint64_t kush_pool_misses = 0;
static uint64_t kush_pool_retains = 0;
static uint64_t kush_pool_releases = 0;
static uint64_t kush_pool_drains = 0;
static size_t kush_pool_class(uint64_t usable) {
    return (size_t)(usable / KUSH_ALLOC_ALIGN) - 1;
}
/* Exact physical size of a block: header plus payload padded to alignment. */
static uint64_t kush_block_bytes(uint64_t usable) {
    uint64_t padded;
    if (__builtin_add_overflow(usable, (uint64_t)sizeof(KushAllocHeader), &padded)) kush_panic();
    if (__builtin_add_overflow(padded, KUSH_ALLOC_ALIGN - 1, &padded)) kush_panic();
    return padded & ~(KUSH_ALLOC_ALIGN - 1);
}
/* One system block, checked for overflow in header + payload + padding.
   `kush_try_system_block` reports refusal to its caller instead of aborting. */
static KushAllocHeader *kush_try_system_block(uint64_t usable) {
    uint64_t total = kush_block_bytes(usable);
    KushAllocHeader *header =
        (KushAllocHeader *)aligned_alloc((size_t)KUSH_ALLOC_ALIGN, (size_t)total);
    if (header == NULL) return NULL;
    header->magic = KUSH_ALLOC_MAGIC;
    header->usable = usable;
    header->pooled = usable <= KUSH_POOL_MAX ? 1 : 0;
    header->next = NULL;
    return header;
}
static KushAllocHeader *kush_system_block(uint64_t usable) {
    KushAllocHeader *header = kush_try_system_block(usable);
    if (header == NULL) kush_panic();
    return header;
}
/* Physical allocation. It never touches the logical allocation counters. */
static KushAllocHeader *kush_block_claim(uint64_t bytes) {
    if (bytes > KUSH_POOL_MAX) return kush_system_block(bytes);
    uint64_t usable = bytes, class_size;
    if (__builtin_add_overflow(bytes, KUSH_ALLOC_ALIGN - 1, &usable)) kush_panic();
    class_size = usable & ~(KUSH_ALLOC_ALIGN - 1);
    if (class_size == 0) class_size = KUSH_ALLOC_ALIGN;
    size_t class = kush_pool_class(class_size);
    KushAllocHeader *header = kush_pool_lists[class];
    if (header == NULL) {
        ++kush_pool_misses;
        return kush_system_block(class_size);
    }
    kush_pool_lists[class] = header->next;
    kush_pool_retained -= kush_block_bytes(header->usable);
    header->magic = KUSH_ALLOC_MAGIC;
    header->usable = class_size;
    header->next = NULL;
    ++kush_pool_hits;
    return header;
}
/* Physical release. Small blocks are retained only under the byte cap; every
   other block goes straight back to the system allocator exactly once. */
static void kush_block_release(KushAllocHeader *header) {
    uint64_t usable = header->usable, block = kush_block_bytes(usable);
    int poolable = header->pooled != 0 && usable >= KUSH_ALLOC_ALIGN
        && usable <= KUSH_POOL_MAX && usable % KUSH_ALLOC_ALIGN == 0;
    header->magic = 0;
    if (poolable && kush_pool_retained + block <= KUSH_POOL_RETAIN_CAP) {
        size_t class = kush_pool_class(usable);
        header->next = kush_pool_lists[class];
        kush_pool_lists[class] = header;
        kush_pool_retained += block;
        if (kush_pool_retained > kush_pool_peak_retained) kush_pool_peak_retained = kush_pool_retained;
        ++kush_pool_retains;
        return;
    }
    free(header);
    ++kush_pool_releases;
}
/* Release every retained physical block on a normal exit. */
static void kush_pool_drain(void) {
    for (size_t class = 0; class < KUSH_POOL_CLASSES; ++class) {
        KushAllocHeader *header = kush_pool_lists[class];
        kush_pool_lists[class] = NULL;
        while (header != NULL) {
            KushAllocHeader *next = header->next;
            free(header);
            ++kush_pool_drains;
            header = next;
        }
    }
    kush_pool_retained = 0;
}
uint64_t kush_alloc(uint64_t bytes) {
    void *payload = (void *)(kush_block_claim(bytes) + 1);
    kush_note_allocation();
    return (uint64_t)(uintptr_t)payload;
}
void kush_free(uint64_t handle) {
    if (handle == 0 || kush_live_allocations == 0) kush_panic();
    KushAllocHeader *header = (KushAllocHeader *)(uintptr_t)handle - 1;
    if (header->magic != KUSH_ALLOC_MAGIC) kush_panic();
    kush_note_deallocation();
    kush_block_release(header);
}
/* Header-aware grow for owning buffers. This replaces `realloc` exactly as far
   as diagnostics are concerned: the logical allocation counters are untouched
   and the caller keeps its own logical growth counter. The payload contents
   and alignment are preserved, and the old block is released once. */
void *kush_grow(void *payload, uint64_t bytes) {
    KushAllocHeader *header = (KushAllocHeader *)payload - 1;
    if (header->magic != KUSH_ALLOC_MAGIC) kush_panic();
    uint64_t copy = header->usable;
    if (bytes <= copy) return payload;
    KushAllocHeader *replacement = kush_block_claim(bytes);
    if (copy != 0) memcpy((void *)(replacement + 1), payload, (size_t)copy);
    kush_block_release(header);
    return (void *)(replacement + 1);
}
/* ---- Checked fallible allocation -----------------------------------------
   Fallible operations never call kush_panic on allocator refusal. A payload
   request that the system allocator or the configured probe rejects returns
   handle 0, which the generated code turns into the checked `Err` value.
   `KUSH_ALLOC_FAIL_AFTER=<n>` is a deterministic test probe: the first n
   growth-capable attempts succeed and later ones report refusal. It is only
   consulted by fallible operations; ordinary allocation still aborts. */
static uint64_t kush_try_attempts = 0;
static uint64_t kush_try_fail_after = UINT64_MAX;
static int kush_try_probe_initialized = 0;
static int kush_try_refuses(void) {
    if (!kush_try_probe_initialized) {
        const char *text = getenv("KUSH_ALLOC_FAIL_AFTER");
        if (text != NULL && *text != '\0') {
            char *end = NULL;
            unsigned long long limit = strtoull(text, &end, 10);
            if (end != text && *end == '\0') kush_try_fail_after = (uint64_t)limit;
        }
        kush_try_probe_initialized = 1;
    }
    if (kush_try_attempts >= kush_try_fail_after) {
        ++kush_try_attempts;
        return 1;
    }
    ++kush_try_attempts;
    return 0;
}
uint64_t kush_try_alloc(uint64_t bytes) {
    if (kush_try_refuses()) return 0;
    if (bytes > KUSH_POOL_MAX) {
        KushAllocHeader *header = kush_try_system_block(bytes);
        if (header == NULL) return 0;
        kush_note_allocation();
        return (uint64_t)(uintptr_t)(header + 1);
    }
    uint64_t usable = bytes, class_size;
    if (__builtin_add_overflow(bytes, KUSH_ALLOC_ALIGN - 1, &usable)) return 0;
    class_size = usable & ~(KUSH_ALLOC_ALIGN - 1);
    if (class_size == 0) class_size = KUSH_ALLOC_ALIGN;
    size_t class = kush_pool_class(class_size);
    KushAllocHeader *header = kush_pool_lists[class];
    if (header == NULL) {
        ++kush_pool_misses;
        header = kush_try_system_block(class_size);
        if (header == NULL) return 0;
    } else {
        kush_pool_lists[class] = header->next;
        kush_pool_retained -= kush_block_bytes(header->usable);
        header->magic = KUSH_ALLOC_MAGIC;
        header->usable = class_size;
        header->next = NULL;
        ++kush_pool_hits;
    }
    kush_note_allocation();
    return (uint64_t)(uintptr_t)(header + 1);
}
/* Fallible header-aware growth. A request that already fits the existing
   usable capacity returns the same payload without touching the probe or the
   allocator, so a same-allocation reuse cannot fail. On refusal the old block
   is left completely untouched for the checked error path. */
void *kush_try_grow(void *payload, uint64_t bytes) {
    KushAllocHeader *header = (KushAllocHeader *)payload - 1;
    if (header->magic != KUSH_ALLOC_MAGIC) return NULL;
    uint64_t copy = header->usable;
    if (bytes <= copy) return payload;
    if (kush_try_refuses()) return NULL;
    KushAllocHeader *replacement = kush_try_system_block(bytes);
    if (replacement == NULL) return NULL;
    if (copy != 0) memcpy((void *)(replacement + 1), payload, (size_t)copy);
    kush_block_release(header);
    return (void *)(replacement + 1);
}
int64_t kush_note_reuse(void) { ++kush_reuses; return 0; }
/* ---- Scoped bump-allocator regions ---------------------------------------
   `Arena.new()` is one logical allocation (the region descriptor). Chunks are
   physical storage obtained directly from the system allocator and are not
   counted as separate logical allocations. Every `ArenaBox` retains one
   region reference, so dropping the arena value while boxes live is safe; the
   last reference releases every chunk and the descriptor. Payloads are word
   aligned. The eight-byte box header stores the region pointer. */
typedef struct KushArenaChunk KushArenaChunk;
struct KushArenaChunk {
    KushArenaChunk *next;
    uint64_t used;
    uint64_t capacity;
    uint64_t padding;
    unsigned char data[];
};
_Static_assert(sizeof(KushArenaChunk) % KUSH_ALLOC_ALIGN == 0,
               "arena chunk data must preserve alignment");
/* Optional user chunk-sizing strategy. It is a noncapturing generated
   function with signature uint64_t(uint64_t need, uint64_t current) and is
   called only while sizing a fresh chunk. */
typedef uint64_t (*KushArenaStrategy)(uint64_t need, uint64_t current);
typedef struct KushArena {
    uint64_t references;
    KushArenaChunk *chunks;
    KushArenaStrategy strategy;
} KushArena;
static uint64_t kush_arena_round(uint64_t bytes) {
    uint64_t rounded, total;
    if (__builtin_add_overflow(bytes, (uint64_t)8, &total)) kush_panic();
    if (__builtin_add_overflow(total, KUSH_ALLOC_ALIGN - 1, &rounded)) kush_panic();
    return rounded & ~(KUSH_ALLOC_ALIGN - 1);
}
/* Non-aborting variant used by the fallible entry point. */
static int kush_arena_try_round(uint64_t bytes, uint64_t *need) {
    uint64_t rounded;
    if (__builtin_add_overflow(bytes, (uint64_t)8, need)) return 0;
    if (__builtin_add_overflow(*need, KUSH_ALLOC_ALIGN - 1, &rounded)) return 0;
    *need = rounded & ~(KUSH_ALLOC_ALIGN - 1);
    return 1;
}
static uint64_t kush_arena_chunk_capacity(KushArena *arena, uint64_t need) {
    uint64_t current = arena->chunks == NULL ? 0 : arena->chunks->capacity;
    if (arena->strategy != NULL) {
        uint64_t chosen = arena->strategy(need, current);
        if ((int64_t)chosen < 0) return need;
        return chosen > need ? chosen : need;
    }
    return need < 4096 ? 4096 : need;
}
static void kush_arena_free_chunks(KushArena *arena) {
    KushArenaChunk *chunk = arena->chunks;
    while (chunk != NULL) {
        KushArenaChunk *next = chunk->next;
        free(chunk);
        chunk = next;
    }
    arena->chunks = NULL;
}
static void kush_arena_release_pointer(KushArena *arena) {
    if (arena->references == 0) kush_panic();
    --arena->references;
    if (arena->references == 0) {
        kush_arena_free_chunks(arena);
        kush_free((uint64_t)(uintptr_t)arena);
    }
}
static KushArena *kush_arena_create(KushArenaStrategy strategy) {
    KushArena *arena = (KushArena *)(uintptr_t)kush_alloc(sizeof(KushArena));
    arena->references = 1;
    arena->chunks = NULL;
    arena->strategy = strategy;
    return arena;
}
uint64_t kush_arena_new(void) { return (uint64_t)(uintptr_t)kush_arena_create(NULL); }
uint64_t kush_arena_new_with_strategy(uint64_t strategy) {
    return (uint64_t)(uintptr_t)kush_arena_create((KushArenaStrategy)(uintptr_t)strategy);
}
static KushArenaChunk *kush_arena_claim_chunk(uint64_t capacity) {
    uint64_t total;
    if (__builtin_add_overflow(sizeof(KushArenaChunk), capacity, &total)) kush_panic();
    if (__builtin_add_overflow(total, KUSH_ALLOC_ALIGN - 1, &total)) kush_panic();
    total &= ~(KUSH_ALLOC_ALIGN - 1);
    KushArenaChunk *fresh =
        (KushArenaChunk *)aligned_alloc((size_t)KUSH_ALLOC_ALIGN, (size_t)total);
    if (fresh == NULL) kush_panic();
    fresh->next = NULL;
    fresh->used = 0;
    fresh->capacity = capacity;
    fresh->padding = 0;
    return fresh;
}
static int kush_arena_try_claim_chunk(uint64_t capacity, KushArenaChunk **out) {
    uint64_t total;
    if (__builtin_add_overflow(sizeof(KushArenaChunk), capacity, &total)) return 0;
    if (__builtin_add_overflow(total, KUSH_ALLOC_ALIGN - 1, &total)) return 0;
    total &= ~(KUSH_ALLOC_ALIGN - 1);
    KushArenaChunk *fresh =
        (KushArenaChunk *)aligned_alloc((size_t)KUSH_ALLOC_ALIGN, (size_t)total);
    if (fresh == NULL) return 0;
    fresh->next = NULL;
    fresh->used = 0;
    fresh->capacity = capacity;
    fresh->padding = 0;
    *out = fresh;
    return 1;
}
uint64_t kush_arena_alloc(uint64_t handle, uint64_t bytes) {
    KushArena *arena = (KushArena *)(uintptr_t)handle;
    uint64_t need = kush_arena_round(bytes);
    KushArenaChunk *chunk = arena->chunks;
    if (chunk == NULL || chunk->capacity - chunk->used < need) {
        uint64_t capacity = kush_arena_chunk_capacity(arena, need);
        KushArenaChunk *fresh = kush_arena_claim_chunk(capacity);
        fresh->next = arena->chunks;
        arena->chunks = fresh;
        chunk = fresh;
    }
    unsigned char *start = chunk->data + chunk->used;
    chunk->used += need;
    *(KushArena **)(void *)start = arena;
    ++arena->references;
    return (uint64_t)(uintptr_t)(start + 8);
}
/* Fallible arena allocation. A refused chunk request leaves the region's
   reference count, chunk list, and bump position exactly as they were, so the
   caller can retry or keep using the region after returning the payload in
   Err. An allocation that fits the current chunk does not touch the fallible
   attempt probe. */
uint64_t kush_arena_try_alloc(uint64_t handle, uint64_t bytes) {
    KushArena *arena = (KushArena *)(uintptr_t)handle;
    uint64_t need;
    if (!kush_arena_try_round(bytes, &need)) return 0;
    KushArenaChunk *chunk = arena->chunks;
    if (chunk == NULL || chunk->capacity - chunk->used < need) {
        if (kush_try_refuses()) return 0;
        uint64_t capacity = kush_arena_chunk_capacity(arena, need);
        KushArenaChunk *fresh = NULL;
        if (!kush_arena_try_claim_chunk(capacity, &fresh)) return 0;
        fresh->next = arena->chunks;
        arena->chunks = fresh;
        chunk = fresh;
    }
    unsigned char *start = chunk->data + chunk->used;
    chunk->used += need;
    *(KushArena **)(void *)start = arena;
    ++arena->references;
    return (uint64_t)(uintptr_t)(start + 8);
}
void kush_arena_release(uint64_t handle) {
    kush_arena_release_pointer((KushArena *)(uintptr_t)handle);
}
void kush_arena_box_release(uint64_t payload) {
    KushArena *arena = *(KushArena **)(void *)(uintptr_t)(payload - 8);
    kush_arena_release_pointer(arena);
}
typedef struct { uint64_t length; uint64_t capacity; unsigned char data[]; } KushBytes;
#define KUSH_MAX_CAPACITY ((uint64_t)INT64_MAX - (uint64_t)sizeof(KushBytes))
uint64_t kush_bytes_with_capacity(int64_t capacity) {
    if (capacity < 0 || (uint64_t)capacity > KUSH_MAX_CAPACITY) kush_panic();
    KushBytes *b = (KushBytes *)(uintptr_t)kush_alloc(sizeof(KushBytes) + (uint64_t)capacity);
    b->length = 0; b->capacity = (uint64_t)capacity; return (uint64_t)(uintptr_t)b;
}
uint64_t kush_try_bytes_with_capacity(int64_t capacity) {
    if (capacity < 0 || (uint64_t)capacity > KUSH_MAX_CAPACITY) return 0;
    uint64_t handle = kush_try_alloc(sizeof(KushBytes) + (uint64_t)capacity);
    if (handle == 0) return 0;
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    b->length = 0; b->capacity = (uint64_t)capacity;
    return handle;
}
uint64_t kush_bytes_from(const unsigned char *source, int64_t length) {
    uint64_t handle = kush_bytes_with_capacity(length); KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (length != 0) memcpy(b->data, source, (size_t)length);
    b->length = (uint64_t)length; return handle;
}
/* ---- User-defined allocators ---------------------------------------------
   A checked allocator value is a pair of noncapturing code pointers:
   `alloc(bytes) -> Bytes` supplies a block with at least `bytes` capacity, and
   `free(block) -> Unit` releases it. A smaller returned block is a refusal and
   is released through the same pair. Containers store the pair themselves, so
   dropping or moving the allocator binding cannot strand an allocation, and
   release always uses the allocator that supplied the block. */
typedef uint64_t (*KushAllocBlockFn)(uint64_t bytes);
typedef void (*KushFreeBlockFn)(uint64_t block);
unsigned char *kush_alloc_block_data(uint64_t block) {
    return ((KushBytes *)(uintptr_t)block)->data;
}
static void kush_alloc_block_release(uint64_t release, uint64_t block) {
    if (block == 0) return;
    if (release == 0) kush_panic();
    ((KushFreeBlockFn)(uintptr_t)release)(block);
}
uint64_t kush_alloc_block_try(uint64_t allocator, uint64_t release, uint64_t bytes) {
    if (allocator == 0) kush_panic();
    uint64_t block = ((KushAllocBlockFn)(uintptr_t)allocator)(bytes);
    if (block == 0) return 0;
    if (((KushBytes *)(uintptr_t)block)->capacity < bytes) {
        kush_alloc_block_release(release, block);
        return 0;
    }
    return block;
}
uint64_t kush_alloc_block(uint64_t allocator, uint64_t release, uint64_t bytes) {
    uint64_t block = kush_alloc_block_try(allocator, release, bytes);
    if (block == 0) kush_panic();
    return block;
}
typedef struct { uint64_t allocator; uint64_t release; uint64_t block; } KushAllocBox;
uint64_t kush_alloc_box_create(uint64_t allocator, uint64_t release, uint64_t block) {
    KushAllocBox *box = (KushAllocBox *)(uintptr_t)kush_alloc(sizeof(KushAllocBox));
    box->allocator = allocator; box->release = release; box->block = block;
    return (uint64_t)(uintptr_t)box;
}
unsigned char *kush_alloc_box_payload(uint64_t handle) {
    return kush_alloc_block_data(((KushAllocBox *)(uintptr_t)handle)->block);
}
void kush_alloc_box_release(uint64_t handle) {
    KushAllocBox *box = (KushAllocBox *)(uintptr_t)handle;
    kush_alloc_block_release(box->release, box->block);
    kush_free(handle);
}
typedef struct {
    uint64_t length; uint64_t capacity; uint64_t width;
    uint64_t allocator; uint64_t release; uint64_t block;
} KushAllocVec;
static uint64_t kush_alloc_vec_block_bytes(uint64_t capacity, uint64_t width) {
    if (width == 0 || capacity > ((uint64_t)INT64_MAX) / 8 / width) kush_panic();
    return capacity * width * 8;
}
uint64_t kush_alloc_vec_create(uint64_t allocator, uint64_t release, int64_t capacity, int64_t width) {
    if (capacity < 0 || width <= 0) kush_panic();
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)kush_alloc(sizeof(KushAllocVec));
    v->length = 0; v->capacity = (uint64_t)capacity; v->width = (uint64_t)width;
    v->allocator = allocator; v->release = release; v->block = 0;
    if (capacity > 0) {
        v->block = kush_alloc_block(allocator, release, kush_alloc_vec_block_bytes(v->capacity, v->width));
    }
    return (uint64_t)(uintptr_t)v;
}
static void kush_alloc_vec_grow(KushAllocVec *v, uint64_t next) {
    uint64_t bytes = kush_alloc_vec_block_bytes(next, v->width);
    uint64_t block = kush_alloc_block(v->allocator, v->release, bytes);
    if (v->length != 0) {
        memcpy(kush_alloc_block_data(block), kush_alloc_block_data(v->block),
               (size_t)(v->length * v->width * 8));
    }
    kush_alloc_block_release(v->release, v->block);
    v->block = block; v->capacity = next; ++kush_buffer_growths;
}
int64_t kush_alloc_vec_len(uint64_t handle) {
    return (int64_t)((KushAllocVec *)(uintptr_t)handle)->length;
}
void kush_alloc_vec_get(uint64_t handle, int64_t index, uint64_t *out) {
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= v->length) kush_panic();
    memcpy(out, kush_alloc_block_data(v->block) + (uint64_t)index * v->width * 8,
           (size_t)(v->width * 8));
}
uint64_t kush_alloc_vec_push(uint64_t handle, const uint64_t *item) {
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)handle;
    if (v->length == v->capacity) {
        uint64_t next = v->capacity == 0 ? 4 : v->capacity * 2;
        if (next <= v->capacity) kush_panic();
        kush_alloc_vec_grow(v, next);
    }
    memcpy(kush_alloc_block_data(v->block) + v->length * v->width * 8, item,
           (size_t)(v->width * 8));
    v->length++;
    return handle;
}
uint64_t kush_alloc_vec_set(uint64_t handle, int64_t index, const uint64_t *item, uint64_t *old) {
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= v->length) kush_panic();
    unsigned char *slot = kush_alloc_block_data(v->block) + (uint64_t)index * v->width * 8;
    memcpy(old, slot, (size_t)(v->width * 8));
    memcpy(slot, item, (size_t)(v->width * 8));
    return handle;
}
void kush_alloc_vec_clear(uint64_t handle) {
    ((KushAllocVec *)(uintptr_t)handle)->length = 0;
}
unsigned char *kush_alloc_vec_data(uint64_t handle) {
    return kush_alloc_block_data(((KushAllocVec *)(uintptr_t)handle)->block);
}
void kush_alloc_vec_release(uint64_t handle) {
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)handle;
    kush_alloc_block_release(v->release, v->block);
    kush_free(handle);
}
int64_t kush_bytes_len(uint64_t handle) { return (int64_t)((KushBytes *)(uintptr_t)handle)->length; }
int64_t kush_bytes_capacity(uint64_t handle) { return (int64_t)((KushBytes *)(uintptr_t)handle)->capacity; }
int64_t kush_bytes_get(uint64_t handle, int64_t index) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= b->length) kush_panic();
    return (int64_t)b->data[(uint64_t)index];
}
uint64_t kush_bytes_clear(uint64_t handle) {
    ((KushBytes *)(uintptr_t)handle)->length = 0; return handle;
}
uint64_t kush_bytes_copy(uint64_t handle) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle; return kush_bytes_from(b->data, (int64_t)b->length);
}
static uint64_t kush_bytes_push_impl(uint64_t handle, int64_t value, int grow) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (value < 0 || value > 255) kush_panic();
    if (b->length == b->capacity) {
        if (!grow) kush_panic();
        uint64_t next = b->capacity == 0 ? 8 : (b->capacity <= KUSH_MAX_CAPACITY / 2 ? b->capacity * 2 : KUSH_MAX_CAPACITY);
        if (next <= b->capacity || next > KUSH_MAX_CAPACITY) kush_panic();
        b = (KushBytes *)kush_grow(b, sizeof(KushBytes) + next);
        b->capacity = next; ++kush_buffer_growths;
    }
    b->data[b->length++] = (unsigned char)value; return (uint64_t)(uintptr_t)b;
}
uint64_t kush_bytes_push(uint64_t handle, int64_t value) { return kush_bytes_push_impl(handle, value, 1); }
uint64_t kush_bytes_push_reserved(uint64_t handle, int64_t value) { return kush_bytes_push_impl(handle, value, 0); }
/* Strict UTF-8 validation: rejects overlong forms, surrogates, and code points
   above U+10FFFF. The String type is admitted only after this check. */
static int kush_utf8_valid_data(const unsigned char *data, uint64_t length) {
    uint64_t i = 0;
    while (i < length) {
        uint32_t code;
        uint64_t need, j;
        unsigned char lead = data[i];
        if (lead < 0x80) { i += 1; continue; }
        if ((lead & 0xE0) == 0xC0) { code = lead & 0x1F; need = 1; }
        else if ((lead & 0xF0) == 0xE0) { code = lead & 0x0F; need = 2; }
        else if ((lead & 0xF8) == 0xF0) { code = lead & 0x07; need = 3; }
        else return 0;
        if (length - i <= need) return 0;
        for (j = 1; j <= need; ++j) {
            unsigned char next = data[i + j];
            if ((next & 0xC0) != 0x80) return 0;
            code = (code << 6) | (uint32_t)(next & 0x3F);
        }
        if ((need == 1 && code < 0x80) || (need == 2 && code < 0x800)
            || (need == 3 && code < 0x10000)) return 0;
        if (code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) return 0;
        i += need + 1;
    }
    return 1;
}
int64_t kush_utf8_validate(uint64_t handle) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    return (int64_t)kush_utf8_valid_data(b->data, b->length);
}
int64_t kush_utf8_scalar_len(uint64_t handle) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (!kush_utf8_valid_data(b->data, b->length)) kush_panic();
    int64_t count = 0;
    for (uint64_t i = 0; i < b->length; ++i) {
        if ((b->data[i] & 0xC0) != 0x80) ++count;
    }
    return count;
}
/* Scalar-indexed code point, or -1 when the scalar index is out of range. */
int64_t kush_utf8_scalar_at(uint64_t handle, int64_t index) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (!kush_utf8_valid_data(b->data, b->length)) kush_panic();
    if (index < 0) return -1;
    uint64_t target = (uint64_t)index, scalar = 0, i = 0;
    while (i < b->length) {
        unsigned char lead = b->data[i];
        uint32_t code;
        uint64_t need;
        if (lead < 0x80) { code = lead; need = 0; }
        else if ((lead & 0xE0) == 0xC0) { code = lead & 0x1F; need = 1; }
        else if ((lead & 0xF0) == 0xE0) { code = lead & 0x0F; need = 2; }
        else { code = lead & 0x07; need = 3; }
        for (uint64_t j = 1; j <= need; ++j) code = (code << 6) | (uint32_t)(b->data[i + j] & 0x3F);
        if (scalar == target) return (int64_t)code;
        ++scalar;
        i += need + 1;
    }
    return -1;
}
/* Borrowed &str views are checked contiguous pieces of a validated String at
   Unicode scalar boundaries, so these reads need no revalidation. */
int64_t kush_str_scalar_len(const unsigned char *data, int64_t length) {
    int64_t count = 0;
    for (int64_t i = 0; i < length; ++i) {
        if ((data[i] & 0xC0) != 0x80) ++count;
    }
    return count;
}
int64_t kush_str_byte_at(const unsigned char *data, int64_t length, int64_t index) {
    if (index < 0 || index >= length) kush_panic();
    return (int64_t)data[index];
}
int64_t kush_str_scalar_at(const unsigned char *data, int64_t length, int64_t index) {
    if (index < 0) return -1;
    int64_t target = index, scalar = 0, i = 0;
    while (i < length) {
        unsigned char lead = data[i];
        uint32_t code;
        uint64_t need;
        if (lead < 0x80) { code = lead; need = 0; }
        else if ((lead & 0xE0) == 0xC0) { code = lead & 0x1F; need = 1; }
        else if ((lead & 0xF0) == 0xE0) { code = lead & 0x0F; need = 2; }
        else { code = lead & 0x07; need = 3; }
        for (uint64_t j = 1; j <= need; ++j) code = (code << 6) | (uint32_t)(data[i + j] & 0x3F);
        if (scalar == target) return (int64_t)code;
        ++scalar;
        i += (int64_t)need + 1;
    }
    return -1;
}
uint64_t kush_str_to_string(const unsigned char *data, int64_t length) {
    return kush_bytes_from(data, length);
}
/* These operations never grow storage. On read failure, ownership is consumed. */
int64_t kush_io_read_all(int64_t stream, uint64_t handle) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    unsigned char probe;
    for (;;) {
        int full = b->length == b->capacity;
        void *destination = full ? (void *)&probe : (void *)(b->data + b->length);
        size_t count = full ? 1 : (size_t)(b->capacity - b->length);
        ssize_t received = read((int)stream, destination, count);
        if (received < 0 && errno == EINTR) continue;
        if (received < 0) { int code = errno; kush_free(handle); return code; }
        if (received == 0) return 0;
        if (full) { kush_free(handle); return EFBIG; }
        b->length += (uint64_t)received;
    }
}
/* A line includes its newline; EOF returns the partial line, or an empty buffer.
   Never read past the delimiter, so the next call retains the next command. */
int64_t kush_io_read_line(int64_t stream, uint64_t handle) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    for (;;) {
        unsigned char byte;
        ssize_t received = read((int)stream, &byte, 1);
        if (received < 0 && errno == EINTR) continue;
        if (received < 0) { int code = errno; kush_free(handle); return code; }
        if (received == 0) return 0;
        if (b->length == b->capacity) { kush_free(handle); return EFBIG; }
        b->data[b->length++] = byte;
        if (byte == '\n') return 0;
    }
}
/* One successful read, never an excess-byte probe. Full input is EFBIG. */
int64_t kush_io_read_chunk(int64_t stream, uint64_t handle) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (b->length == b->capacity) { kush_free(handle); return EFBIG; }
    for (;;) {
        ssize_t n = read((int)stream, b->data + b->length, (size_t)(b->capacity - b->length));
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { int code = errno; kush_free(handle); return code; }
        b->length += (uint64_t)n; return 0;
    }
}
int64_t kush_io_write(int64_t stream, uint64_t handle) {
    const KushBytes *b = (const KushBytes *)(uintptr_t)handle;
    uint64_t offset = 0;
    while (offset < b->length) {
        ssize_t written = write((int)stream, b->data + offset, (size_t)(b->length - offset));
        if (written < 0 && errno == EINTR) continue;
        if (written < 0) return errno;
        if (written == 0) return EIO;
        offset += (uint64_t)written;
    }
    return 0;
}
/* Vectors store fixed-width elements of `width` 64-bit words each. */
typedef struct { uint64_t length; uint64_t capacity; uint64_t width; uint64_t data[]; } KushVec;
static uint64_t kush_vec_bytes(uint64_t capacity, uint64_t width) {
    if (width == 0 || capacity > ((uint64_t)INT64_MAX - sizeof(KushVec)) / 8 / width) kush_panic();
    return sizeof(KushVec) + capacity * width * 8;
}
uint64_t kush_vec_with_capacity(int64_t capacity, int64_t width) {
    if (capacity < 0 || width <= 0) kush_panic();
    KushVec *v = (KushVec *)(uintptr_t)kush_alloc(kush_vec_bytes((uint64_t)capacity, (uint64_t)width));
    v->length = 0; v->capacity = (uint64_t)capacity; v->width = (uint64_t)width;
    return (uint64_t)(uintptr_t)v;
}
int64_t kush_vec_len(uint64_t handle) { return (int64_t)((KushVec *)(uintptr_t)handle)->length; }
void kush_vec_get(uint64_t handle, int64_t index, uint64_t *out) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= v->length) kush_panic();
    memcpy(out, v->data + (uint64_t)index * v->width, (size_t)(v->width * 8));
}
uint64_t kush_vec_push(uint64_t handle, const uint64_t *item) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (v->length == v->capacity) {
        uint64_t next = v->capacity == 0 ? 4 : v->capacity * 2;
        if (next <= v->capacity) kush_panic();
        uint64_t bytes = kush_vec_bytes(next, v->width);
        v = (KushVec *)kush_grow(v, bytes);
        v->capacity = next; ++kush_buffer_growths;
    }
    memcpy(v->data + v->length * v->width, item, (size_t)(v->width * 8));
    v->length++;
    return (uint64_t)(uintptr_t)v;
}
uint64_t kush_vec_set(uint64_t handle, int64_t index, const uint64_t *item, uint64_t *old) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= v->length) kush_panic();
    uint64_t *slot = v->data + (uint64_t)index * v->width;
    memcpy(old, slot, (size_t)(v->width * 8));
    memcpy(slot, item, (size_t)(v->width * 8));
    return handle;
}
/* Ensure room for `additional` elements after the current length. Growth
   happens at most once, to exactly the requested length, and only when the
   retained capacity is insufficient. Negative or overflowing requests panic. */
uint64_t kush_vec_reserve(uint64_t handle, int64_t additional) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (additional < 0) kush_panic();
    uint64_t needed;
    if (__builtin_add_overflow(v->length, (uint64_t)additional, &needed)) kush_panic();
    if (needed <= v->capacity) return handle;
    KushVec *replacement = (KushVec *)kush_grow(v, kush_vec_bytes(needed, v->width));
    replacement->capacity = needed;
    ++kush_buffer_growths;
    return (uint64_t)(uintptr_t)replacement;
}
/* On refusal or invalid capacity, the original allocation/header/elements
   remain untouched. Zero is an out-of-band failure handle, never an owner. */
uint64_t kush_vec_try_reserve(uint64_t handle, int64_t additional) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (additional < 0) return 0;
    uint64_t needed;
    if (__builtin_add_overflow(v->length, (uint64_t)additional, &needed)) return 0;
    if (needed <= v->capacity) return handle;
    if (v->width == 0 || needed > ((uint64_t)INT64_MAX - sizeof(KushVec)) / 8 / v->width) return 0;
    uint64_t bytes = sizeof(KushVec) + needed * v->width * 8;
    KushVec *replacement = (KushVec *)kush_try_grow(v, bytes);
    if (replacement == NULL) return 0;
    replacement->capacity = needed;
    ++kush_buffer_growths;
    return (uint64_t)(uintptr_t)replacement;
}
/* Widen or compact a vector's element stride while preserving the allocation
   when the retained usable capacity already covers `capacity * target_width`
   elements. Otherwise `kush_grow` moves the block once. Elements are moved
   with memmove: forwards for a compaction, backwards for a widening, so the
   move never overwrites a source element that has not been moved yet. The
   caller then applies callbacks in forward order at the new stride. The
   logical allocation counters are unchanged; `buffer-growths` counts an
   actual block move. */
uint64_t kush_vec_restride(uint64_t handle, int64_t source_width, int64_t target_width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (source_width <= 0 || target_width <= 0) kush_panic();
    if (v->width != (uint64_t)source_width) kush_panic();
    uint64_t bytes = kush_vec_bytes(v->capacity, (uint64_t)target_width);
    KushVec *replacement = (KushVec *)kush_grow(v, bytes);
    if (replacement != v) ++kush_buffer_growths;
    v = replacement;
    uint64_t source = (uint64_t)source_width * 8;
    uint64_t target = (uint64_t)target_width * 8;
    if (source != target) {
        unsigned char *data = (unsigned char *)v->data;
        if (target > source) {
            uint64_t index = v->length;
            while (index > 0) {
                --index;
                memmove(data + index * target, data + index * source, (size_t)source);
            }
        } else {
            for (uint64_t index = 0; index < v->length; ++index) {
                memmove(data + index * target, data + index * source, (size_t)source);
            }
        }
    }
    v->width = (uint64_t)target_width;
    return (uint64_t)(uintptr_t)v;
}
/* Stackful cooperative tasks. One OS thread; strict handoff. */
#include <ucontext.h>
#include <sys/mman.h>
#define KUSH_MAX_TASKS 256
#define KUSH_MAX_SCOPES 16
#define KUSH_MAX_CHILDREN 64
#define KUSH_TASK_STACK (256u * 1024u)
enum { KUSH_READY = 0, KUSH_RUNNING = 1, KUSH_BLOCKED = 2, KUSH_FINISHED = 3 };
typedef struct KushTask KushTask;
struct KushTask {
    ucontext_t context;
    uint64_t id, wrapper, code, env;
    void *result;
    size_t result_size;
    void (*drop)(void *);
    int state, cancelled, joined, completed, preserve;
    KushTask *waiter;
    uint64_t scope_ids[KUSH_MAX_SCOPES][KUSH_MAX_CHILDREN];
    int scope_counts[KUSH_MAX_SCOPES];
    int scope_depth;
    void *stack_base;
    size_t stack_total;
};
static KushTask *kush_tasks[KUSH_MAX_TASKS];
static int kush_task_count = 0;
static KushTask *kush_current = NULL;
static ucontext_t kush_scheduler_context;
static void *kush_scheduler_stack = NULL;
static size_t kush_scheduler_stack_total = 0;
static int kush_initialized = 0;
static int kush_ready[KUSH_MAX_TASKS];
static int kush_ready_head = 0, kush_ready_tail = 0, kush_ready_count = 0;
/* ---- Dynamic one-shot effect handlers -----------------------------------
   Declared effect operations use a small per-task stack of copyable,
   noncapturing handler code pointers. A lexical handle pushes one entry for
   the duration of its body; a `perform` in a called function resolves the
   innermost matching entry. Entries carry no owning environment: the checker
   rejects consuming/capturing handlers here, and the ordinary lexical path
   still consumes those values. */
#define KUSH_HANDLER_MAX 64
typedef struct {
    int64_t operation;
    int64_t code;
    int64_t environment;
} kush_handler_frame;
typedef struct {
    kush_handler_frame frames[KUSH_HANDLER_MAX];
    int64_t depth;
} kush_handler_context;
static kush_handler_context kush_handler_contexts[KUSH_MAX_TASKS];
static kush_handler_context *kush_handlers(void) {
    int64_t id = kush_current == NULL ? 0 : (int64_t)kush_current->id;
    if (id < 0 || id >= KUSH_MAX_TASKS) id = 0;
    return &kush_handler_contexts[id];
}
int64_t kush_handler_depth(void) {
    return kush_handlers()->depth;
}
void kush_handler_restore(int64_t depth) {
    if (depth < 0) depth = 0;
    if (depth < kush_handlers()->depth) kush_handlers()->depth = depth;
}
void kush_handler_push(int64_t operation, int64_t code, int64_t environment) {
    kush_handler_context *handlers = kush_handlers();
    if (handlers->depth >= KUSH_HANDLER_MAX) kush_panic();
    handlers->frames[handlers->depth].operation = operation;
    handlers->frames[handlers->depth].code = code;
    handlers->frames[handlers->depth].environment = environment;
    handlers->depth += 1;
}
void kush_handler_pop(void) {
    kush_handler_context *handlers = kush_handlers();
    if (handlers->depth > 0) handlers->depth -= 1;
}
int64_t kush_handler_lookup(int64_t operation, int64_t *out) {
    kush_handler_context *handlers = kush_handlers();
    for (int64_t index = handlers->depth - 1; index >= 0; --index) {
        if (handlers->frames[index].operation == operation) {
            out[0] = handlers->frames[index].code;
            out[1] = handlers->frames[index].environment;
            return 1;
        }
    }
    return 0;
}
static void *kush_stack_alloc(size_t bytes, void **base_out, size_t *total_out) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    size_t total = ((bytes + page - 1) / page) * page + page;
    void *base = mmap(NULL, total, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK, -1, 0);
    if (base == MAP_FAILED) kush_panic();
    if (mprotect(base, page, PROT_NONE) != 0) kush_panic();
    kush_note_allocation();
    *base_out = base; *total_out = total;
    return (void *)((char *)base + page);
}
static void kush_stack_free(void *base, size_t total) {
    if (base == NULL) return;
    if (munmap(base, total) != 0) kush_panic();
    kush_note_deallocation();
}
static void kush_ready_push(int id) {
    if (kush_ready_count >= KUSH_MAX_TASKS) kush_panic();
    kush_ready[kush_ready_tail] = id;
    kush_ready_tail = (kush_ready_tail + 1) % KUSH_MAX_TASKS;
    ++kush_ready_count;
}
static int kush_ready_pop(void) {
    int id = kush_ready[kush_ready_head];
    kush_ready_head = (kush_ready_head + 1) % KUSH_MAX_TASKS;
    --kush_ready_count;
    return id;
}
static void kush_scheduler(void) {
    for (;;) {
        if (kush_ready_count == 0) kush_panic();
        int id = kush_ready_pop();
        KushTask *t = kush_tasks[id];
        if (t == NULL || t->state == KUSH_FINISHED) continue;
        t->state = KUSH_RUNNING;
        kush_current = t;
        swapcontext(&kush_scheduler_context, &t->context);
    }
}
static void kush_task_entry(unsigned int low, unsigned int high);
static void kush_task_init(void) {
    if (kush_initialized) return;
    KushTask *root = (KushTask *)(uintptr_t)kush_alloc(sizeof(KushTask));
    memset(root, 0, sizeof(*root));
    root->id = 0; root->state = KUSH_RUNNING; root->completed = 1;
    kush_tasks[0] = root; kush_task_count = 1; kush_current = root;
    void *base; size_t total;
    void *stack = kush_stack_alloc(KUSH_TASK_STACK, &base, &total);
    kush_scheduler_stack = base; kush_scheduler_stack_total = total;
    if (getcontext(&kush_scheduler_context) != 0) kush_panic();
    kush_scheduler_context.uc_stack.ss_sp = stack;
    kush_scheduler_context.uc_stack.ss_size = KUSH_TASK_STACK;
    kush_scheduler_context.uc_link = NULL;
    makecontext(&kush_scheduler_context, kush_scheduler, 0);
    kush_initialized = 1;
}
uint64_t kush_task_spawn(uint64_t wrapper, uint64_t code, uint64_t env,
                         uint64_t result_size, uint64_t drop, uint64_t preserve) {
    kush_task_init();
    if (kush_current->scope_depth == 0) kush_panic();
    if (kush_task_count >= KUSH_MAX_TASKS) kush_panic();
    int id = kush_task_count++;
    KushTask *t = (KushTask *)(uintptr_t)kush_alloc(sizeof(KushTask));
    memset(t, 0, sizeof(*t));
    t->id = (uint64_t)id; t->wrapper = wrapper; t->code = code; t->env = env;
    t->result_size = result_size == 0 ? 8 : (size_t)result_size;
    t->drop = (void (*)(void *))(uintptr_t)drop;
    t->preserve = preserve != 0;
    t->result = (void *)(uintptr_t)kush_alloc(t->result_size);
    void *base; size_t total;
    void *stack = kush_stack_alloc(KUSH_TASK_STACK, &base, &total);
    t->stack_base = base; t->stack_total = total;
    if (getcontext(&t->context) != 0) kush_panic();
    t->context.uc_stack.ss_sp = stack;
    t->context.uc_stack.ss_size = KUSH_TASK_STACK;
    t->context.uc_link = NULL;
    uintptr_t pointer = (uintptr_t)t;
    makecontext(&t->context, (void (*)(void))kush_task_entry, 2,
                (unsigned int)(pointer & 0xffffffffu),
                (unsigned int)(pointer >> 32));
    t->state = KUSH_READY;
    kush_tasks[id] = t;
    kush_ready_push(id);
    int depth = kush_current->scope_depth - 1;
    if (kush_current->scope_counts[depth] >= KUSH_MAX_CHILDREN) kush_panic();
    kush_current->scope_ids[depth][kush_current->scope_counts[depth]++] = (uint64_t)id;
    return (uint64_t)(id + 1);
}
static void kush_task_entry(unsigned int low, unsigned int high) {
    uintptr_t pointer = ((uintptr_t)high << 32) | (uintptr_t)low;
    KushTask *t = (KushTask *)pointer;
    kush_current = t;
    ((void (*)(uint64_t, uint64_t, uint64_t))(uintptr_t)t->wrapper)(
        t->code, t->env, (uint64_t)(uintptr_t)t->result);
    t->completed = (t->cancelled && !t->preserve) ? 0 : 1;
    t->state = KUSH_FINISHED;
    if (t->waiter != NULL) {
        t->waiter->state = KUSH_READY;
        kush_ready_push((int)t->waiter->id);
        t->waiter = NULL;
    }
    swapcontext(&t->context, &kush_scheduler_context);
    abort();
}
uint64_t kush_task_join(uint64_t handle, void *out) {
    if (!kush_initialized || handle == 0) kush_panic();
    int id = (int)(handle - 1);
    if (id <= 0 || id >= kush_task_count || kush_tasks[id] == NULL) kush_panic();
    KushTask *t = kush_tasks[id];
    if (t->joined || t == kush_current) kush_panic();
    while (t->state != KUSH_FINISHED) {
        kush_current->state = KUSH_BLOCKED;
        t->waiter = kush_current;
        swapcontext(&kush_current->context, &kush_scheduler_context);
    }
    int completed = t->completed;
    if (out == NULL && t->preserve) kush_panic();
    if (out != NULL) {
        memcpy(out, t->result, t->result_size);
    } else if (t->drop != NULL) {
        t->drop(t->result);
    }
    t->joined = 1;
    kush_tasks[id] = NULL;
    kush_free((uint64_t)(uintptr_t)t->result);
    kush_stack_free(t->stack_base, t->stack_total);
    kush_free((uint64_t)(uintptr_t)t);
    return completed ? 0 : 1;
}
uint64_t kush_task_yield(void) {
    kush_task_init();
    KushTask *t = kush_current;
    t->state = KUSH_READY;
    kush_ready_push((int)t->id);
    swapcontext(&t->context, &kush_scheduler_context);
    return (uint64_t)(t->cancelled != 0);
}
uint64_t kush_task_check_cancel(void) {
    if (!kush_initialized || kush_current == NULL) return 0;
    return (uint64_t)(kush_current->cancelled != 0);
}
uint64_t kush_task_cancel(uint64_t *handle) {
    if (!kush_initialized || handle == NULL) return 0;
    uint64_t value = *handle;
    if (value == 0) return 0;
    int id = (int)(value - 1);
    if (id <= 0 || id >= kush_task_count || kush_tasks[id] == NULL) return 0;
    KushTask *t = kush_tasks[id];
    if (!t->joined && t->state != KUSH_FINISHED) t->cancelled = 1;
    return 0;
}
uint64_t kush_task_scope_begin(void) {
    kush_task_init();
    if (kush_current->scope_depth >= KUSH_MAX_SCOPES) kush_panic();
    kush_current->scope_counts[kush_current->scope_depth] = 0;
    ++kush_current->scope_depth;
    return 0;
}
uint64_t kush_task_cancel_scope(void) {
    if (!kush_initialized || kush_current == NULL || kush_current->scope_depth == 0) return 0;
    int depth = kush_current->scope_depth - 1;
    int count = kush_current->scope_counts[depth];
    for (int i = 0; i < count; ++i) {
        int id = (int)kush_current->scope_ids[depth][i];
        if (id > 0 && id < kush_task_count && kush_tasks[id] != NULL &&
            !kush_tasks[id]->joined && kush_tasks[id]->state != KUSH_FINISHED) {
            kush_tasks[id]->cancelled = 1;
        }
    }
    return 0;
}
uint64_t kush_task_scope_end(void) {
    if (!kush_initialized || kush_current->scope_depth == 0) kush_panic();
    --kush_current->scope_depth;
    int depth = kush_current->scope_depth;
    int count = kush_current->scope_counts[depth];
    for (int i = 0; i < count; ++i) {
        int id = (int)kush_current->scope_ids[depth][i];
        if (id > 0 && id < kush_task_count && kush_tasks[id] != NULL &&
            !kush_tasks[id]->joined) {
            (void)kush_task_join((uint64_t)(id + 1), NULL);
        }
    }
    return 0;
}
static void kush_task_finish(void) {
    if (!kush_initialized) return;
    for (int i = 1; i < kush_task_count; ++i) {
        if (kush_tasks[i] != NULL) kush_panic();
    }
    KushTask *root = kush_tasks[0];
    kush_tasks[0] = NULL;
    kush_free((uint64_t)(uintptr_t)root);
    kush_stack_free(kush_scheduler_stack, kush_scheduler_stack_total);
    kush_scheduler_stack = NULL;
    kush_initialized = 0;
    kush_current = NULL;
    kush_task_count = 0;
}
int main(void) {
    /* Broken pipes become recoverable EPIPE results instead of process signals. */
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) kush_panic();
    /* Formatting and parse-back must never depend on the host locale. */
    if (setlocale(LC_NUMERIC, "C") == NULL) kush_panic();
#ifdef KUSH_HAS_TASKS
    kush_task_init();
#endif
    int64_t result = kush_entry();
    kush_task_finish();
    /* Retained pool storage is physical only; release it before the live
       allocation check so a normal exit owns nothing either way. */
    kush_pool_drain();
#ifdef KUSH_STATS
    {
        char line[256];
        int length = snprintf(line, sizeof(line),
            "allocation-stats: allocations=%llu deallocations=%llu peak-live=%llu buffer-growths=%llu reuses=%llu fusions=%lld\n",
            (unsigned long long)kush_allocations, (unsigned long long)kush_deallocations,
            (unsigned long long)kush_peak_live, (unsigned long long)kush_buffer_growths,
            (unsigned long long)kush_reuses, (long long)KUSH_FUSION_COUNT);
        if (length > 0) (void)write(2, line, (size_t)(length < (int)sizeof(line) ? length : (int)sizeof(line) - 1));
    }
    /* Opt-in native-only allocator observation. It is guarded by both the
       stats build and this environment variable, so the stable one-line
       allocation-stats interface never changes by default. */
    if (getenv("KUSH_ALLOCATOR_POOL_STATS") != NULL) {
        char line[256];
        int length = snprintf(line, sizeof(line),
            "allocator-pool: hits=%llu misses=%llu retains=%llu releases=%llu drained=%llu retained-bytes=%llu peak-retained-bytes=%llu\n",
            (unsigned long long)kush_pool_hits, (unsigned long long)kush_pool_misses,
            (unsigned long long)kush_pool_retains, (unsigned long long)kush_pool_releases,
            (unsigned long long)kush_pool_drains, (unsigned long long)kush_pool_retained,
            (unsigned long long)kush_pool_peak_retained);
        if (length > 0) (void)write(2, line, (size_t)(length < (int)sizeof(line) ? length : (int)sizeof(line) - 1));
    }
#endif
    if (kush_live_allocations != 0) {
        static const char message[] = "panic: live owning allocations after normal exit\n";
        (void)write(2, message, sizeof(message)-1); abort();
    }
    return (int)((uint64_t)result & UINT64_C(255));
}
"#;

/// Compile and link atomically in the output's directory. No shell expansion or
/// user-supplied flags; a failed build leaves the previous output intact.
pub fn build(program: &Executable, output: &Path) -> Result<()> {
    build_with_stats(program, output, false)
}

/// Build an executable that reports allocation diagnostics to stderr on a
/// normal exit. The program's own stdout and exit status are unchanged.
pub fn build_with_stats(program: &Executable, output: &Path, stats: bool) -> Result<()> {
    let object = object(program)?;
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let scratch = Scratch::new(parent)?;
    let object_path = scratch.path.join("program.o");
    let runtime_path = scratch.path.join("runtime.c");
    let binary_path = scratch.path.join("program");
    fs::write(&object_path, object).map_err(error)?;
    fs::write(&runtime_path, RUNTIME).map_err(error)?;
    let mut command = Command::new("cc");
    command
        .arg("-std=c11")
        .arg("-O2")
        .arg(&object_path)
        .arg(&runtime_path)
        .arg("-o")
        .arg(&binary_path)
        .arg("-lm");
    if program.uses_tasks {
        command.arg("-DKUSH_HAS_TASKS=1");
    }
    if stats {
        command
            .arg("-DKUSH_STATS=1")
            .arg(format!("-DKUSH_FUSION_COUNT={}", program.fusion_count()));
    }
    let result = command
        .output()
        .map_err(|e| error(format!("could not start the native linker 'cc': {e}")))?;
    if !result.status.success() {
        return Err(error(format!(
            "native link failed: {}",
            String::from_utf8_lossy(&result.stderr)
        )));
    }
    fs::rename(binary_path, output).map_err(|e| {
        error(format!(
            "cannot install executable '{}': {e}",
            output.display()
        ))
    })
}

/// Scratch ownership is local to this process. Existing directories are never
/// reused or deleted; create_dir is the atomic collision check.
pub struct Scratch {
    path: PathBuf,
}
impl Scratch {
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn new(parent: &Path) -> Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        for _ in 0..100 {
            let path = parent.join(format!(
                ".kush-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let mut directory = fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                directory.mode(0o700);
            }
            match directory.create(&path) {
                Ok(()) => return Ok(Self { path }),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => return Err(error(format!("cannot create build directory: {e}"))),
            }
        }
        Err(error("could not create a unique build directory"))
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn object(program: &Executable) -> Result<Vec<u8>> {
    if !cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        return Err(error(
            "the first native backend supports Linux x86-64 hosts only",
        ));
    }
    let entry = program.entry()?;
    let mut flags = settings::builder();
    flags.set("is_pic", "true").map_err(error)?;
    let isa = cranelift_native::builder_with_options(false)
        .map_err(error)?
        .finish(settings::Flags::new(flags))
        .map_err(error)?;
    let mut module =
        ObjectModule::new(ObjectBuilder::new(isa, "kush", default_libcall_names()).map_err(error)?);
    let mut print_sig = module.make_signature();
    print_sig.params.push(AbiParam::new(I64));
    print_sig.returns.push(AbiParam::new(I64));
    let print = module
        .declare_function("kush_print_i64", Linkage::Import, &print_sig)
        .map_err(error)?;
    let print_u64 = module
        .declare_function("kush_print_u64", Linkage::Import, &print_sig)
        .map_err(error)?;
    let print_f64 = module
        .declare_function("kush_print_f64", Linkage::Import, &print_sig)
        .map_err(error)?;
    let print_f32 = module
        .declare_function("kush_print_f32", Linkage::Import, &print_sig)
        .map_err(error)?;
    let mut two_sig = module.make_signature();
    two_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    two_sig.returns.push(AbiParam::new(I64));
    let float_from_int = module
        .declare_function("kush_float_from_int", Linkage::Import, &two_sig)
        .map_err(error)?;
    let float_to_int = module
        .declare_function("kush_float_to_int", Linkage::Import, &two_sig)
        .map_err(error)?;
    let float_int_present = module
        .declare_function("kush_float_int_present", Linkage::Import, &two_sig)
        .map_err(error)?;
    let mut rem_sig = module.make_signature();
    rem_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    rem_sig.returns.push(AbiParam::new(I64));
    let float_rem = module
        .declare_function("kush_float_rem", Linkage::Import, &rem_sig)
        .map_err(error)?;
    let mut three_sig = module.make_signature();
    three_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    three_sig.returns.push(AbiParam::new(I64));
    let int_exact_in_float = module
        .declare_function("kush_int_exact_in_float", Linkage::Import, &three_sig)
        .map_err(error)?;
    let panic_sig = module.make_signature();
    let panic = module
        .declare_function("kush_panic", Linkage::Import, &panic_sig)
        .map_err(error)?;
    let mut alloc_sig = module.make_signature();
    alloc_sig.params.push(AbiParam::new(I64));
    alloc_sig.returns.push(AbiParam::new(I64));
    let allocate = module
        .declare_function("kush_alloc", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let try_allocate = module
        .declare_function("kush_try_alloc", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let mut grow_sig = module.make_signature();
    grow_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    grow_sig.returns.push(AbiParam::new(I64));
    let grow = module
        .declare_function("kush_grow", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let try_grow = module
        .declare_function("kush_try_grow", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let try_bytes_with_capacity = module
        .declare_function("kush_try_bytes_with_capacity", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let mut free_sig = module.make_signature();
    free_sig.params.push(AbiParam::new(I64));
    let free = module
        .declare_function("kush_free", Linkage::Import, &free_sig)
        .map_err(error)?;
    let mut arena_new_sig = module.make_signature();
    arena_new_sig.returns.push(AbiParam::new(I64));
    let arena_new = module
        .declare_function("kush_arena_new", Linkage::Import, &arena_new_sig)
        .map_err(error)?;
    let arena_new_with_strategy = module
        .declare_function("kush_arena_new_with_strategy", Linkage::Import, &alloc_sig)
        .map_err(error)?;
    let arena_alloc = module
        .declare_function("kush_arena_alloc", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let arena_try_alloc = module
        .declare_function("kush_arena_try_alloc", Linkage::Import, &grow_sig)
        .map_err(error)?;
    let arena_release = module
        .declare_function("kush_arena_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let arena_box_release = module
        .declare_function("kush_arena_box_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let mut alloc_block_sig = module.make_signature();
    alloc_block_sig
        .params
        .extend((0..3).map(|_| AbiParam::new(I64)));
    alloc_block_sig.returns.push(AbiParam::new(I64));
    let alloc_block = module
        .declare_function("kush_alloc_block", Linkage::Import, &alloc_block_sig)
        .map_err(error)?;
    let alloc_block_try = module
        .declare_function("kush_alloc_block_try", Linkage::Import, &alloc_block_sig)
        .map_err(error)?;
    let mut alloc_unary_sig = module.make_signature();
    alloc_unary_sig.params.push(AbiParam::new(I64));
    alloc_unary_sig.returns.push(AbiParam::new(I64));
    let alloc_block_data = module
        .declare_function("kush_alloc_block_data", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let alloc_box_create = module
        .declare_function("kush_alloc_box_create", Linkage::Import, &alloc_block_sig)
        .map_err(error)?;
    let alloc_box_payload = module
        .declare_function("kush_alloc_box_payload", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let alloc_box_release = module
        .declare_function("kush_alloc_box_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let mut alloc_vec_create_sig = module.make_signature();
    alloc_vec_create_sig
        .params
        .extend((0..4).map(|_| AbiParam::new(I64)));
    alloc_vec_create_sig.returns.push(AbiParam::new(I64));
    let alloc_vec_create = module
        .declare_function(
            "kush_alloc_vec_create",
            Linkage::Import,
            &alloc_vec_create_sig,
        )
        .map_err(error)?;
    let mut alloc_vec_push_sig = module.make_signature();
    alloc_vec_push_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    alloc_vec_push_sig.returns.push(AbiParam::new(I64));
    let alloc_vec_push = module
        .declare_function("kush_alloc_vec_push", Linkage::Import, &alloc_vec_push_sig)
        .map_err(error)?;
    let alloc_vec_len = module
        .declare_function("kush_alloc_vec_len", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let mut alloc_vec_get_sig = module.make_signature();
    alloc_vec_get_sig
        .params
        .extend((0..3).map(|_| AbiParam::new(I64)));
    let alloc_vec_get = module
        .declare_function("kush_alloc_vec_get", Linkage::Import, &alloc_vec_get_sig)
        .map_err(error)?;
    let mut alloc_vec_set_sig = module.make_signature();
    alloc_vec_set_sig
        .params
        .extend((0..4).map(|_| AbiParam::new(I64)));
    alloc_vec_set_sig.returns.push(AbiParam::new(I64));
    let alloc_vec_set = module
        .declare_function("kush_alloc_vec_set", Linkage::Import, &alloc_vec_set_sig)
        .map_err(error)?;
    let alloc_vec_clear = module
        .declare_function("kush_alloc_vec_clear", Linkage::Import, &free_sig)
        .map_err(error)?;
    let alloc_vec_data = module
        .declare_function("kush_alloc_vec_data", Linkage::Import, &alloc_unary_sig)
        .map_err(error)?;
    let alloc_vec_release = module
        .declare_function("kush_alloc_vec_release", Linkage::Import, &free_sig)
        .map_err(error)?;
    let alloc_ops = AllocOps {
        block: alloc_block,
        block_try: alloc_block_try,
        block_data: alloc_block_data,
        box_create: alloc_box_create,
        box_payload: alloc_box_payload,
        box_release: alloc_box_release,
        vec_create: alloc_vec_create,
        vec_push: alloc_vec_push,
        vec_len: alloc_vec_len,
        vec_get: alloc_vec_get,
        vec_set: alloc_vec_set,
        vec_clear: alloc_vec_clear,
        vec_data: alloc_vec_data,
        vec_release: alloc_vec_release,
    };
    let mut restride_sig = module.make_signature();
    restride_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    restride_sig.returns.push(AbiParam::new(I64));
    let vec_restride = module
        .declare_function("kush_vec_restride", Linkage::Import, &restride_sig)
        .map_err(error)?;
    let mut reuse_sig = module.make_signature();
    reuse_sig.returns.push(AbiParam::new(I64));
    let note_reuse = module
        .declare_function("kush_note_reuse", Linkage::Import, &reuse_sig)
        .map_err(error)?;
    let mut from_sig = module.make_signature();
    from_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    from_sig.returns.push(AbiParam::new(I64));
    let bytes_from = module
        .declare_function("kush_bytes_from", Linkage::Import, &from_sig)
        .map_err(error)?;
    let mut bytes_ops = BTreeMap::new();
    for op in BytesOp::ALL {
        let count = if matches!(op, BytesOp::Get | BytesOp::Push | BytesOp::PushReserved) {
            2
        } else {
            1
        };
        let mut sig = module.make_signature();
        sig.params.extend((0..count).map(|_| AbiParam::new(I64)));
        sig.returns.push(AbiParam::new(I64));
        bytes_ops.insert(
            op,
            module
                .declare_function(op.symbol(), Linkage::Import, &sig)
                .map_err(error)?,
        );
    }
    let mut string_sig = module.make_signature();
    string_sig.params.push(AbiParam::new(I64));
    string_sig.returns.push(AbiParam::new(I64));
    let string_validate = module
        .declare_function("kush_utf8_validate", Linkage::Import, &string_sig)
        .map_err(error)?;
    let string_scalar_len = module
        .declare_function("kush_utf8_scalar_len", Linkage::Import, &string_sig)
        .map_err(error)?;
    let mut scalar_at_sig = module.make_signature();
    scalar_at_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    scalar_at_sig.returns.push(AbiParam::new(I64));
    let string_scalar_at = module
        .declare_function("kush_utf8_scalar_at", Linkage::Import, &scalar_at_sig)
        .map_err(error)?;
    let mut str_range_sig = module.make_signature();
    str_range_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    str_range_sig.returns.push(AbiParam::new(I64));
    let str_scalar_len = module
        .declare_function("kush_str_scalar_len", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let str_to_string = module
        .declare_function("kush_str_to_string", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let mut str_index_sig = module.make_signature();
    str_index_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    str_index_sig.returns.push(AbiParam::new(I64));
    let str_byte_at = module
        .declare_function("kush_str_byte_at", Linkage::Import, &str_index_sig)
        .map_err(error)?;
    let str_scalar_at = module
        .declare_function("kush_str_scalar_at", Linkage::Import, &str_index_sig)
        .map_err(error)?;
    let mut vec_ops = BTreeMap::new();
    for (op, name, params, returns) in [
        (VecOp::WithCapacity, "kush_vec_with_capacity", 2, true),
        (VecOp::Reserve, "kush_vec_reserve", 2, true),
        (
            VecOp::TryReserve {
                ok_tag: 0,
                err_tag: 0,
            },
            "kush_vec_try_reserve",
            2,
            true,
        ),
        (VecOp::Len, "kush_vec_len", 1, true),
        (VecOp::Get, "kush_vec_get", 3, false),
        (VecOp::Push, "kush_vec_push", 2, true),
        (VecOp::Set, "kush_vec_set", 4, true),
        (VecOp::PushBorrowed, "kush_vec_push", 2, true),
        (VecOp::SetBorrowed, "kush_vec_set", 4, true),
        (VecOp::ReserveBorrowed, "kush_vec_reserve", 2, true),
    ] {
        let mut sig = module.make_signature();
        sig.params.extend((0..params).map(|_| AbiParam::new(I64)));
        if returns {
            sig.returns.push(AbiParam::new(I64));
        }
        vec_ops.insert(
            op,
            module
                .declare_function(name, Linkage::Import, &sig)
                .map_err(error)?,
        );
    }
    let mut io_sig = module.make_signature();
    io_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    io_sig.returns.push(AbiParam::new(I64));
    let read_all = module
        .declare_function("kush_io_read_all", Linkage::Import, &io_sig)
        .map_err(error)?;
    let read_line = module
        .declare_function("kush_io_read_line", Linkage::Import, &io_sig)
        .map_err(error)?;
    let read_chunk = module
        .declare_function("kush_io_read_chunk", Linkage::Import, &io_sig)
        .map_err(error)?;
    let write = module
        .declare_function("kush_io_write", Linkage::Import, &io_sig)
        .map_err(error)?;
    let mut task_spawn_sig = module.make_signature();
    task_spawn_sig
        .params
        .extend((0..6).map(|_| AbiParam::new(I64)));
    task_spawn_sig.returns.push(AbiParam::new(I64));
    let task_spawn = module
        .declare_function("kush_task_spawn", Linkage::Import, &task_spawn_sig)
        .map_err(error)?;
    let mut task_join_sig = module.make_signature();
    task_join_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    task_join_sig.returns.push(AbiParam::new(I64));
    let task_join = module
        .declare_function("kush_task_join", Linkage::Import, &task_join_sig)
        .map_err(error)?;
    let mut task_cancel_sig = module.make_signature();
    task_cancel_sig.params.push(AbiParam::new(I64));
    task_cancel_sig.returns.push(AbiParam::new(I64));
    let task_cancel = module
        .declare_function("kush_task_cancel", Linkage::Import, &task_cancel_sig)
        .map_err(error)?;
    let mut task_unary_sig = module.make_signature();
    task_unary_sig.returns.push(AbiParam::new(I64));
    let task_yield = module
        .declare_function("kush_task_yield", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_check_cancel = module
        .declare_function("kush_task_check_cancel", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_scope_begin = module
        .declare_function("kush_task_scope_begin", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_cancel_scope = module
        .declare_function("kush_task_cancel_scope", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let task_scope_end = module
        .declare_function("kush_task_scope_end", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let mut handler_depth_sig = module.make_signature();
    handler_depth_sig.returns.push(AbiParam::new(I64));
    let handler_depth = module
        .declare_function("kush_handler_depth", Linkage::Import, &handler_depth_sig)
        .map_err(error)?;
    let mut handler_restore_sig = module.make_signature();
    handler_restore_sig.params.push(AbiParam::new(I64));
    let handler_restore = module
        .declare_function(
            "kush_handler_restore",
            Linkage::Import,
            &handler_restore_sig,
        )
        .map_err(error)?;
    let mut handler_push_sig = module.make_signature();
    handler_push_sig
        .params
        .extend((0..3).map(|_| AbiParam::new(I64)));
    let handler_push = module
        .declare_function("kush_handler_push", Linkage::Import, &handler_push_sig)
        .map_err(error)?;
    let handler_pop = module
        .declare_function("kush_handler_pop", Linkage::Import, &task_unary_sig)
        .map_err(error)?;
    let mut handler_lookup_sig = module.make_signature();
    handler_lookup_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    handler_lookup_sig.returns.push(AbiParam::new(I64));
    let handler_lookup = module
        .declare_function("kush_handler_lookup", Linkage::Import, &handler_lookup_sig)
        .map_err(error)?;
    let mut literal_data = BTreeMap::new();
    let mut literals = Vec::new();
    for f in &program.functions {
        collect_literals(&f.body, &mut literals);
    }
    for (index, (start, bytes)) in literals.into_iter().enumerate() {
        let id = module
            .declare_data(
                &format!("kush_literal_{index}"),
                Linkage::Local,
                false,
                false,
            )
            .map_err(error)?;
        let mut desc = DataDescription::new();
        desc.define(
            if bytes.is_empty() {
                vec![0]
            } else {
                bytes.to_vec()
            }
            .into_boxed_slice(),
        );
        module.define_data(id, &desc).map_err(error)?;
        literal_data.insert(start, id);
    }
    let (drops, closure_drops) = synthesize_drops(
        &mut module,
        program,
        free,
        arena_release,
        arena_box_release,
        &alloc_ops,
    )?;
    let task_types = collect_task_types(program);
    let (task_wrappers, task_pointer_drops) =
        synthesize_task_wrappers(&mut module, program, &task_types, &drops)?;
    let mut ids = Vec::new();
    for (index, f) in program.functions.iter().enumerate() {
        let mut sig = module.make_signature();
        let erased_result = f.result_grade.is_some_and(Grade::is_zero);
        if erased_result {
            // A copyable `@[0]` result has no payload and no ABI return slot.
        } else if aggregate_result(program, f.result) {
            sig.params.push(AbiParam::new(I64));
        } else {
            sig.returns.push(AbiParam::new(I64));
        }
        let captures = f.closure.unwrap_or(0);
        if f.closure.is_some() {
            sig.params.push(AbiParam::new(I64));
        }
        for (index, local) in f.locals[captures..f.parameters].iter().enumerate() {
            let slot = captures + index;
            if f.parameter_grades
                .get(slot)
                .copied()
                .flatten()
                .is_some_and(Grade::is_zero)
            {
                // Grade-zero parameter: the argument is evaluated at the call
                // site but has no physical ABI slot.
                continue;
            }
            sig.params
                .extend((0..program.width(local.ty)).map(|_| AbiParam::new(I64)));
        }
        let name = if index == entry {
            "kush_entry".to_owned()
        } else {
            format!("kush_fn_{index}")
        };
        ids.push(
            module
                .declare_function(
                    &name,
                    if index == entry {
                        Linkage::Export
                    } else {
                        Linkage::Local
                    },
                    &sig,
                )
                .map_err(error)?,
        );
    }
    for (index, f) in program.functions.iter().enumerate() {
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(ids[index])
            .signature
            .clone();
        let mut function_context = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut context.func, &mut function_context);
        let mut g = Generator {
            builder,
            module: &mut module,
            ids: &ids,
            program,
            print,
            print_u64,
            print_f64,
            print_f32,
            float_from_int,
            int_exact_in_float,
            float_to_int,
            float_int_present,
            float_rem,
            panic,
            variables: Vec::new(),
            locations: Vec::new(),
            result: f.result,
            return_pointer: None,
            allocate,
            try_allocate,
            grow,
            try_grow,
            try_bytes_with_capacity,
            free,
            arena_new,
            arena_new_with_strategy,
            arena_alloc,
            arena_try_alloc,
            arena_box_release,
            alloc_ops: &alloc_ops,
            vec_restride,
            note_reuse,
            drops: &drops,
            tracked: vec![],
            function_index: index,
            bytes_from,
            read_all,
            read_line,
            read_chunk,
            write,
            bytes_ops: &bytes_ops,
            string_validate,
            string_scalar_len,
            string_scalar_at,
            str_scalar_len,
            str_byte_at,
            str_scalar_at,
            str_to_string,
            vec_ops: &vec_ops,
            literal_data: &literal_data,
            closure_drops: &closure_drops,
            task_spawn,
            task_join,
            task_cancel,
            task_yield,
            task_check_cancel,
            task_scope_begin,
            task_cancel_scope,
            task_scope_end,
            handler_depth,
            handler_restore,
            handler_push,
            handler_pop,
            handler_lookup,
            handler_base: Variable::from_u32(0),
            task_wrappers: &task_wrappers,
            task_pointer_drops: &task_pointer_drops,
            loops: Vec::new(),
        };
        let entry = g.builder.create_block();
        g.builder.append_block_params_for_function_params(entry);
        g.builder.switch_to_block(entry);
        let handler_base = g.builder.declare_var(I64);
        g.handler_base = handler_base;
        let base = g.runtime_call(g.handler_depth, &[]);
        g.builder.def_var(handler_base, base);
        for local in &f.locals {
            let variables = (0..program.width(local.ty))
                .map(|_| g.builder.declare_var(I64))
                .collect();
            g.variables.push(variables);
        }
        for local in &f.locals {
            let array = local
                .ty
                .layout()
                .is_some_and(|id| program.enums[id].array.is_some());
            // Nominal records are pinned for the whole function so a
            // call-scoped `&Record`/`&mut Record` can point at the same storage
            // the local reads and writes. Inline arrays keep their existing
            // pinning rule.
            let record = local.ty.layout().is_some_and(|id| program.enums[id].record);
            let object = matches!(local.ty, Type::Union(_) | Type::DynObj(_));
            // Owning handles are pinned too so an exclusive `&mut Box`/`&mut
            // Vec` can update the caller's slot in place, including after a
            // vector growth moves the allocation.
            let owner_handle = matches!(
                local.ty,
                Type::Box(_)
                    | Type::ArenaBox(_)
                    | Type::Arena
                    | Type::Bytes
                    | Type::String
                    | Type::Vec(_)
            );
            if array || record || object || owner_handle {
                let width = program.width(local.ty);
                let slot = g.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (width * 8) as u32,
                    3,
                ));
                let pointer = g.builder.ins().stack_addr(I64, slot, 0);
                for index in 0..width {
                    let zero = g.constant(0);
                    g.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                g.locations.push(Some(pointer));
            } else {
                g.locations.push(None);
            }
        }
        for ty in &f.resources {
            let active = g.builder.declare_var(ir::types::I8);
            let zero = g.builder.ins().iconst(ir::types::I8, 0);
            g.builder.def_var(active, zero);
            let mut words = Vec::new();
            for _ in 0..program.width(*ty) {
                let v = g.builder.declare_var(I64);
                let zero = g.constant(0);
                g.builder.def_var(v, zero);
                words.push(v);
            }
            g.tracked.push(Tracked {
                active,
                words,
                ty: *ty,
                location: None,
            });
        }
        let mut offset = 0;
        let erased_result = f.result_grade.is_some_and(Grade::is_zero);
        if !erased_result && aggregate_result(program, f.result) {
            g.return_pointer = Some(g.builder.block_params(entry)[0]);
            offset = 1;
        }
        let captures = f.closure.unwrap_or(0);
        if f.closure.is_some() {
            let environment = g.builder.block_params(entry)[offset];
            offset += 1;
            if captures != 0 {
                let mut capture_offset = 8i32;
                for i in 0..captures {
                    let width = g.variables[i].len();
                    let values = g.load_words(environment, capture_offset, width);
                    capture_offset += (width * 8) as i32;
                    g.assign(i, &values);
                    g.activate_local(i);
                }
                emit_drop(&mut g.builder, g.module, free, &[environment]);
            }
        }
        for i in captures..f.parameters {
            if f.parameter_grades
                .get(i)
                .copied()
                .flatten()
                .is_some_and(Grade::is_zero)
            {
                continue;
            }
            let width = g.variables[i].len();
            let values = g.builder.block_params(entry)[offset..offset + width].to_vec();
            g.assign(i, &values);
            g.activate_local(i);
            offset += width;
        }
        if let Some(value) = g.block(&f.body) {
            g.cleanup_all();
            if erased_result {
                // Preserve actual cleanup for a copyable erased result, then
                // return without an ABI payload.
                g.drop_value(f.result, &value);
                g.return_value(&[]);
            } else {
                g.return_value(&value);
            }
        }
        g.builder.seal_all_blocks();
        g.builder.finalize(g.module.target_config());
        module
            .define_function(ids[index], &mut context)
            .map_err(|e| {
                Diagnostic::new(
                    f.span,
                    format!(
                        "Cranelift verification/code generation failed in {}: {e:?}",
                        f.name
                    ),
                )
            })?;
    }
    module.finish().emit().map_err(error)
}
fn aggregate_result(program: &Executable, ty: Type) -> bool {
    ty.layout().is_some() || program.width(ty) > 1
}
fn collect_literals<'a>(block: &'a ex::Block, out: &mut Vec<(usize, &'a [u8])>) {
    for statement in &block.statements {
        match statement {
            ex::Statement::Let(_, value) | ex::Statement::Expr(value) => {
                collect_expr_literals(value, out)
            }
        }
    }
    if let Some(tail) = &block.tail {
        collect_expr_literals(tail, out);
    }
}
fn collect_expr_literals<'a>(expr: &'a Expr, out: &mut Vec<(usize, &'a [u8])>) {
    if let ExprKind::BytesLiteral(bytes) = &expr.kind {
        out.push((expr.span.start, bytes));
    }
    expr.for_each_child(&mut |child| collect_expr_literals(child, out));
}
fn emit_drop(
    builder: &mut FunctionBuilder<'_>,
    module: &mut ObjectModule,
    id: FuncId,
    values: &[Value],
) {
    let reference = module.declare_func_in_func(id, builder.func);
    builder.ins().call(reference, values);
}
/// Environment capture types introduced by checked coercions. A callable
/// field adapter stores its source callable in an owned environment exactly
/// like a capturing `FnValue`, so the native backend must synthesize the same
/// environment drop function for it.
fn collect_coercion_captures(coercion: &ex::Coercion, out: &mut Vec<Vec<Type>>) {
    match coercion {
        ex::Coercion::Callable {
            capture: Some(capture),
            ..
        } => out.push(vec![capture.full()]),
        ex::Coercion::Struct { kept, .. } => {
            for (_, _, nested) in kept {
                if let Some(nested) = nested {
                    collect_coercion_captures(nested, out);
                }
            }
        }
        _ => {}
    }
}
fn collect_closure_types(program: &Executable) -> Vec<Vec<Type>> {
    // Every expression position is visited through the exhaustive child walk,
    // so a capturing closure or callable adapter nested anywhere gets its
    // environment-drop function.
    fn walk(node: &Expr, out: &mut Vec<Vec<Type>>) {
        match &node.kind {
            ExprKind::FnValue { captures, .. } if !captures.is_empty() => out.push(
                captures
                    .iter()
                    .map(|capture| capture.ty.full())
                    .collect::<Vec<_>>(),
            ),
            // A callable field adapter owns its source callable in an
            // environment; record that capture type too.
            ExprKind::Coerce { coercion, .. } => collect_coercion_captures(coercion, out),
            _ => {}
        }
        node.for_each_child(&mut |child| walk(child, out));
    }
    let mut all = Vec::new();
    for function in &program.functions {
        for statement in &function.body.statements {
            match statement {
                ex::Statement::Let(_, value) | ex::Statement::Expr(value) => walk(value, &mut all),
            }
        }
        if let Some(tail) = &function.body.tail {
            walk(tail, &mut all);
        }
    }
    all.sort();
    all.dedup();
    all
}
/// Imported runtime helpers for checked user-allocator containers.
#[derive(Clone, Copy)]
struct AllocOps {
    block: FuncId,
    block_try: FuncId,
    block_data: FuncId,
    box_create: FuncId,
    box_payload: FuncId,
    box_release: FuncId,
    vec_create: FuncId,
    vec_push: FuncId,
    vec_len: FuncId,
    vec_get: FuncId,
    vec_set: FuncId,
    vec_clear: FuncId,
    vec_data: FuncId,
    vec_release: FuncId,
}
type DropTables = (BTreeMap<Type, FuncId>, BTreeMap<Vec<Type>, FuncId>);
fn synthesize_drops(
    module: &mut ObjectModule,
    program: &Executable,
    free: FuncId,
    arena_release: FuncId,
    arena_box_release: FuncId,
    alloc_ops: &AllocOps,
) -> Result<DropTables> {
    let mut types = (0..program.pointees.len())
        .map(Type::Box)
        .chain((0..program.pointees.len()).map(Type::ArenaBox))
        .chain((0..program.pointees.len()).map(Type::AllocBox))
        .chain((0..program.pointees.len()).map(Type::AllocVec))
        .chain((0..program.pointees.len()).map(Type::Vec))
        .chain((0..program.pointees.len()).map(Type::Task))
        .chain([Type::Arena])
        .chain((0..program.enums.len()).map(Type::Enum))
        .chain((0..program.unions.len()).map(Type::Union))
        .chain((0..program.dyn_object_names.len()).map(Type::DynObj))
        .chain(
            (0..program.function_types.len())
                .filter(|id| program.function_types[*id].once)
                .map(Type::Once),
        )
        .chain([Type::Bytes, Type::String])
        .filter(|ty| program.owns(*ty))
        .collect::<Vec<_>>();
    types.sort();
    types.dedup();
    let mut ids = BTreeMap::new();
    for (i, ty) in types.iter().enumerate() {
        let mut signature = module.make_signature();
        signature
            .params
            .extend((0..program.width(*ty)).map(|_| AbiParam::new(I64)));
        ids.insert(
            *ty,
            module
                .declare_function(&format!("kush_drop_{i}"), Linkage::Local, &signature)
                .map_err(error)?,
        );
    }
    // One environment drop function per distinct captured-type list. The
    // environment header stores this address, so an owning closure type does
    // not need capture metadata after checking.
    let closure_types = collect_closure_types(program);
    let mut closure_ids = BTreeMap::new();
    for (i, captures) in closure_types.iter().enumerate() {
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(I64));
        closure_ids.insert(
            captures.clone(),
            module
                .declare_function(
                    &format!("kush_closure_drop_{i}"),
                    Linkage::Local,
                    &signature,
                )
                .map_err(error)?,
        );
    }
    for ty in types {
        let id = ids[&ty];
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(id)
            .signature
            .clone();
        let mut fc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let args = builder.block_params(entry).to_vec();
        match ty {
            Type::Bytes | Type::String => {
                emit_drop(&mut builder, module, free, &args);
                builder.ins().return_(&[]);
            }
            Type::Box(index) | Type::ArenaBox(index) => {
                let pointee = program.pointees[index];
                if program.owns(pointee) {
                    let fields = (0..program.width(pointee))
                        .map(|i| {
                            builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                args[0],
                                (i * 8) as i32,
                            )
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&pointee.full()], &fields);
                }
                if matches!(ty, Type::ArenaBox(_)) {
                    emit_drop(&mut builder, module, arena_box_release, &args);
                } else {
                    emit_drop(&mut builder, module, free, &args);
                }
                builder.ins().return_(&[]);
            }
            Type::Arena => {
                emit_drop(&mut builder, module, arena_release, &args);
                builder.ins().return_(&[]);
            }
            Type::DynObj(object) => {
                // args = [member identifier, payload pointer]. The identifier
                // selects the concrete payload type; its drop runs in place,
                // then the payload allocation is released exactly once.
                let members = program.dyn_members.get(object).cloned().unwrap_or_default();
                for (index, entry) in members.iter().enumerate() {
                    let hit = builder.create_block();
                    let next = builder.create_block();
                    let condition = builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, args[0], index as i64);
                    builder.ins().brif(condition, hit, &[], next, &[]);
                    builder.switch_to_block(hit);
                    if program.owns(entry.member) {
                        let fields = (0..program.width(entry.member))
                            .map(|i| {
                                builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    args[1],
                                    (i * 8) as i32,
                                )
                            })
                            .collect::<Vec<_>>();
                        emit_drop(&mut builder, module, ids[&entry.member.full()], &fields);
                    }
                    emit_drop(&mut builder, module, free, &[args[1]]);
                    builder.ins().return_(&[]);
                    builder.switch_to_block(next);
                }
                // No registered member can reach here, but release the
                // payload allocation defensively rather than leaking it.
                emit_drop(&mut builder, module, free, &[args[1]]);
                builder.ins().return_(&[]);
            }
            Type::AllocBox(index) => {
                let pointee = program.pointees[index];
                let payload_function =
                    module.declare_func_in_func(alloc_ops.box_payload, builder.func);
                let payload_call = builder.ins().call(payload_function, &[args[0]]);
                let data = builder.inst_results(payload_call)[0];
                if program.owns(pointee) {
                    let fields = (0..program.width(pointee))
                        .map(|i| {
                            builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), data, (i * 8) as i32)
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&pointee.full()], &fields);
                }
                emit_drop(&mut builder, module, alloc_ops.box_release, &args);
                builder.ins().return_(&[]);
            }
            Type::AllocVec(index) => {
                let element = program.pointees[index];
                if program.owns(element) {
                    let width = program.width(element);
                    let length = builder.ins().load(I64, ir::MemFlagsData::new(), args[0], 0);
                    let data_function =
                        module.declare_func_in_func(alloc_ops.vec_data, builder.func);
                    let data_call = builder.ins().call(data_function, &[args[0]]);
                    let data = builder.inst_results(data_call)[0];
                    let head = builder.create_block();
                    let body = builder.create_block();
                    let done = builder.create_block();
                    builder.append_block_param(head, I64);
                    let zero = builder.ins().iconst(I64, 0);
                    builder.ins().jump(head, &[zero.into()]);
                    builder.switch_to_block(head);
                    let i = builder.block_params(head)[0];
                    let more = builder.ins().icmp(IntCC::UnsignedLessThan, i, length);
                    builder.ins().brif(more, body, &[], done, &[]);
                    builder.switch_to_block(body);
                    let stride = builder.ins().imul_imm_s(i, (width * 8) as i64);
                    let base = builder.ins().iadd(data, stride);
                    let fields = (0..width)
                        .map(|j| {
                            builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), base, (j * 8) as i32)
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&element.full()], &fields);
                    let next = builder.ins().iadd_imm_s(i, 1);
                    builder.ins().jump(head, &[next.into()]);
                    builder.switch_to_block(done);
                }
                emit_drop(&mut builder, module, alloc_ops.vec_release, &args);
                builder.ins().return_(&[]);
            }
            Type::Vec(index) => {
                let element = program.pointees[index];
                if program.owns(element) {
                    // for (i = 0; i < length; i++) drop(data[i])
                    let width = program.width(element);
                    let length = builder.ins().load(I64, ir::MemFlagsData::new(), args[0], 0);
                    let head = builder.create_block();
                    let body = builder.create_block();
                    let done = builder.create_block();
                    builder.append_block_param(head, I64);
                    let zero = builder.ins().iconst(I64, 0);
                    builder.ins().jump(head, &[zero.into()]);
                    builder.switch_to_block(head);
                    let i = builder.block_params(head)[0];
                    let more = builder.ins().icmp(IntCC::UnsignedLessThan, i, length);
                    builder.ins().brif(more, body, &[], done, &[]);
                    builder.switch_to_block(body);
                    let stride = builder.ins().imul_imm_s(i, (width * 8) as i64);
                    let base = builder.ins().iadd(args[0], stride);
                    let fields = (0..width)
                        .map(|k| {
                            builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                base,
                                (24 + k * 8) as i32,
                            )
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&element.full()], &fields);
                    let next = builder.ins().iadd_imm_s(i, 1);
                    builder.ins().jump(head, &[next.into()]);
                    builder.switch_to_block(done);
                }
                emit_drop(&mut builder, module, free, &args);
                builder.ins().return_(&[]);
            }
            Type::Enum(index) => {
                if let Some((element, capacity)) = program.enums[index].dynamic_array {
                    if program.owns(element) {
                        // The runtime length is word zero; fields at or beyond
                        // it are uninitialized and must never be interpreted.
                        // Words arrive as function arguments, so the capacity
                        // bound is expanded into a guard per slot instead of a
                        // dynamic index into SSA values.
                        let width = program.width(element);
                        let length = args[0];
                        for slot in (0..capacity).rev() {
                            let active = builder.ins().icmp_imm_s(
                                IntCC::UnsignedGreaterThan,
                                length,
                                slot as i64,
                            );
                            let body = builder.create_block();
                            let next = builder.create_block();
                            builder.ins().brif(active, body, &[], next, &[]);
                            builder.switch_to_block(body);
                            emit_drop(
                                &mut builder,
                                module,
                                ids[&element.full()],
                                &args[1 + slot * width..1 + (slot + 1) * width],
                            );
                            builder.ins().jump(next, &[]);
                            builder.switch_to_block(next);
                        }
                    }
                    builder.ins().return_(&[]);
                } else {
                    for (tag, variant) in program.enums[index].variants.iter().enumerate() {
                        let hit = builder.create_block();
                        let next = builder.create_block();
                        let condition = builder.ins().icmp_imm_s(IntCC::Equal, args[0], tag as i64);
                        builder.ins().brif(condition, hit, &[], next, &[]);
                        builder.switch_to_block(hit);
                        let mut offset = 1;
                        let mut fields = Vec::new();
                        for ty in &variant.fields {
                            fields.push((*ty, offset));
                            offset += program.width(*ty);
                        }
                        for (ty, offset) in fields.into_iter().rev() {
                            if program.owns(ty) {
                                emit_drop(
                                    &mut builder,
                                    module,
                                    ids[&ty.full()],
                                    &args[offset..offset + program.width(ty)],
                                );
                            }
                        }
                        builder.ins().return_(&[]);
                        builder.switch_to_block(next);
                    }
                    builder.ins().trap(TrapCode::unwrap_user(2));
                }
            }
            Type::Union(index) => {
                for (tag, member) in program.unions[index].members.iter().enumerate() {
                    let hit = builder.create_block();
                    let next = builder.create_block();
                    let condition = builder.ins().icmp_imm_s(IntCC::Equal, args[0], tag as i64);
                    builder.ins().brif(condition, hit, &[], next, &[]);
                    builder.switch_to_block(hit);
                    if program.owns(*member) {
                        emit_drop(
                            &mut builder,
                            module,
                            ids[&member.full()],
                            &args[1..1 + program.width(*member)],
                        );
                    }
                    builder.ins().return_(&[]);
                    builder.switch_to_block(next);
                }
                builder.ins().trap(TrapCode::unwrap_user(2));
            }
            Type::Once(_) => {
                // args = [code, environment]. A noncapturing function coerced to
                // once has a null environment and owns nothing.
                let environment = args[1];
                let present = builder.ins().icmp_imm_s(IntCC::NotEqual, environment, 0);
                let close = builder.create_block();
                let done = builder.create_block();
                builder.ins().brif(present, close, &[], done, &[]);
                builder.switch_to_block(close);
                let drop = builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), environment, 0);
                let signature = {
                    let mut signature = module.make_signature();
                    signature.params.push(AbiParam::new(I64));
                    signature
                };
                let signature = builder.import_signature(signature);
                builder.ins().call_indirect(signature, drop, &[environment]);
                builder.ins().return_(&[]);
                builder.switch_to_block(done);
                builder.ins().return_(&[]);
            }
            Type::Task(_) => {
                // A task handle owns no heap cell. Scope completion joins it.
                builder.ins().return_(&[]);
            }
            _ => unreachable!(),
        }
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module.define_function(id, &mut context).map_err(error)?;
    }
    for (captures, id) in closure_ids.clone() {
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(id)
            .signature
            .clone();
        let mut fc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let environment = builder.block_params(entry)[0];
        let mut positions = Vec::with_capacity(captures.len());
        let mut offset = 8;
        for ty in &captures {
            positions.push((*ty, offset));
            offset += (program.width(*ty) * 8) as i32;
        }
        for (ty, offset) in positions.into_iter().rev() {
            if program.owns(ty) {
                let values = (0..program.width(ty))
                    .map(|i| {
                        builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            environment,
                            offset + (i * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                emit_drop(&mut builder, module, ids[&ty.full()], &values);
            }
        }
        emit_drop(&mut builder, module, free, &[environment]);
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module.define_function(id, &mut context).map_err(error)?;
    }
    Ok((ids, closure_ids))
}
fn collect_task_types(program: &Executable) -> Vec<usize> {
    fn walk(node: &Expr, out: &mut Vec<usize>) {
        match &node.kind {
            ExprKind::TaskSpawn { body, .. } => {
                if let Type::Once(id) = body.ty {
                    out.push(id);
                }
                walk(body, out);
            }
            ExprKind::TaskScope { body, .. } => walk(body, out),
            ExprKind::TaskCancel(reference) => walk(reference, out),
            ExprKind::TaskJoin { task, .. } => walk(task, out),
            ExprKind::Block(block) => walk_block(block, out),
            ExprKind::HandlerPush { handler, body, .. } => {
                walk(handler, out);
                walk_block(body, out);
            }
            ExprKind::DynamicPerform {
                payload, resume, ..
            } => {
                walk(payload, out);
                walk(resume, out);
            }
            ExprKind::Unary(_, value)
            | ExprKind::Try { value, .. }
            | ExprKind::Return(value)
            | ExprKind::BoxNew(value)
            | ExprKind::BoxTake(value)
            | ExprKind::BoxRead(value)
            | ExprKind::ArenaBoxRead(value)
            | ExprKind::ArenaBoxTake(value)
            | ExprKind::Drop(value)
            | ExprKind::Project(value, _)
            | ExprKind::Coerce { value, .. }
            | ExprKind::Break(Some(value), _)
            | ExprKind::Assign(_, value) => walk(value, out),
            ExprKind::BoxWrite(reference, value) => {
                walk(reference, out);
                walk(value, out);
            }
            ExprKind::ArenaAlloc { arena, value } => {
                walk(arena, out);
                walk(value, out);
            }
            ExprKind::ArenaNewWith { strategy } => walk(strategy, out),
            ExprKind::ArenaTryAlloc { arena, value, .. } => {
                walk(arena, out);
                walk(value, out);
            }
            ExprKind::ArenaNew => {}
            ExprKind::RefAssign(reference, _, value) => {
                walk(reference, out);
                walk(value, out);
            }
            ExprKind::Loop(block) => walk_block(block, out),
            ExprKind::While(condition, block) => {
                walk(condition, out);
                walk_block(block, out);
            }
            ExprKind::BoxReuse { owner, payload } => {
                walk(owner, out);
                walk(payload, out);
            }
            ExprKind::VecMap {
                vector, callbacks, ..
            } => {
                walk(vector, out);
                for callback in callbacks {
                    walk(callback, out);
                }
            }
            ExprKind::BytesAt(a, b) | ExprKind::Binary(_, a, b) => {
                walk(a, out);
                walk(b, out);
            }
            ExprKind::Slice {
                base, start, end, ..
            } => {
                walk(base, out);
                if let Some(start) = start {
                    walk(start, out);
                }
                if let Some(end) = end {
                    walk(end, out);
                }
            }
            ExprKind::Call(_, arguments)
            | ExprKind::Construct {
                fields: arguments, ..
            } => {
                for argument in arguments {
                    walk(argument, out);
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                walk(callee, out);
                for argument in arguments {
                    walk(argument, out);
                }
            }
            ExprKind::FnValue { captures, .. } => {
                for capture in captures {
                    walk(capture, out);
                }
            }
            ExprKind::If(condition, yes, no) => {
                walk(condition, out);
                walk_block(yes, out);
                walk_block(no, out);
            }
            ExprKind::Match(value, arms) => {
                walk(value, out);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        walk(guard, out);
                    }
                    walk(&arm.body, out);
                }
            }
            _ => {}
        }
    }
    fn walk_block(block: &ex::Block, out: &mut Vec<usize>) {
        for statement in &block.statements {
            match statement {
                ex::Statement::Let(_, value) | ex::Statement::Expr(value) => walk(value, out),
            }
        }
        if let Some(tail) = &block.tail {
            walk(tail, out);
        }
    }
    let mut ids = Vec::new();
    for function in &program.functions {
        walk_block(&function.body, &mut ids);
    }
    ids.sort_unstable();
    ids.dedup();
    ids
}

/// Build the native task entry wrappers. A wrapper always has the C ABI
/// `(code, env, result_ptr) -> ()`, so the runtime can call a statically or
/// dynamically selected once callable without knowing its signature.
fn synthesize_task_wrappers(
    module: &mut ObjectModule,
    program: &Executable,
    types: &[usize],
    drops: &BTreeMap<Type, FuncId>,
) -> Result<(BTreeMap<usize, FuncId>, BTreeMap<Type, FuncId>)> {
    let mut pointer_drops = BTreeMap::new();
    for id in types {
        let result = program.function_types[*id].result;
        if program.owns(result) && !pointer_drops.contains_key(&result.full()) {
            let mut signature = module.make_signature();
            signature.params.push(AbiParam::new(I64));
            let function = module
                .declare_function(
                    &format!("kush_task_drop_{}", pointer_drops.len()),
                    Linkage::Local,
                    &signature,
                )
                .map_err(error)?;
            let mut context = module.make_context();
            context.func.signature = module
                .declarations()
                .get_function_decl(function)
                .signature
                .clone();
            let mut fc = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            let pointer = builder.block_params(entry)[0];
            let width = program.width(result);
            let words = (0..width)
                .map(|i| {
                    builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), pointer, (i * 8) as i32)
                })
                .collect::<Vec<_>>();
            emit_drop(&mut builder, module, drops[&result.full()], &words);
            builder.ins().return_(&[]);
            builder.seal_all_blocks();
            builder.finalize(module.target_config());
            module
                .define_function(function, &mut context)
                .map_err(error)?;
            pointer_drops.insert(result.full(), function);
        }
    }
    let mut wrappers = BTreeMap::new();
    for id in types {
        let signature = &program.function_types[*id];
        let result = signature.result;
        let aggregate = aggregate_result(program, result);
        let mut wrapper_signature = module.make_signature();
        wrapper_signature
            .params
            .extend((0..3).map(|_| AbiParam::new(I64)));
        let wrapper = module
            .declare_function(
                &format!("kush_task_wrapper_{id}"),
                Linkage::Local,
                &wrapper_signature,
            )
            .map_err(error)?;
        let mut context = module.make_context();
        context.func.signature = module
            .declarations()
            .get_function_decl(wrapper)
            .signature
            .clone();
        let mut fc = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut context.func, &mut fc);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        let params = builder.block_params(entry).to_vec();
        let (code, env, result_pointer) = (params[0], params[1], params[2]);
        let mut body_signature = module.make_signature();
        if aggregate {
            body_signature.params.push(AbiParam::new(I64));
        }
        body_signature.params.push(AbiParam::new(I64));
        if !aggregate {
            body_signature.returns.push(AbiParam::new(I64));
        }
        let body_signature = builder.import_signature(body_signature);
        let mut arguments = Vec::new();
        if aggregate {
            arguments.push(result_pointer);
        }
        arguments.push(env);
        let call = builder
            .ins()
            .call_indirect(body_signature, code, &arguments);
        if !aggregate {
            let value = builder.inst_results(call)[0];
            builder
                .ins()
                .store(ir::MemFlagsData::new(), value, result_pointer, 0);
        }
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module
            .define_function(wrapper, &mut context)
            .map_err(error)?;
        wrappers.insert(*id, wrapper);
    }
    Ok((wrappers, pointer_drops))
}
struct Tracked {
    active: Variable,
    words: Vec<Variable>,
    ty: Type,
    /// Stack storage for a pinned owning local. Reads of the tracked value at
    /// cleanup go through this location so an in-place `&mut` mutation is
    /// observed exactly once.
    location: Option<Value>,
}
type Words = Vec<Value>;
struct Generator<'a, 'b> {
    builder: FunctionBuilder<'a>,
    module: &'b mut ObjectModule,
    ids: &'b [FuncId],
    program: &'b Executable,
    print: FuncId,
    print_u64: FuncId,
    print_f64: FuncId,
    print_f32: FuncId,
    float_from_int: FuncId,
    int_exact_in_float: FuncId,
    float_to_int: FuncId,
    float_int_present: FuncId,
    float_rem: FuncId,
    panic: FuncId,
    variables: Vec<Vec<Variable>>,
    /// Stack storage for inline-array locals so slice views can alias the real
    /// local storage (needed for `&mut [T]` write-back).
    locations: Vec<Option<Value>>,
    result: Type,
    return_pointer: Option<Value>,
    bytes_from: FuncId,
    read_all: FuncId,
    read_line: FuncId,
    read_chunk: FuncId,
    write: FuncId,
    bytes_ops: &'b BTreeMap<BytesOp, FuncId>,
    string_validate: FuncId,
    string_scalar_len: FuncId,
    string_scalar_at: FuncId,
    str_scalar_len: FuncId,
    str_byte_at: FuncId,
    str_scalar_at: FuncId,
    str_to_string: FuncId,
    vec_ops: &'b BTreeMap<VecOp, FuncId>,
    /// (continue target, break target, break carries a value, handler depth at
    /// loop entry). Break/continue restore the handler depth so a dynamic
    /// handler frame inside the body cannot survive an early loop exit.
    loops: Vec<(ir::Block, ir::Block, bool, Variable)>,
    literal_data: &'b BTreeMap<usize, DataId>,
    allocate: FuncId,
    try_allocate: FuncId,
    grow: FuncId,
    try_grow: FuncId,
    try_bytes_with_capacity: FuncId,
    free: FuncId,
    arena_new: FuncId,
    arena_new_with_strategy: FuncId,
    arena_alloc: FuncId,
    arena_try_alloc: FuncId,
    arena_box_release: FuncId,
    alloc_ops: &'b AllocOps,
    vec_restride: FuncId,
    note_reuse: FuncId,
    drops: &'b BTreeMap<Type, FuncId>,
    closure_drops: &'b BTreeMap<Vec<Type>, FuncId>,
    task_spawn: FuncId,
    task_join: FuncId,
    task_cancel: FuncId,
    task_yield: FuncId,
    task_check_cancel: FuncId,
    task_scope_begin: FuncId,
    task_cancel_scope: FuncId,
    task_scope_end: FuncId,
    handler_depth: FuncId,
    handler_restore: FuncId,
    handler_push: FuncId,
    handler_pop: FuncId,
    handler_lookup: FuncId,
    /// Entry handler-stack depth for this function; every return restores it so
    /// an early `return` cannot leave a dynamic handler frame visible.
    handler_base: Variable,
    task_wrappers: &'b BTreeMap<usize, FuncId>,
    task_pointer_drops: &'b BTreeMap<Type, FuncId>,
    tracked: Vec<Tracked>,
    function_index: usize,
}
macro_rules! lower {
    ($e:expr) => {
        match $e {
            Some(v) => v,
            None => return None,
        }
    };
}
impl Generator<'_, '_> {
    fn track(&mut self, id: Option<usize>, values: &[Value]) {
        if let Some(id) = id {
            for (v, value) in self.tracked[id].words.iter().zip(values) {
                self.builder.def_var(*v, *value);
            }
            let one = self.builder.ins().iconst(ir::types::I8, 1);
            self.builder.def_var(self.tracked[id].active, one);
        }
    }
    fn deactivate(&mut self, id: Option<usize>) {
        if let Some(id) = id {
            let zero = self.builder.ins().iconst(ir::types::I8, 0);
            self.builder.def_var(self.tracked[id].active, zero);
        }
    }
    fn consume(&mut self, expr: &Expr) {
        self.deactivate(expr.resource);
    }
    /// A grade-zero binding is not materialized at runtime. Its initializer is
    /// still evaluated for strict effects, but no store, local resource, or
    /// read is emitted for the binding.
    fn erased_local(&self, slot: usize) -> bool {
        self.program.functions[self.function_index].locals[slot]
            .grade
            .is_some_and(Grade::is_zero)
    }
    fn activate_local(&mut self, slot: usize) {
        let location = self.locations[slot];
        let values = if let Some(pointer) = location {
            let width = self.variables[slot].len();
            self.load_words(pointer, 0, width)
        } else {
            self.variables[slot]
                .iter()
                .map(|v| self.builder.use_var(*v))
                .collect::<Vec<_>>()
        };
        let id = self.program.functions[self.function_index].local_resources[slot];
        self.track(id, &values);
        if let Some(id) = id {
            self.tracked[id].location = location;
        }
    }
    fn drop_value(&mut self, ty: Type, values: &[Value]) {
        if self.program.owns(ty) {
            emit_drop(
                &mut self.builder,
                self.module,
                self.drops[&ty.full()],
                &values[..self.program.width(ty)],
            );
        }
    }
    fn cleanup(&mut self, id: Option<usize>) {
        if let Some(id) = id {
            let active = self.builder.use_var(self.tracked[id].active);
            let yes = self.builder.create_block();
            let no = self.builder.create_block();
            self.builder.ins().brif(active, yes, &[], no, &[]);
            self.builder.switch_to_block(yes);
            self.deactivate(Some(id));
            let values = if let Some(pointer) = self.tracked[id].location {
                let width = self.program.width(self.tracked[id].ty);
                self.load_words(pointer, 0, width)
            } else {
                self.tracked[id]
                    .words
                    .iter()
                    .map(|v| self.builder.use_var(*v))
                    .collect::<Vec<_>>()
            };
            self.drop_value(self.tracked[id].ty, &values);
            self.jump(no, &[]);
            self.builder.switch_to_block(no);
        }
    }
    fn cleanup_all(&mut self) {
        for id in (0..self.tracked.len()).rev() {
            self.cleanup(Some(id));
        }
    }
    fn constant(&mut self, n: i64) -> Value {
        self.builder.ins().iconst(I64, n)
    }
    fn scalar(&mut self, expr: &Expr) -> Option<Value> {
        self.expr(expr).map(|values| values[0])
    }
    /// Interpret a one-word float representation as a hardware float value.
    fn float_value(&mut self, kind: FloatKind, bits: Value) -> Value {
        match kind {
            FloatKind::F32 => {
                let low = self.builder.ins().ireduce(ir::types::I32, bits);
                self.builder
                    .ins()
                    .bitcast(ir::types::F32, ir::MemFlagsData::new(), low)
            }
            FloatKind::F64 => {
                self.builder
                    .ins()
                    .bitcast(ir::types::F64, ir::MemFlagsData::new(), bits)
            }
        }
    }
    /// Store a hardware float back into its canonical one-word bit form.
    fn float_bits(&mut self, kind: FloatKind, value: Value) -> Value {
        match kind {
            FloatKind::F32 => {
                let low =
                    self.builder
                        .ins()
                        .bitcast(ir::types::I32, ir::MemFlagsData::new(), value);
                self.builder.ins().uextend(I64, low)
            }
            FloatKind::F64 => self
                .builder
                .ins()
                .bitcast(I64, ir::MemFlagsData::new(), value),
        }
    }
    fn float_binary(&mut self, kind: FloatKind, op: &Kind, a: Value, b: Value) -> Value {
        let comparison = match op {
            Kind::Lt => Some(FloatCC::LessThan),
            Kind::Le => Some(FloatCC::LessThanOrEqual),
            Kind::Gt => Some(FloatCC::GreaterThan),
            Kind::Ge => Some(FloatCC::GreaterThanOrEqual),
            Kind::EqEq => Some(FloatCC::Equal),
            Kind::Ne => Some(FloatCC::NotEqual),
            _ => None,
        };
        if let Some(condition) = comparison {
            let value = self.builder.ins().fcmp(condition, a, b);
            return self.builder.ins().uextend(I64, value);
        }
        let result = match op {
            Kind::Plus => self.builder.ins().fadd(a, b),
            Kind::Minus => self.builder.ins().fsub(a, b),
            Kind::Star => self.builder.ins().fmul(a, b),
            Kind::Slash => self.builder.ins().fdiv(a, b),
            Kind::Percent => {
                let is_f32 = self.constant(i64::from(matches!(kind, FloatKind::F32)));
                let a = self.float_bits(kind, a);
                let b = self.float_bits(kind, b);
                return self.runtime_call(self.float_rem, &[a, b, is_f32]);
            }
            _ => unreachable!("checked float operator"),
        };
        self.float_bits(kind, result)
    }
    /// Integer -> float payload bits, rounding to nearest-even.
    fn float_from_integer(&mut self, source: IntKind, target: FloatKind, value: Value) -> Value {
        let signed = self.constant(i64::from(source.signed()));
        let wide = self.runtime_call(self.float_from_int, &[value, signed]);
        match target {
            FloatKind::F64 => wide,
            FloatKind::F32 => {
                let wide = self.float_value(FloatKind::F64, wide);
                let narrow = self.builder.ins().fdemote(ir::types::F32, wide);
                self.float_bits(FloatKind::F32, narrow)
            }
        }
    }
    fn float_builtin(&mut self, op: crate::float::FloatOp, values: &[Value], ty: Type) -> Words {
        use crate::float::FloatOp;
        let word = values[0];
        let option =
            |g: &mut Self, present: Value, payload: Value, some: usize, none: usize| -> Words {
                let some_tag = g.constant(some as i64);
                let none_tag = g.constant(none as i64);
                let tag = g.builder.ins().select(present, some_tag, none_tag);
                let zero = g.constant(0);
                let payload = g.builder.ins().select(present, payload, zero);
                let mut words = vec![tag, payload];
                while words.len() < g.program.width(ty) {
                    words.push(g.constant(0));
                }
                words
            };
        match op {
            FloatOp::Abs(kind) => {
                let mask = match kind {
                    FloatKind::F32 => 0x7fff_ffffi64,
                    FloatKind::F64 => i64::MAX,
                };
                let mask = self.constant(mask);
                vec![self.builder.ins().band(word, mask)]
            }
            FloatOp::Sqrt(kind) => {
                let value = self.float_value(kind, word);
                let result = self.builder.ins().sqrt(value);
                vec![self.float_bits(kind, result)]
            }
            FloatOp::IsNan(kind) => {
                let value = self.float_value(kind, word);
                let result = self.builder.ins().fcmp(FloatCC::Unordered, value, value);
                vec![self.builder.ins().uextend(I64, result)]
            }
            FloatOp::IsInfinite(kind) => {
                let mask = self.constant(match kind {
                    FloatKind::F32 => 0x7fff_ffffi64,
                    FloatKind::F64 => i64::MAX,
                });
                let magnitude = self.builder.ins().band(word, mask);
                let result = self.builder.ins().icmp_imm_u(
                    IntCC::Equal,
                    magnitude,
                    kind.infinity_bits() as i64,
                );
                vec![self.builder.ins().uextend(I64, result)]
            }
            FloatOp::IsFinite(kind) => {
                let mask = self.constant(match kind {
                    FloatKind::F32 => 0x7fff_ffffi64,
                    FloatKind::F64 => i64::MAX,
                });
                let magnitude = self.builder.ins().band(word, mask);
                let result = self.builder.ins().icmp_imm_u(
                    IntCC::UnsignedLessThan,
                    magnitude,
                    kind.infinity_bits() as i64,
                );
                vec![self.builder.ins().uextend(I64, result)]
            }
            FloatOp::FromInt { source, target } | FloatOp::FromIntRounded { source, target } => {
                vec![self.float_from_integer(source, target, word)]
            }
            FloatOp::TryFromInt {
                source,
                target,
                some_tag,
                none_tag,
            } => {
                let payload = self.float_from_integer(source, target, word);
                let signed = self.constant(i64::from(source.signed()));
                let mantissa = self.constant(i64::from(target.mantissa_bits()));
                let exact = self.runtime_call(self.int_exact_in_float, &[word, signed, mantissa]);
                let present = self.builder.ins().icmp_imm_s(IntCC::NotEqual, exact, 0);
                option(self, present, payload, some_tag, none_tag)
            }
            FloatOp::ToF64(source) => match source {
                FloatKind::F64 => vec![word],
                FloatKind::F32 => {
                    let value = self.float_value(FloatKind::F32, word);
                    let wide = self.builder.ins().fpromote(ir::types::F64, value);
                    vec![self.float_bits(FloatKind::F64, wide)]
                }
            },
            FloatOp::TryToF32 {
                source,
                some_tag,
                none_tag,
            } => match source {
                FloatKind::F32 => {
                    let one = self.constant(1);
                    let present = self.builder.ins().icmp_imm_s(IntCC::NotEqual, one, 0);
                    option(self, present, word, some_tag, none_tag)
                }
                FloatKind::F64 => {
                    let wide = self.float_value(FloatKind::F64, word);
                    let narrow = self.builder.ins().fdemote(ir::types::F32, wide);
                    let payload = self.float_bits(FloatKind::F32, narrow);
                    let wide_mask = self.constant(i64::MAX);
                    let narrow_mask = self.constant(0x7fff_ffffi64);
                    let wide_magnitude = self.builder.ins().band(word, wide_mask);
                    let narrow_magnitude = self.builder.ins().band(payload, narrow_mask);
                    let wide_finite = self.builder.ins().icmp_imm_u(
                        IntCC::UnsignedLessThan,
                        wide_magnitude,
                        0x7ff0_0000_0000_0000,
                    );
                    let narrow_finite = self.builder.ins().icmp_imm_u(
                        IntCC::UnsignedLessThan,
                        narrow_magnitude,
                        0x7f80_0000,
                    );
                    // Reject only a finite wide value that overflowed to an
                    // f32 infinity. NaN and infinity are representable.
                    let overflowed = self.builder.ins().band_not(wide_finite, narrow_finite);
                    let present = self.builder.ins().icmp_imm_s(IntCC::Equal, overflowed, 0);
                    option(self, present, payload, some_tag, none_tag)
                }
            },
            FloatOp::TryToInt {
                source,
                target,
                some_tag,
                none_tag,
            } => {
                let wide = match source {
                    FloatKind::F64 => word,
                    FloatKind::F32 => {
                        let value = self.float_value(FloatKind::F32, word);
                        let wide = self.builder.ins().fpromote(ir::types::F64, value);
                        self.float_bits(FloatKind::F64, wide)
                    }
                };
                let target_index = self.constant(target.index());
                let present = self.runtime_call(self.float_int_present, &[wide, target_index]);
                let present = self.builder.ins().icmp_imm_s(IntCC::NotEqual, present, 0);
                let payload = self.runtime_call(self.float_to_int, &[wide, target_index]);
                option(self, present, payload, some_tag, none_tag)
            }
        }
    }
    fn assign(&mut self, slot: usize, values: &[Value]) {
        for (variable, value) in self.variables[slot].iter().zip(values) {
            self.builder.def_var(*variable, *value);
        }
        if let Some(pointer) = self.locations[slot] {
            for (index, value) in values.iter().enumerate() {
                self.builder.ins().store(
                    ir::MemFlagsData::new(),
                    *value,
                    pointer,
                    (index * 8) as i32,
                );
            }
        }
    }
    fn return_value(&mut self, values: &[Value]) {
        let base = self.builder.use_var(self.handler_base);
        self.runtime_void(self.handler_restore, &[base]);
        if let Some(pointer) = self.return_pointer {
            for (index, value) in values.iter().enumerate() {
                self.builder.ins().store(
                    ir::MemFlagsData::new(),
                    *value,
                    pointer,
                    (index * 8) as i32,
                );
            }
            self.builder.ins().return_(&[]);
        } else {
            self.builder.ins().return_(values);
        }
    }
    fn jump(&mut self, block: ir::Block, values: &[Value]) {
        let values = values.iter().copied().map(Into::into).collect::<Vec<_>>();
        self.builder.ins().jump(block, &values);
    }
    fn join(&mut self, ty: Type) -> Option<ir::Block> {
        if ty == Type::Never {
            return None;
        }
        let block = self.builder.create_block();
        for _ in 0..self.program.width(ty) {
            self.builder.append_block_param(block, I64);
        }
        Some(block)
    }
    fn runtime_call(&mut self, id: FuncId, values: &[Value]) -> Value {
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        let call = self.builder.ins().call(callee, values);
        self.builder.inst_results(call)[0]
    }
    fn runtime_void(&mut self, id: FuncId, values: &[Value]) {
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        self.builder.ins().call(callee, values);
    }
    /// Resolve a dynamic-object member identifier and call the checked method
    /// selected for that member. Owned dispatch loads the payload and releases
    /// its allocation before the call; borrowed dispatch passes the payload
    /// pointer directly so an owning/linear member is never copied.
    fn dyn_call(&mut self, spec_index: usize, values: Words) -> Words {
        let spec = self.program.dyn_calls[spec_index].clone();
        let members = self
            .program
            .dyn_members
            .get(spec.object)
            .cloned()
            .unwrap_or_default();
        let result_ty = if spec.result_grade.is_some_and(Grade::is_zero) {
            Type::Unit
        } else {
            spec.result
        };
        let join = self.join(result_ty);
        let owned = spec.mode == ReceiverMode::Owned;
        let member_id = if owned {
            values[0]
        } else {
            self.builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), values[0], 0)
        };
        let argument_start = if owned { 2 } else { 1 };
        for (index, entry) in members.iter().enumerate() {
            let hit = self.builder.create_block();
            let next = self.builder.create_block();
            let condition = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, member_id, index as i64);
            self.builder.ins().brif(condition, hit, &[], next, &[]);
            self.builder.switch_to_block(hit);
            let mut arguments = if owned {
                let pointer = values[1];
                let payload = (0..self.program.width(entry.member))
                    .map(|word| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            pointer,
                            (word * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                emit_drop(&mut self.builder, self.module, self.free, &[pointer]);
                payload
            } else {
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 8);
                vec![pointer]
            };
            arguments.extend(
                self.physical_dyn_arguments(&spec.parameter_grades, &values[argument_start..]),
            );
            let function = *entry
                .methods
                .get(&spec.method)
                .expect("checked dynamic member registers every object-safe trait method");
            let out = self.function_call(function, arguments);
            if let Some(join) = join {
                self.jump(join, &out);
            }
            self.builder.switch_to_block(next);
        }
        // No registered member can reach this point; a trait object value is
        // always created by a coercion that registered its member.
        self.abort();
        let join = join.expect("a dynamic call always has a value result");
        self.builder.switch_to_block(join);
        self.builder.block_params(join).to_vec()
    }
    /// Drop grade-zero logical arguments; they have no physical ABI slot but
    /// were still evaluated in source order by the call expression.
    fn physical_dyn_arguments(&self, grades: &[Option<Grade>], values: &[Value]) -> Vec<Value> {
        values
            .iter()
            .enumerate()
            .filter(|(index, _)| {
                !grades
                    .get(*index)
                    .copied()
                    .flatten()
                    .is_some_and(Grade::is_zero)
            })
            .map(|(_, value)| *value)
            .collect()
    }
    /// Dispatch a borrowed closed-world object in place. `values[0]` is a
    /// pointer to the inline union; the payload starts one word after the tag,
    /// so the selected member method receives that address as its borrowed
    /// receiver and no payload is copied or dropped.
    fn union_borrow_call(&mut self, spec_index: usize, values: Words) -> Words {
        let spec = self.program.union_calls[spec_index].clone();
        let result_ty = if spec.result_grade.is_some_and(Grade::is_zero) {
            Type::Unit
        } else {
            spec.result
        };
        let join = self.join(result_ty);
        let pointer = values[0];
        let tag = self
            .builder
            .ins()
            .load(I64, ir::MemFlagsData::new(), pointer, 0);
        let payload = self.builder.ins().iadd_imm_s(pointer, 8);
        for (member_tag, _member, function) in &spec.members {
            let hit = self.builder.create_block();
            let next = self.builder.create_block();
            let condition = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, tag, *member_tag as i64);
            self.builder.ins().brif(condition, hit, &[], next, &[]);
            self.builder.switch_to_block(hit);
            let mut arguments = vec![payload];
            arguments.extend(self.physical_dyn_arguments(&spec.parameter_grades, &values[1..]));
            let out = self.function_call(*function, arguments);
            if let Some(join) = join {
                self.jump(join, &out);
            }
            self.builder.switch_to_block(next);
        }
        self.abort();
        let join = join.expect("a borrowed dynamic call always has a value result");
        self.builder.switch_to_block(join);
        self.builder.block_params(join).to_vec()
    }
    fn function_call(&mut self, index: usize, mut values: Words) -> Words {
        let function = &self.program.functions[index];
        let result = function.result;
        let erased_result = function.result_grade.is_some_and(Grade::is_zero);
        let pointer = if !erased_result && aggregate_result(self.program, result) {
            let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                (self.program.width(result) * 8) as u32,
                3,
            ));
            let pointer = self.builder.ins().stack_addr(I64, slot, 0);
            values.insert(0, pointer);
            Some(pointer)
        } else {
            None
        };
        let callee = self
            .module
            .declare_func_in_func(self.ids[index], self.builder.func);
        let call = self.builder.ins().call(callee, &values);
        if erased_result {
            return vec![self.constant(0)];
        }
        if let Some(pointer) = pointer {
            (0..self.program.width(result))
                .map(|i| {
                    self.builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), pointer, (i * 8) as i32)
                })
                .collect()
        } else {
            self.builder.inst_results(call).to_vec()
        }
    }
    fn indirect_signature(&self, id: usize) -> ir::Signature {
        let signature = &self.program.function_types[id];
        let mut result = self.module.make_signature();
        let aggregate =
            !signature.result_erased() && aggregate_result(self.program, signature.result);
        if aggregate {
            result.params.push(AbiParam::new(I64));
        }
        if signature.once {
            result.params.push(AbiParam::new(I64));
        }
        for (index, parameter) in signature.parameters.iter().enumerate() {
            if signature.parameter_erased(index) {
                continue;
            }
            result
                .params
                .extend((0..self.program.width(*parameter)).map(|_| AbiParam::new(I64)));
        }
        if !aggregate && !signature.result_erased() {
            result
                .returns
                .extend((0..self.program.width(signature.result)).map(|_| AbiParam::new(I64)));
        }
        result
    }
    fn abort(&mut self) {
        let panic = self
            .module
            .declare_func_in_func(self.panic, self.builder.func);
        self.builder.ins().call(panic, &[]);
        self.builder.ins().trap(TrapCode::unwrap_user(1));
    }
    fn guard(&mut self, fail: Value) {
        let bad = self.builder.create_block();
        let good = self.builder.create_block();
        self.builder.ins().brif(fail, bad, &[], good, &[]);
        self.builder.switch_to_block(bad);
        self.abort();
        self.builder.switch_to_block(good);
    }
    fn block(&mut self, block: &ex::Block) -> Option<Words> {
        let mut slots = Vec::new();
        for statement in &block.statements {
            match statement {
                ex::Statement::Let(slot, expr) => {
                    let value = lower!(self.expr(expr));
                    self.consume(expr);
                    if self.erased_local(*slot) {
                        if self.program.owns(expr.ty) {
                            self.drop_value(expr.ty, &value);
                        }
                        continue;
                    }
                    self.assign(*slot, &value);
                    self.activate_local(*slot);
                    slots.push(*slot);
                }
                ex::Statement::Expr(expr) => {
                    lower!(self.expr(expr));
                    self.cleanup(expr.resource);
                }
            }
        }
        let value = if let Some(tail) = &block.tail {
            let value = lower!(self.expr(tail));
            self.consume(tail);
            value
        } else {
            vec![self.constant(0)]
        };
        for slot in slots.into_iter().rev() {
            self.cleanup(self.program.functions[self.function_index].local_resources[slot]);
        }
        Some(value)
    }
    fn expr(&mut self, expr: &Expr) -> Option<Words> {
        let values = self.expression(expr)?;
        self.track(expr.resource, &values);
        Some(values)
    }
    fn expression(&mut self, expr: &Expr) -> Option<Words> {
        let scalar = match &expr.kind {
            ExprKind::Constant(n) => self.constant(*n),
            // Synthesized adapter placeholder for a physically erased
            // parameter position. The call's ABI drops these words.
            ExprKind::Erased(ty) => {
                let width = self.program.width(*ty);
                return Some(vec![self.constant(0); width]);
            }
            ExprKind::FnValue { function, captures } => {
                let reference = self
                    .module
                    .declare_func_in_func(self.ids[*function], self.builder.func);
                let code = self.builder.ins().func_addr(I64, reference);
                if captures.is_empty() {
                    if matches!(expr.ty, Type::Once(_)) {
                        let zero = self.constant(0);
                        return Some(vec![code, zero]);
                    }
                    code
                } else {
                    let types = captures
                        .iter()
                        .map(|capture| capture.ty.full())
                        .collect::<Vec<_>>();
                    let bytes = 8 + types
                        .iter()
                        .map(|ty| self.program.width(*ty) * 8)
                        .sum::<usize>();
                    let size = self.constant(bytes as i64);
                    let environment = self.runtime_call(self.allocate, &[size]);
                    let drop = self.closure_drops[&types];
                    let drop = self.module.declare_func_in_func(drop, self.builder.func);
                    let drop = self.builder.ins().func_addr(I64, drop);
                    self.builder
                        .ins()
                        .store(ir::MemFlagsData::new(), drop, environment, 0);
                    let mut offset = 8;
                    for capture in captures {
                        let values = lower!(self.expr(capture));
                        self.consume(capture);
                        let width = self.program.width(capture.ty);
                        let mut position = offset;
                        for value in values.iter().take(width) {
                            self.builder.ins().store(
                                ir::MemFlagsData::new(),
                                *value,
                                environment,
                                position as i32,
                            );
                            position += 8;
                        }
                        offset += width * 8;
                    }
                    return Some(vec![code, environment]);
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                let callable = lower!(self.expr(callee));
                let Some((id, once)) = (match callee.ty {
                    Type::Fn(id) => Some((id, false)),
                    Type::Once(id) => Some((id, true)),
                    _ => None,
                }) else {
                    unreachable!("checked indirect callee")
                };
                let signature = self.program.function_types[id].clone();
                let result = signature.result;
                let result_erased = signature.result_erased();
                let pointer = if !result_erased && aggregate_result(self.program, result) {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (self.program.width(result) * 8) as u32,
                        3,
                    ));
                    let pointer = self.builder.ins().stack_addr(I64, slot, 0);
                    Some(pointer)
                } else {
                    None
                };
                let mut values = Vec::new();
                if let Some(pointer) = pointer {
                    values.push(pointer);
                }
                if once {
                    values.push(callable[1]);
                }
                for (index, argument) in arguments.iter().enumerate() {
                    let words = lower!(self.expr(argument));
                    if !signature.parameter_erased(index) {
                        values.extend(words);
                    }
                }
                self.consume(callee);
                for argument in arguments {
                    self.consume(argument);
                }
                let signature = self.indirect_signature(id);
                let signature = self.builder.import_signature(signature);
                let call = self
                    .builder
                    .ins()
                    .call_indirect(signature, callable[0], &values);
                if result_erased {
                    return Some(vec![self.constant(0)]);
                }
                if let Some(pointer) = pointer {
                    return Some(
                        (0..self.program.width(result))
                            .map(|i| {
                                self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    pointer,
                                    (i * 8) as i32,
                                )
                            })
                            .collect(),
                    );
                }
                return Some(self.builder.inst_results(call).to_vec());
            }
            ExprKind::HandlerPush {
                operation,
                handler,
                body,
            } => {
                let code = lower!(self.scalar(handler));
                self.consume(handler);
                let zero = self.constant(0);
                let op = self.constant(*operation as i64);
                self.runtime_void(self.handler_push, &[op, code, zero]);
                if let Some(values) = self.block(body) {
                    self.runtime_void(self.handler_pop, &[]);
                    return Some(values);
                }
                return None;
            }
            ExprKind::DynamicPerform {
                operation,
                payload,
                resume,
                handler,
            } => {
                let payload_values = lower!(self.expr(payload));
                let resume_values = lower!(self.expr(resume));
                self.consume(payload);
                self.consume(resume);
                let out = self.stack_words(2);
                let op = self.constant(*operation as i64);
                let found = self.runtime_call(self.handler_lookup, &[op, out]);
                let missing = self.builder.ins().icmp_imm_s(IntCC::Equal, found, 0);
                self.guard(missing);
                let code = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 0);
                let signature = self.program.function_types[*handler].clone();
                let result = signature.result;
                let pointer = if aggregate_result(self.program, result) {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (self.program.width(result) * 8) as u32,
                        3,
                    ));
                    Some(self.builder.ins().stack_addr(I64, slot, 0))
                } else {
                    None
                };
                let mut values = Vec::new();
                if let Some(pointer) = pointer {
                    values.push(pointer);
                }
                values.extend(payload_values);
                values.extend(resume_values);
                let signature = self.indirect_signature(*handler);
                let signature = self.builder.import_signature(signature);
                let call = self.builder.ins().call_indirect(signature, code, &values);
                if let Some(pointer) = pointer {
                    return Some(
                        (0..self.program.width(result))
                            .map(|i| {
                                self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    pointer,
                                    (i * 8) as i32,
                                )
                            })
                            .collect(),
                    );
                }
                return Some(self.builder.inst_results(call).to_vec());
            }
            ExprKind::BytesLiteral(bytes) => {
                let gv = self
                    .module
                    .declare_data_in_func(self.literal_data[&expr.span.start], self.builder.func);
                let address = self.builder.ins().symbol_value(I64, gv);
                let length = self.constant(bytes.len() as i64);
                self.runtime_call(self.bytes_from, &[address, length])
            }
            ExprKind::Move(slot) => {
                self.deactivate(self.program.functions[self.function_index].local_resources[*slot]);
                if let Some(pointer) = self.locations[*slot] {
                    let width = self.variables[*slot].len();
                    return Some(self.load_words(pointer, 0, width));
                }
                return Some(
                    self.variables[*slot]
                        .iter()
                        .map(|v| self.builder.use_var(*v))
                        .collect(),
                );
            }
            ExprKind::Borrow(slot) => {
                let local = &self.program.functions[self.function_index].locals[*slot];
                let record = local
                    .ty
                    .layout()
                    .is_some_and(|id| self.program.enums[id].record);
                if record || matches!(local.ty, Type::Union(_) | Type::DynObj(_)) {
                    let pointer = self.locations[*slot]
                        .expect("checked inline object borrow is pinned to stack storage");
                    return Some(vec![pointer]);
                }
                if matches!(
                    local.ty,
                    Type::Box(_)
                        | Type::ArenaBox(_)
                        | Type::Arena
                        | Type::Bytes
                        | Type::String
                        | Type::Vec(_)
                ) {
                    let pointer = self.locations[*slot]
                        .expect("checked owner borrow is pinned to stack storage");
                    return Some(vec![pointer]);
                }
                let variable = self.builder.use_var(self.variables[*slot][0]);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    8,
                    3,
                ));
                let pointer = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), variable, pointer, 0);
                pointer
            }
            ExprKind::BoxNew(arg) => {
                let values = lower!(self.expr(arg));
                let bytes = self.constant((self.program.width(arg.ty) * 8) as i64);
                let pointer = self.runtime_call(self.allocate, &[bytes]);
                self.consume(arg);
                for (i, value) in values.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        (i * 8) as i32,
                    );
                }
                pointer
            }
            ExprKind::BoxTake(arg) => {
                let pointer = lower!(self.scalar(arg));
                let values = (0..self.program.width(expr.ty))
                    .map(|i| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            pointer,
                            (i * 8) as i32,
                        )
                    })
                    .collect();
                self.consume(arg);
                emit_drop(&mut self.builder, self.module, self.free, &[pointer]);
                return Some(values);
            }
            ExprKind::BoxRead(arg) => {
                let reference = lower!(self.scalar(arg));
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                return Some(
                    (0..self.program.width(expr.ty))
                        .map(|i| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                pointer,
                                (i * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::BoxWrite(reference, value) => {
                let reference = lower!(self.scalar(reference));
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let words = lower!(self.expr(value));
                for (index, word) in words.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                self.consume(value);
                return Some(vec![self.constant(0)]);
            }
            ExprKind::AllocatorNew { alloc, free } => {
                let allocator = lower!(self.expr(alloc));
                let release = lower!(self.expr(free));
                return Some(vec![allocator[0], release[0]]);
            }
            ExprKind::AllocBoxNew { allocator, value } => {
                let pair = lower!(self.expr(allocator));
                let payload = lower!(self.expr(value));
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                self.consume(value);
                let block = self.runtime_call(self.alloc_ops.block, &[pair[0], pair[1], bytes]);
                let data = self.runtime_call(self.alloc_ops.block_data, &[block]);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        data,
                        (index * 8) as i32,
                    );
                }
                let handle =
                    self.runtime_call(self.alloc_ops.box_create, &[pair[0], pair[1], block]);
                return Some(vec![handle]);
            }
            ExprKind::AllocBoxTryNew {
                allocator,
                value,
                shape,
            } => {
                let pair = lower!(self.expr(allocator));
                let payload = lower!(self.expr(value));
                self.consume(value);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                let block = self.runtime_call(self.alloc_ops.block_try, &[pair[0], pair[1], bytes]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, block, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    3,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                let data = self.runtime_call(self.alloc_ops.block_data, &[block]);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        data,
                        (index * 8) as i32,
                    );
                }
                let owner =
                    self.runtime_call(self.alloc_ops.box_create, &[pair[0], pair[1], block]);
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), owner, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        destination,
                        ((index + 1) * 8) as i32,
                    );
                }
                let zero = self.constant(0);
                for index in (payload.len() + 1)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::AllocBoxRead(argument) => {
                let reference = lower!(self.scalar(argument));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let data = self.runtime_call(self.alloc_ops.box_payload, &[handle]);
                return Some(
                    (0..self.program.width(expr.ty))
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                data,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::AllocBoxTake(argument) => {
                let handle = lower!(self.scalar(argument));
                let data = self.runtime_call(self.alloc_ops.box_payload, &[handle]);
                let payload = (0..self.program.width(expr.ty))
                    .map(|index| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            data,
                            (index * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                self.consume(argument);
                self.runtime_void(self.alloc_ops.box_release, &[handle]);
                return Some(payload);
            }
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                element,
            } => {
                let pair = lower!(self.expr(allocator));
                let capacity = match capacity {
                    Some(capacity) => lower!(self.scalar(capacity)),
                    None => self.constant(0),
                };
                let width = self.constant(self.program.width(*element) as i64);
                let handle = self.runtime_call(
                    self.alloc_ops.vec_create,
                    &[pair[0], pair[1], capacity, width],
                );
                return Some(vec![handle]);
            }
            ExprKind::BoxReuse { owner, payload } => {
                let pointer = lower!(self.scalar(owner));
                let old = match owner.ty {
                    Type::Box(index) => self.program.pointees[index],
                    _ => unreachable!("checked Box.reuse owner"),
                };
                let old_width = self.program.width(old);
                // Both arguments are evaluated before the old payload is
                // destroyed. If the payload diverges, the owner's tracked
                // resource is still live and cleanup reclaims the box.
                let new = lower!(self.expr(payload));
                self.consume(owner);
                self.consume(payload);
                let previous = self.load_words(pointer, 0, old_width);
                self.drop_value(old, &previous);
                for (index, value) in new.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                let _ = self.runtime_call(self.note_reuse, &[]);
                pointer
            }
            ExprKind::BoxReuseGrow { owner, payload } => {
                let pointer = lower!(self.scalar(owner));
                let old = match owner.ty {
                    Type::Box(index) => self.program.pointees[index],
                    _ => unreachable!("checked Box.reuse_grow owner"),
                };
                let old_width = self.program.width(old);
                let new = lower!(self.expr(payload));
                self.consume(owner);
                self.consume(payload);
                let previous = self.load_words(pointer, 0, old_width);
                self.drop_value(old, &previous);
                let new_width = self.program.width(payload.ty);
                let pointer = if new_width > old_width {
                    let bytes = self.constant((new_width * 8) as i64);
                    self.runtime_call(self.grow, &[pointer, bytes])
                } else {
                    pointer
                };
                for (index, value) in new.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                let _ = self.runtime_call(self.note_reuse, &[]);
                pointer
            }
            ExprKind::ArenaNew => self.runtime_call(self.arena_new, &[]),
            ExprKind::ArenaNewWith { strategy } => {
                let code = lower!(self.scalar(strategy));
                self.consume(strategy);
                self.runtime_call(self.arena_new_with_strategy, &[code])
            }
            ExprKind::ArenaAlloc { arena, value } => {
                let reference = lower!(self.scalar(arena));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let payload = lower!(self.expr(value));
                self.consume(arena);
                self.consume(value);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                let pointer = self.runtime_call(self.arena_alloc, &[handle, bytes]);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                pointer
            }
            ExprKind::ArenaTryAlloc {
                arena,
                value,
                shape,
            } => {
                let reference = lower!(self.scalar(arena));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let payload = lower!(self.expr(value));
                self.consume(arena);
                self.consume(value);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                let pointer = self.runtime_call(self.arena_try_alloc, &[handle, bytes]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, pointer, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    3,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), pointer, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        destination,
                        ((index + 1) * 8) as i32,
                    );
                }
                let zero = self.constant(0);
                for index in (payload.len() + 1)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::ArenaBoxRead(argument) => {
                let reference = lower!(self.scalar(argument));
                let pointer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                return Some(
                    (0..self.program.width(expr.ty))
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                pointer,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::ArenaBoxTake(argument) => {
                let pointer = lower!(self.scalar(argument));
                self.consume(argument);
                let values = (0..self.program.width(expr.ty))
                    .map(|index| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            pointer,
                            (index * 8) as i32,
                        )
                    })
                    .collect::<Vec<_>>();
                self.runtime_void(self.arena_box_release, &[pointer]);
                return Some(values);
            }
            ExprKind::BoxTryNew { value, shape } => {
                let payload = lower!(self.expr(value));
                self.consume(value);
                let width = self.program.width(value.ty);
                let bytes = self.constant((width * 8) as i64);
                let handle = self.runtime_call(self.try_allocate, &[bytes]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, handle, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    3,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        handle,
                        (index * 8) as i32,
                    );
                }
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), handle, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        destination,
                        ((index + 1) * 8) as i32,
                    );
                }
                let zero = self.constant(0);
                for index in (payload.len() + 1)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                let _ = shape;
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::BoxTryReuse {
                owner,
                payload,
                shape,
            } => {
                let pointer = lower!(self.scalar(owner));
                let old = match owner.ty {
                    Type::Box(index) => self.program.pointees[index],
                    _ => unreachable!("checked Box.try_reuse owner"),
                };
                let old_width = self.program.width(old);
                let new = lower!(self.expr(payload));
                self.consume(owner);
                self.consume(payload);
                let previous = self.load_words(pointer, 0, old_width);
                let new_width = self.program.width(payload.ty);
                let bytes = self.constant((new_width * 8) as i64);
                let grown = self.runtime_call(self.try_grow, &[pointer, bytes]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, grown, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    3,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                self.drop_value(old, &previous);
                for (index, word) in new.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        grown,
                        (index * 8) as i32,
                    );
                }
                let _ = self.runtime_call(self.note_reuse, &[]);
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), grown, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), pointer, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                let _ = shape;
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::BytesTryWithCapacity { capacity, shape } => {
                let requested = lower!(self.scalar(capacity));
                self.consume(capacity);
                let handle = self.runtime_call(self.try_bytes_with_capacity, &[requested]);
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, handle, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    3,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), handle, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), requested, destination, 8);
                let zero = self.constant(0);
                for index in 2..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                let _ = shape;
                return Some(
                    (0..result_width)
                        .map(|index| {
                            self.builder.ins().load(
                                I64,
                                ir::MemFlagsData::new(),
                                destination,
                                (index * 8) as i32,
                            )
                        })
                        .collect(),
                );
            }
            ExprKind::Drop(arg) => {
                let value = lower!(self.expr(arg));
                self.consume(arg);
                self.drop_value(arg.ty, &value);
                self.constant(0)
            }
            ExprKind::Coerce {
                value,
                to,
                coercion,
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                let width = self.program.width(*to);
                match coercion {
                    Coercion::Inject { tag } => {
                        let mut out = Vec::with_capacity(width);
                        out.push(self.constant(*tag as i64));
                        out.extend(values.iter().copied().take(width.saturating_sub(1)));
                        while out.len() < width {
                            out.push(self.constant(0));
                        }
                        return Some(out);
                    }
                    Coercion::Struct {
                        source,
                        kept,
                        drops,
                    } => {
                        let target_id = to.layout().expect("checked structural target layout");
                        let target_fields =
                            self.program.enums[target_id].variants[0].fields.clone();
                        let mut out: Vec<Value> = vec![self.constant(0)];
                        self.struct_coercion_words(
                            *source,
                            &target_fields,
                            kept,
                            drops,
                            &values,
                            &mut out,
                        );
                        while out.len() < width {
                            out.push(self.constant(0));
                        }
                        return Some(out);
                    }
                    Coercion::Repack { map } => {
                        let exit = self.join(*to)?;
                        for (source_tag, target_tag) in map.iter().enumerate() {
                            let hit = self.builder.create_block();
                            let next = self.builder.create_block();
                            let condition = self.builder.ins().icmp_imm_s(
                                IntCC::Equal,
                                values[0],
                                source_tag as i64,
                            );
                            self.builder.ins().brif(condition, hit, &[], next, &[]);
                            self.builder.switch_to_block(hit);
                            let mut out = Vec::with_capacity(width);
                            out.push(self.constant(*target_tag as i64));
                            out.extend(values[1..].iter().copied().take(width.saturating_sub(1)));
                            while out.len() < width {
                                out.push(self.constant(0));
                            }
                            self.jump(exit, &out);
                            self.builder.switch_to_block(next);
                        }
                        self.builder.ins().trap(TrapCode::unwrap_user(2));
                        self.builder.switch_to_block(exit);
                        return Some(self.builder.block_params(exit).to_vec());
                    }
                    Coercion::Callable { .. } => {
                        return Some(self.nested_coercion_words(coercion, *to, &values));
                    }
                    Coercion::DynBox {
                        member,
                        member_type,
                        ..
                    } => {
                        let pointer = self.allocate_dyn_payload(*member_type, &values);
                        return Some(vec![self.constant(*member as i64), pointer]);
                    }
                }
            }
            ExprKind::DynArrayNew { element, capacity } => {
                let width = self.program.width(*element);
                return Some(vec![self.constant(0); 1 + width * capacity]);
            }
            ExprKind::DynArrayPush {
                array,
                value,
                element,
                capacity,
            } => {
                let values = lower!(self.expr(array));
                self.consume(array);
                let item = lower!(self.expr(value));
                self.consume(value);
                let element_width = self.program.width(*element);
                let length = values[0];
                let full = self.builder.ins().icmp_imm_s(
                    IntCC::UnsignedGreaterThanOrEqual,
                    length,
                    *capacity as i64,
                );
                self.guard(full);
                let mut out = values.clone();
                let next = self.builder.ins().iadd_imm_s(length, 1);
                out[0] = next;
                // The inline storage is represented as SSA words, not memory.
                // Select the active capacity slot without a runtime index into
                // the value vector: each slot compares the length once.
                for slot in 0..*capacity {
                    let active = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, length, slot as i64);
                    for (word, value) in item.iter().take(element_width).enumerate() {
                        let index = 1 + slot * element_width + word;
                        out[index] = self.builder.ins().select(active, *value, out[index]);
                    }
                }
                return Some(out);
            }
            ExprKind::DynArraySet {
                array,
                index,
                value,
                element,
                capacity,
            } => {
                let mut values = lower!(self.expr(array));
                self.consume(array);
                let position = lower!(self.scalar(index));
                self.consume(index);
                let item = lower!(self.expr(value));
                self.consume(value);
                let length = values[0];
                let bad =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, position, length);
                self.guard(bad);
                let element_width = self.program.width(*element);
                for slot in 0..*capacity {
                    let active = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, position, slot as i64);
                    for (word, value) in item.iter().take(element_width).enumerate() {
                        let index = 1 + slot * element_width + word;
                        values[index] = self.builder.ins().select(active, *value, values[index]);
                    }
                }
                return Some(values);
            }
            ExprKind::DynArrayPop {
                array,
                element,
                capacity,
            } => {
                let mut values = lower!(self.expr(array));
                self.consume(array);
                let length = values[0];
                let empty = self.builder.ins().icmp_imm_s(IntCC::Equal, length, 0);
                self.guard(empty);
                let next = self.builder.ins().iadd_imm_s(length, -1);
                let zero = self.constant(0);
                // The result type is the checked tuple layout, whose first
                // word is the single (always zero) constructor tag.
                values.insert(0, zero);
                values[1] = next;
                let element_width = self.program.width(*element);
                let mut item = vec![zero; element_width];
                for slot in 0..*capacity {
                    let active = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, next, slot as i64);
                    for (word, item_word) in item.iter_mut().enumerate() {
                        let index = 2 + slot * element_width + word;
                        *item_word = self.builder.ins().select(active, values[index], *item_word);
                        values[index] = self.builder.ins().select(active, zero, values[index]);
                    }
                }
                values.extend(item);
                return Some(values);
            }
            ExprKind::Project(base, offset) => {
                let values = lower!(self.expr(base));
                let width = self.program.width(expr.ty);
                if base.ty.is_ref() {
                    let pointer = values[0];
                    return Some(self.load_words(pointer, (*offset * 8) as i32, width));
                }
                return Some(values[*offset..*offset + width].to_vec());
            }
            ExprKind::BytesAt(bytes, index) => {
                let reference = lower!(self.scalar(bytes));
                let index = lower!(self.scalar(index));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                // Proved in bounds: no check. Data follows the 16-byte header.
                let address = self.builder.ins().iadd(handle, index);
                self.builder
                    .ins()
                    .uload8(I64, ir::MemFlagsData::new(), address, 16)
            }
            ExprKind::Slice {
                base,
                start,
                end,
                element,
                check,
                split: _,
                text,
            } => {
                if *text {
                    let base_values = lower!(self.expr(base));
                    let (pointer, length) = match base.ty {
                        Type::Ref(p) => match self.program.pointees[p] {
                            Type::String => {
                                let handle = self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    base_values[0],
                                    0,
                                );
                                let data = self.builder.ins().iadd_imm_s(handle, 16);
                                let length = self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    handle,
                                    0,
                                );
                                (data, length)
                            }
                            _ => unreachable!("checked text view source"),
                        },
                        Type::Str => (base_values[0], base_values[1]),
                        _ => unreachable!("checked text view source"),
                    };
                    let start = match start {
                        Some(start) => lower!(self.scalar(start)),
                        None => self.constant(0),
                    };
                    let end = match end {
                        Some(end) => lower!(self.scalar(end)),
                        None => length,
                    };
                    if *check {
                        self.check_range(start, end, length);
                        self.check_text_boundary(pointer, start, length);
                        self.check_text_boundary(pointer, end, length);
                    }
                    let pointer = self.builder.ins().iadd(pointer, start);
                    let length = self.builder.ins().isub(end, start);
                    return Some(vec![pointer, length, self.constant(1), self.constant(1)]);
                }
                let element_width = self.program.width(*element);
                let array_location = match &base.kind {
                    ExprKind::Local(slot) | ExprKind::Peek(slot)
                        if base
                            .ty
                            .layout()
                            .is_some_and(|id| self.program.enums[id].array.is_some()) =>
                    {
                        self.locations[*slot]
                    }
                    _ => None,
                };
                // A checked DynArray view borrows the pinned record storage, so
                // the descriptor points at the live inline slots. The length is
                // the runtime length word, and the capacity is the static bound.
                let dynamic_array_location = match &base.kind {
                    ExprKind::Borrow(slot)
                        if base
                            .ty
                            .ref_pointee()
                            .and_then(|pointee| self.program.pointees.get(pointee).copied())
                            .and_then(|pointee| pointee.layout())
                            .is_some_and(|id| self.program.enums[id].dynamic_array.is_some()) =>
                    {
                        self.locations[*slot]
                    }
                    _ => None,
                };
                let base_values = if array_location.is_some() || dynamic_array_location.is_some() {
                    Vec::new()
                } else {
                    lower!(self.expr(base))
                };
                let (pointer, length, stride, bytes) =
                    if let Some(location) = dynamic_array_location {
                        // Word 0 is the runtime length; elements follow it.
                        let data = self.builder.ins().iadd_imm_s(location, 8);
                        let length =
                            self.builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), location, 0);
                        (
                            data,
                            length,
                            self.constant((element_width * 8) as i64),
                            self.constant(0),
                        )
                    } else if let Some(location) = array_location {
                        let (_, length) = base
                            .ty
                            .layout()
                            .and_then(|id| self.program.enums[id].array)
                            .expect("checked array slice source");
                        // Word 0 is the private array tag; elements follow it.
                        let data = self.builder.ins().iadd_imm_s(location, 8);
                        (
                            data,
                            self.constant(length as i64),
                            self.constant((element_width * 8) as i64),
                            self.constant(0),
                        )
                    } else if let Some((_, length)) =
                        base.ty.layout().and_then(|id| self.program.enums[id].array)
                    {
                        let slot = self.stack_words(base_values.len());
                        self.store_words(slot, &base_values);
                        // Word 0 is the private array tag; elements follow it.
                        let data = self.builder.ins().iadd_imm_s(slot, 8);
                        (
                            data,
                            self.constant(length as i64),
                            self.constant((element_width * 8) as i64),
                            self.constant(0),
                        )
                    } else {
                        match base.ty {
                            Type::Ref(p) => match self.program.pointees[p] {
                                Type::Bytes => {
                                    let handle = self.builder.ins().load(
                                        I64,
                                        ir::MemFlagsData::new(),
                                        base_values[0],
                                        0,
                                    );
                                    let data = self.builder.ins().iadd_imm_s(handle, 16);
                                    let length = self.builder.ins().load(
                                        I64,
                                        ir::MemFlagsData::new(),
                                        handle,
                                        0,
                                    );
                                    (data, length, self.constant(1), self.constant(1))
                                }
                                Type::Vec(_) => {
                                    let handle = self.builder.ins().load(
                                        I64,
                                        ir::MemFlagsData::new(),
                                        base_values[0],
                                        0,
                                    );
                                    let data = self.builder.ins().iadd_imm_s(handle, 24);
                                    let length = self.builder.ins().load(
                                        I64,
                                        ir::MemFlagsData::new(),
                                        handle,
                                        0,
                                    );
                                    (
                                        data,
                                        length,
                                        self.constant((element_width * 8) as i64),
                                        self.constant(0),
                                    )
                                }
                                _ => unreachable!("checked slice source"),
                            },
                            Type::Slice(_) | Type::SliceMut(_) => (
                                base_values[0],
                                base_values[1],
                                base_values[2],
                                base_values[3],
                            ),
                            _ => unreachable!("checked slice source"),
                        }
                    };
                let start = match start {
                    Some(start) => lower!(self.scalar(start)),
                    None => self.constant(0),
                };
                let end = match end {
                    Some(end) => lower!(self.scalar(end)),
                    None => length,
                };
                if *check {
                    self.check_range(start, end, length);
                }
                let offset = self.builder.ins().imul(start, stride);
                let pointer = self.builder.ins().iadd(pointer, offset);
                let length = self.builder.ins().isub(end, start);
                return Some(vec![pointer, length, stride, bytes]);
            }
            ExprKind::While(condition, body) => {
                let head = self.builder.create_block();
                let enter = self.builder.create_block();
                let exit = self.builder.create_block();
                let depth = self.builder.declare_var(I64);
                let at_entry = self.runtime_call(self.handler_depth, &[]);
                self.builder.def_var(depth, at_entry);
                self.jump(head, &[]);
                self.builder.switch_to_block(head);
                if let Some(test) = self.scalar(condition) {
                    self.builder.ins().brif(test, enter, &[], exit, &[]);
                    self.builder.switch_to_block(enter);
                    self.loops.push((head, exit, false, depth));
                    let finished = self.block(body);
                    self.loops.pop();
                    if finished.is_some() {
                        self.jump(head, &[]);
                    }
                }
                self.builder.switch_to_block(exit);
                self.constant(0)
            }
            ExprKind::Loop(body) => {
                let head = self.builder.create_block();
                let exit = self.join(expr.ty);
                let depth = self.builder.declare_var(I64);
                let at_entry = self.runtime_call(self.handler_depth, &[]);
                self.builder.def_var(depth, at_entry);
                self.jump(head, &[]);
                self.builder.switch_to_block(head);
                // A loop without break has type Never; its exit is never targeted.
                let target = exit.unwrap_or(head);
                self.loops.push((head, target, true, depth));
                let finished = self.block(body);
                self.loops.pop();
                if finished.is_some() {
                    self.jump(head, &[]);
                }
                let exit = exit?;
                self.builder.switch_to_block(exit);
                return Some(self.builder.block_params(exit).to_vec());
            }
            ExprKind::Break(value, cleanup) => {
                let (_, exit, carries, depth) = *self.loops.last().unwrap();
                let values = match value {
                    Some(value) => {
                        let values = lower!(self.expr(value));
                        self.consume(value);
                        values
                    }
                    None if carries => vec![self.constant(0)],
                    None => vec![],
                };
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                let depth = self.builder.use_var(depth);
                self.runtime_void(self.handler_restore, &[depth]);
                self.jump(exit, &values);
                return None;
            }
            ExprKind::Continue(cleanup) => {
                let (head, _, _, depth) = *self.loops.last().unwrap();
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                let depth = self.builder.use_var(depth);
                self.runtime_void(self.handler_restore, &[depth]);
                self.jump(head, &[]);
                return None;
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot) => {
                if let Some(pointer) = self.locations[*slot] {
                    let width = self.variables[*slot].len();
                    return Some(self.load_words(pointer, 0, width));
                }
                return Some(
                    self.variables[*slot]
                        .iter()
                        .map(|v| self.builder.use_var(*v))
                        .collect(),
                );
            }
            ExprKind::Block(block) => return self.block(block),
            ExprKind::Construct {
                enum_id,
                tag,
                fields,
            } => {
                let mut values = vec![self.constant(*tag as i64)];
                for field in fields {
                    values.extend(lower!(self.expr(field)));
                }
                for field in fields {
                    self.consume(field);
                }
                while values.len() < self.program.enums[*enum_id].words {
                    values.push(self.constant(0));
                }
                return Some(values);
            }
            ExprKind::Try {
                value,
                input,
                output,
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                let condition =
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, values[0], input.ok_tag as i64);
                let success = self.builder.create_block();
                let failure = self.builder.create_block();
                self.builder
                    .ins()
                    .brif(condition, success, &[], failure, &[]);
                self.builder.switch_to_block(failure);
                let mut error = vec![self.constant(output.err_tag as i64)];
                error.extend_from_slice(&values[1..1 + self.program.width(input.error)]);
                while error.len() < self.program.width(self.result) {
                    error.push(self.constant(0));
                }
                self.cleanup_all();
                self.return_value(&error);
                self.builder.switch_to_block(success);
                return Some(values[1..1 + self.program.width(input.ok)].to_vec());
            }
            ExprKind::Unary(op, operand) => {
                let value = lower!(self.scalar(operand));
                if let Some(kind) = operand.ty.float_kind() {
                    if *op != Kind::Minus {
                        self.abort();
                        return None;
                    }
                    let mask = match kind {
                        FloatKind::F32 => 1i64 << 31,
                        FloatKind::F64 => i64::MIN,
                    };
                    let mask = self.constant(mask);
                    self.builder.ins().bxor(value, mask)
                } else if let Some(kind) = operand.ty.int_kind().filter(|k| *k != IntKind::I64) {
                    if *op == Kind::Minus {
                        let zero = self.constant(0);
                        let (negated, overflow) = self.builder.ins().ssub_overflow(zero, value);
                        self.guard(overflow);
                        self.check_int_range(kind, negated)
                    } else {
                        let inverted = self.builder.ins().bnot(value);
                        self.canonical(kind, inverted)
                    }
                } else if *op == Kind::Bang && operand.ty == Type::I64 {
                    self.builder.ins().bnot(value)
                } else if *op == Kind::Minus {
                    let zero = self.constant(0);
                    let (value, overflow) = self.builder.ins().ssub_overflow(zero, value);
                    self.guard(overflow);
                    value
                } else {
                    let comparison = self.builder.ins().icmp_imm_s(IntCC::Equal, value, 0);
                    self.builder.ins().uextend(I64, comparison)
                }
            }
            ExprKind::Assign(slot, replacement) => {
                let value = lower!(self.expr(replacement));
                self.consume(replacement);
                if !self.erased_local(*slot) {
                    self.cleanup(
                        self.program.functions[self.function_index].local_resources[*slot],
                    );
                    self.assign(*slot, &value);
                    self.activate_local(*slot);
                } else if self.program.owns(replacement.ty) {
                    self.drop_value(replacement.ty, &value);
                }
                self.constant(0)
            }
            ExprKind::RefRead(reference) => {
                let pointer = lower!(self.scalar(reference));
                return Some(self.load_words(pointer, 0, self.program.width(expr.ty)));
            }
            ExprKind::RefWrite(reference, replacement) => {
                let pointer = lower!(self.scalar(reference));
                let value = lower!(self.expr(replacement));
                for (index, word) in value.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        (index * 8) as i32,
                    );
                }
                self.consume(replacement);
                self.constant(0)
            }
            ExprKind::RefAssign(reference, offset, replacement) => {
                let pointer = lower!(self.scalar(reference));
                let value = lower!(self.expr(replacement));
                for (index, word) in value.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        pointer,
                        ((offset + index) * 8) as i32,
                    );
                }
                self.consume(replacement);
                self.constant(0)
            }
            ExprKind::StructEq {
                left,
                right,
                negated,
            } => {
                let ty = left.ty;
                let left = lower!(self.expr(left));
                let right = lower!(self.expr(right));
                let equal = self.struct_eq_words(ty, &left, &right);
                let value = if *negated {
                    self.builder.ins().bxor_imm_s(equal, 1)
                } else {
                    equal
                };
                return Some(vec![self.builder.ins().uextend(I64, value)]);
            }
            ExprKind::Binary(op, left, right_expr) => {
                let left_ty = left.ty;
                let left_kind = left.ty.int_kind();
                let left = lower!(self.scalar(left));
                if matches!(op, Kind::AmpAmp | Kind::PipePipe) {
                    return self.short_circuit(op, left, right_expr);
                }
                let right_kind = right_expr.ty.int_kind();
                let right = lower!(self.scalar(right_expr));
                if let Some(kind) = left_ty.float_kind() {
                    let left = self.float_value(kind, left);
                    let right = self.float_value(kind, right);
                    return Some(vec![self.float_binary(kind, op, left, right)]);
                }
                if let Some(kind) = left_kind {
                    return Some(vec![self.int_binary(kind, op, left, right, right_kind)]);
                }
                match op {
                    Kind::Plus | Kind::Minus | Kind::Star => {
                        let (value, overflow) = match op {
                            Kind::Plus => self.builder.ins().sadd_overflow(left, right),
                            Kind::Minus => self.builder.ins().ssub_overflow(left, right),
                            Kind::Star => self.builder.ins().smul_overflow(left, right),
                            _ => unreachable!(),
                        };
                        self.guard(overflow);
                        value
                    }
                    Kind::Slash | Kind::Percent => {
                        let zero = self.builder.ins().icmp_imm_s(IntCC::Equal, right, 0);
                        self.guard(zero);
                        let min = self.builder.ins().icmp_imm_s(IntCC::Equal, left, i64::MIN);
                        let neg = self.builder.ins().icmp_imm_s(IntCC::Equal, right, -1);
                        let invalid = self.builder.ins().band(min, neg);
                        self.guard(invalid);
                        if *op == Kind::Slash {
                            self.builder.ins().sdiv(left, right)
                        } else {
                            self.builder.ins().srem(left, right)
                        }
                    }
                    _ => {
                        let condition = match op {
                            Kind::Lt => IntCC::SignedLessThan,
                            Kind::Le => IntCC::SignedLessThanOrEqual,
                            Kind::Gt => IntCC::SignedGreaterThan,
                            Kind::Ge => IntCC::SignedGreaterThanOrEqual,
                            Kind::EqEq => IntCC::Equal,
                            Kind::Ne => IntCC::NotEqual,
                            _ => unreachable!(),
                        };
                        let value = self.builder.ins().icmp(condition, left, right);
                        self.builder.ins().uextend(I64, value)
                    }
                }
            }
            ExprKind::VecMap {
                vector,
                callbacks,
                source,
                target,
                grow,
            } => {
                let mut handle = lower!(self.scalar(vector));
                let mut codes = Vec::with_capacity(callbacks.len());
                for callback in callbacks {
                    codes.push(lower!(self.scalar(callback)));
                }
                self.consume(vector);
                for callback in callbacks {
                    self.consume(callback);
                }
                let source_width = self.program.width(*source);
                let target_width = self.program.width(*target);
                let element_width = if *grow {
                    // Grow or compact storage once, move elements safely, and
                    // update the header before any callback runs. The loop then
                    // reads and writes at the final stride in source order.
                    let source_words = self.constant(source_width as i64);
                    let target_words = self.constant(target_width as i64);
                    handle =
                        self.runtime_call(self.vec_restride, &[handle, source_words, target_words]);
                    target_width
                } else {
                    source_width
                };
                let length = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0);
                let head = self.builder.create_block();
                let body = self.builder.create_block();
                let done = self.builder.create_block();
                self.builder.append_block_param(head, I64);
                let zero = self.constant(0);
                self.jump(head, &[zero]);
                self.builder.switch_to_block(head);
                let index = self.builder.block_params(head)[0];
                let more = self
                    .builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThan, index, length);
                self.builder.ins().brif(more, body, &[], done, &[]);
                self.builder.switch_to_block(body);
                // Elements are transferred to the callback by value; storage is
                // overwritten only with the callback's result.
                let stride = self
                    .builder
                    .ins()
                    .imul_imm_s(index, (element_width * 8) as i64);
                let address = self.builder.ins().iadd(handle, stride);
                // The destination stride is the final width, but the value
                // currently in the slot still has the source width until the
                // first callback consumes it.
                let mut current = self.load_words(address, 24, source_width);
                for (code, callback) in codes.iter().zip(callbacks.iter()) {
                    let Type::Fn(id) = callback.ty else {
                        unreachable!("checked map callback")
                    };
                    let signature = self.program.function_types[id].clone();
                    let result = signature.result;
                    let pointer = if aggregate_result(self.program, result) {
                        let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                            ir::StackSlotKind::ExplicitSlot,
                            (self.program.width(result) * 8).max(1) as u32,
                            3,
                        ));
                        Some(self.builder.ins().stack_addr(I64, slot, 0))
                    } else {
                        None
                    };
                    let mut values = Vec::new();
                    if let Some(pointer) = pointer {
                        values.push(pointer);
                    }
                    values.extend(current.iter().copied());
                    let signature = self.indirect_signature(id);
                    let signature = self.builder.import_signature(signature);
                    let call = self.builder.ins().call_indirect(signature, *code, &values);
                    current = if let Some(pointer) = pointer {
                        self.load_words(pointer, 0, self.program.width(result))
                    } else {
                        self.builder.inst_results(call).to_vec()
                    };
                }
                let destination_stride = self
                    .builder
                    .ins()
                    .imul_imm_s(index, (target_width * 8) as i64);
                let destination = self.builder.ins().iadd(handle, destination_stride);
                for (word, value) in current.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        destination,
                        (24 + word * 8) as i32,
                    );
                }
                let next = self.builder.ins().iadd_imm_s(index, 1);
                self.jump(head, &[next]);
                self.builder.switch_to_block(done);
                // Later vector operations use the compacted element width.
                let width = self.constant(target_width as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), width, handle, 16);
                handle
            }
            ExprKind::TaskSpawn {
                body,
                result,
                obligation,
            } => {
                let values = lower!(self.expr(body));
                let Type::Once(id) = body.ty else {
                    unreachable!("checked task body is once")
                };
                self.consume(body);
                let wrapper = self.task_wrappers[&id];
                let wrapper = self.module.declare_func_in_func(wrapper, self.builder.func);
                let wrapper = self.builder.ins().func_addr(I64, wrapper);
                let bytes = self.constant((self.program.width(*result).max(1) * 8) as i64);
                let drop = if self.program.owns(*result) {
                    let drop = self.task_pointer_drops[&result.full()];
                    let drop = self.module.declare_func_in_func(drop, self.builder.func);
                    self.builder.ins().func_addr(I64, drop)
                } else {
                    self.constant(0)
                };
                let preserve = self.constant(i64::from(*obligation));
                self.runtime_call(
                    self.task_spawn,
                    &[wrapper, values[0], values[1], bytes, drop, preserve],
                )
            }
            ExprKind::TaskScope {
                body,
                result,
                failure,
                ..
            } => {
                let values = lower!(self.expr(body));
                let Type::Once(id) = body.ty else {
                    unreachable!("checked scope body is once")
                };
                self.consume(body);
                let result_ty = self.program.function_types[id].result;
                let aggregate = aggregate_result(self.program, result_ty);
                let pointer = if aggregate {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (self.program.width(result_ty).max(1) * 8) as u32,
                        3,
                    ));
                    Some(self.builder.ins().stack_addr(I64, slot, 0))
                } else {
                    None
                };
                self.runtime_void(self.task_scope_begin, &[]);
                let mut arguments = Vec::new();
                if let Some(pointer) = pointer {
                    arguments.push(pointer);
                }
                arguments.push(values[1]);
                let signature = self.indirect_signature(id);
                let signature = self.builder.import_signature(signature);
                let call = self
                    .builder
                    .ins()
                    .call_indirect(signature, values[0], &arguments);
                let result_values = if let Some(pointer) = pointer {
                    self.load_words(pointer, 0, self.program.width(result_ty))
                } else {
                    self.builder.inst_results(call).to_vec()
                };
                if result_ty == Type::Never {
                    self.runtime_void(self.task_scope_end, &[]);
                    return None;
                }
                if let Some(shape) = *failure {
                    let failed = self.builder.create_block();
                    let succeeded = self.builder.create_block();
                    let done = self.builder.create_block();
                    let condition = self.builder.ins().icmp_imm_s(
                        IntCC::Equal,
                        result_values[0],
                        shape.err_tag as i64,
                    );
                    self.builder
                        .ins()
                        .brif(condition, failed, &[], succeeded, &[]);
                    self.builder.switch_to_block(failed);
                    self.runtime_void(self.task_cancel_scope, &[]);
                    self.jump(done, &[]);
                    self.builder.switch_to_block(succeeded);
                    self.jump(done, &[]);
                    self.builder.switch_to_block(done);
                }
                self.runtime_void(self.task_scope_end, &[]);
                let _ = result;
                return Some(result_values);
            }
            ExprKind::TaskYield => self.runtime_call(self.task_yield, &[]),
            ExprKind::TaskCheckCancel => self.runtime_call(self.task_check_cancel, &[]),
            ExprKind::TaskCancel(reference) => {
                let pointer = lower!(self.scalar(reference));
                self.runtime_void(self.task_cancel, &[pointer]);
                self.constant(0)
            }
            ExprKind::TaskJoin { task, exit, .. } => {
                let handle = lower!(self.scalar(task));
                self.consume(task);
                let width = self.program.width(exit.payload).max(1);
                let out = self.stack_words(width);
                let status = self.runtime_call(self.task_join, &[handle, out]);
                let completed = self.builder.create_block();
                let cancelled = self.builder.create_block();
                let join = self.join(exit.result).unwrap();
                let condition = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
                self.builder
                    .ins()
                    .brif(condition, completed, &[], cancelled, &[]);
                self.builder.switch_to_block(completed);
                let payload = self.load_words(out, 0, width);
                let mut values = vec![self.constant(exit.completed_tag as i64)];
                values.extend(payload);
                while values.len() < self.program.width(exit.result) {
                    values.push(self.constant(0));
                }
                self.jump(join, &values);
                self.builder.switch_to_block(cancelled);
                let payload = self.load_words(out, 0, width);
                self.drop_value(exit.payload, &payload);
                let mut values = vec![self.constant(exit.cancelled_tag as i64)];
                while values.len() < self.program.width(exit.result) {
                    values.push(self.constant(0));
                }
                self.jump(join, &values);
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
            ExprKind::Call(target, args) => {
                let erased_parameters = match target {
                    Target::Function(index)
                    | Target::ObjectFunction {
                        function: index, ..
                    } => {
                        let function = &self.program.functions[*index];
                        (0..args.len())
                            .map(|position| {
                                function
                                    .parameter_grades
                                    .get(position)
                                    .copied()
                                    .flatten()
                                    .is_some_and(Grade::is_zero)
                            })
                            .collect::<Vec<_>>()
                    }
                    _ => Vec::new(),
                };
                let mut values = Vec::new();
                for (position, arg) in args.iter().enumerate() {
                    let words = lower!(self.expr(arg));
                    if erased_parameters.get(position).copied() != Some(true) {
                        values.extend(words);
                    }
                }
                for arg in args {
                    self.consume(arg);
                }
                match target {
                    Target::Io(op, shape) => match op {
                        IoOp::Stdin => self.constant(0),
                        IoOp::Stdout => self.constant(1),
                        IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk | IoOp::Write => {
                            let ok_value = if matches!(op, IoOp::Write) {
                                values[1] = self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    values[1],
                                    0,
                                );
                                self.constant(0)
                            } else {
                                values[1]
                            };
                            let callee = if matches!(op, IoOp::ReadAll) {
                                self.read_all
                            } else if matches!(op, IoOp::ReadLine) {
                                self.read_line
                            } else if matches!(op, IoOp::ReadChunk) {
                                self.read_chunk
                            } else {
                                self.write
                            };
                            let status = self.runtime_call(callee, &values);
                            let success = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
                            let shape = shape.expect("checked I/O result shape");
                            let ok_tag = self.constant(shape.ok_tag as i64);
                            let err_tag = self.constant(shape.err_tag as i64);
                            let tag = self.builder.ins().select(success, ok_tag, err_tag);
                            let payload = self.builder.ins().select(success, ok_value, status);
                            return Some(vec![tag, payload]);
                        }
                    },
                    Target::Bytes(op) => {
                        if op.borrowed() {
                            values[0] =
                                self.builder
                                    .ins()
                                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                        }
                        self.runtime_call(self.bytes_ops[op], &values)
                    }
                    Target::String(op) => {
                        if op.borrowed() {
                            values[0] =
                                self.builder
                                    .ins()
                                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                        }
                        match op {
                            StringOp::Len => {
                                self.runtime_call(self.bytes_ops[&BytesOp::Len], &values)
                            }
                            StringOp::ScalarLen => {
                                self.runtime_call(self.string_scalar_len, &values)
                            }
                            StringOp::ByteAt => {
                                self.runtime_call(self.bytes_ops[&BytesOp::Get], &values)
                            }
                            StringOp::AsBytes => {
                                self.runtime_call(self.bytes_ops[&BytesOp::Copy], &values)
                            }
                            StringOp::IntoBytes => values[0],
                            StringOp::ScalarAt { some_tag, none_tag } => {
                                let codepoint = self.runtime_call(self.string_scalar_at, &values);
                                let present = self.builder.ins().icmp_imm_s(
                                    IntCC::SignedGreaterThanOrEqual,
                                    codepoint,
                                    0,
                                );
                                let some = self.constant(*some_tag as i64);
                                let none = self.constant(*none_tag as i64);
                                let tag = self.builder.ins().select(present, some, none);
                                let zero = self.constant(0);
                                let payload = self.builder.ins().select(present, codepoint, zero);
                                let width = self.program.width(expr.ty);
                                let mut words = vec![tag, payload];
                                while words.len() < width {
                                    words.push(zero);
                                }
                                return Some(words);
                            }
                            StringOp::FromUtf8 { ok_tag, err_tag } => {
                                let valid = self.runtime_call(self.string_validate, &values);
                                let present =
                                    self.builder.ins().icmp_imm_s(IntCC::NotEqual, valid, 0);
                                let ok = self.constant(*ok_tag as i64);
                                let err = self.constant(*err_tag as i64);
                                let tag = self.builder.ins().select(present, ok, err);
                                let width = self.program.width(expr.ty);
                                let mut words = vec![tag, values[0]];
                                while words.len() < width {
                                    words.push(self.constant(0));
                                }
                                return Some(words);
                            }
                        }
                    }
                    Target::Str(op) => return Some(self.str_call(*op, values)),
                    Target::Function(index)
                    | Target::ObjectFunction {
                        function: index, ..
                    } => return Some(self.function_call(*index, values)),
                    Target::DynCall { spec, .. } => return Some(self.dyn_call(*spec, values)),
                    Target::UnionBorrowCall { spec, .. } => {
                        return Some(self.union_borrow_call(*spec, values));
                    }
                    Target::Vec(op, element) => return Some(self.vec_call(*op, *element, values)),
                    Target::AllocVec(op, element) => {
                        return Some(self.alloc_vec_call(*op, *element, values));
                    }
                    Target::Slice(op, element) => {
                        return Some(self.slice_call(*op, *element, values));
                    }
                    Target::DynArray(op, element) => {
                        return Some(self.dyn_array_call(*op, *element, values));
                    }
                    Target::Print => self.runtime_call(self.print, &values),
                    Target::PrintInt(kind) => {
                        let callee = if *kind == IntKind::U64 {
                            self.print_u64
                        } else {
                            self.print
                        };
                        self.runtime_call(callee, &values)
                    }
                    Target::PrintFloat(kind) => {
                        let callee = match kind {
                            FloatKind::F32 => self.print_f32,
                            FloatKind::F64 => self.print_f64,
                        };
                        self.runtime_call(callee, &values)
                    }
                    Target::Float(op) => {
                        return Some(self.float_builtin(*op, &values, expr.ty));
                    }
                    Target::Int(op, source, target) => {
                        return Some(self.int_builtin(*op, *source, *target, &values, expr.ty));
                    }
                    Target::Panic => {
                        self.abort();
                        return None;
                    }
                }
            }
            ExprKind::Return(arg) => {
                let value = lower!(self.expr(arg));
                self.consume(arg);
                self.cleanup_all();
                let erased_result = self.program.functions[self.function_index]
                    .result_grade
                    .is_some_and(Grade::is_zero);
                if erased_result {
                    self.drop_value(arg.ty, &value);
                    self.return_value(&[]);
                } else {
                    self.return_value(&value);
                }
                return None;
            }
            ExprKind::If(condition, yes, no) => {
                let condition = lower!(self.scalar(condition));
                let hit = self.builder.create_block();
                let miss = self.builder.create_block();
                let join = self.join(expr.ty);
                self.builder.ins().brif(condition, hit, &[], miss, &[]);
                self.builder.switch_to_block(hit);
                if let Some(values) = self.block(yes) {
                    self.jump(join.unwrap(), &values);
                }
                self.builder.switch_to_block(miss);
                if let Some(values) = self.block(no) {
                    self.jump(join.unwrap(), &values);
                }
                let join = join?;
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
            ExprKind::Match(value, arms) => {
                let input = value;
                let value = lower!(self.expr(input));
                let join = self.join(expr.ty);
                for arm in arms {
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    let condition = self.pattern(&arm.pattern, &value);
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    self.bind_pattern(&arm.pattern, &value);
                    let mut body_reachable = true;
                    if let Some(guard) = &arm.guard {
                        if let Some(guard) = self.scalar(guard) {
                            let body = self.builder.create_block();
                            self.builder.ins().brif(guard, body, &[], next, &[]);
                            self.builder.switch_to_block(body);
                        } else {
                            body_reachable = false;
                        }
                    }
                    if body_reachable {
                        self.consume(input);
                        self.dispose_pattern(&arm.pattern, input.ty, &value);
                        if let Some(body) = self.expr(&arm.body) {
                            self.consume(&arm.body);
                            let mut slots = std::collections::BTreeSet::new();
                            crate::ownership::pattern_bindings(&arm.pattern, &mut slots);
                            for slot in slots.into_iter().rev() {
                                self.cleanup(
                                    self.program.functions[self.function_index].local_resources
                                        [slot],
                                );
                            }
                            self.jump(join.unwrap(), &body);
                        }
                    }
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                let join = join?;
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
        };
        Some(vec![scalar])
    }
    /// Allocate one owned dynamic-object payload and copy the concrete member
    /// words into it. The corresponding `free` happens in `drop_value` for an
    /// owned object or immediately before an owning method consumes it.
    fn allocate_dyn_payload(&mut self, ty: Type, values: &[Value]) -> Value {
        let bytes = self.constant((self.program.width(ty) * 8) as i64);
        let pointer = self.runtime_call(self.allocate, &[bytes]);
        for (index, value) in values.iter().enumerate() {
            self.builder
                .ins()
                .store(ir::MemFlagsData::new(), *value, pointer, (index * 8) as i32);
        }
        pointer
    }
    fn stack_words(&mut self, words: usize) -> Value {
        let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
            ir::StackSlotKind::ExplicitSlot,
            (words.max(1) * 8) as u32,
            3,
        ));
        self.builder.ins().stack_addr(I64, slot, 0)
    }
    fn store_words(&mut self, pointer: Value, values: &[Value]) {
        for (i, v) in values.iter().enumerate() {
            self.builder
                .ins()
                .store(ir::MemFlagsData::new(), *v, pointer, (i * 8) as i32);
        }
    }
    fn load_words(&mut self, pointer: Value, offset: i32, words: usize) -> Words {
        (0..words)
            .map(|i| {
                self.builder.ins().load(
                    I64,
                    ir::MemFlagsData::new(),
                    pointer,
                    offset + (i * 8) as i32,
                )
            })
            .collect()
    }
    /// Reject a text range endpoint that falls inside a UTF-8 continuation
    /// sequence. `index` must already be in `0..=length`; `index == length` is
    /// always a boundary and is not dereferenced.
    fn check_text_boundary(&mut self, pointer: Value, index: Value, length: Value) {
        let at_end = self.builder.ins().icmp(IntCC::Equal, index, length);
        let check = self.builder.create_block();
        let good = self.builder.create_block();
        self.builder.ins().brif(at_end, good, &[], check, &[]);
        self.builder.switch_to_block(check);
        let address = self.builder.ins().iadd(pointer, index);
        let byte = self
            .builder
            .ins()
            .uload8(I64, ir::MemFlagsData::new(), address, 0);
        let masked = self.builder.ins().band_imm_s(byte, 0xC0);
        let continuation = self.builder.ins().icmp_imm_s(IntCC::Equal, masked, 0x80);
        let bad = self.builder.create_block();
        let ok = self.builder.create_block();
        self.builder.ins().brif(continuation, bad, &[], ok, &[]);
        self.builder.switch_to_block(bad);
        self.abort();
        self.builder.switch_to_block(ok);
        self.jump(good, &[]);
        self.builder.switch_to_block(good);
    }
    fn check_range(&mut self, start: Value, end: Value, length: Value) {
        let negative = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, start, 0);
        let reversed = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThan, start, end);
        let beyond = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThan, end, length);
        let invalid = self.builder.ins().bor(negative, reversed);
        let invalid = self.builder.ins().bor(invalid, beyond);
        self.guard(invalid);
    }
    fn str_call(&mut self, op: StrOp, values: Words) -> Words {
        let (pointer, length) = (values[0], values[1]);
        match op {
            StrOp::Len => vec![length],
            StrOp::ScalarLen => vec![self.runtime_call(self.str_scalar_len, &[pointer, length])],
            StrOp::ByteAt => {
                vec![self.runtime_call(self.str_byte_at, &[pointer, length, values[4]])]
            }
            StrOp::ScalarAt { some_tag, none_tag } => {
                let codepoint =
                    self.runtime_call(self.str_scalar_at, &[pointer, length, values[4]]);
                let present =
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedGreaterThanOrEqual, codepoint, 0);
                let some = self.constant(some_tag as i64);
                let none = self.constant(none_tag as i64);
                let tag = self.builder.ins().select(present, some, none);
                let zero = self.constant(0);
                let payload = self.builder.ins().select(present, codepoint, zero);
                vec![tag, payload]
            }
            StrOp::ToString => {
                vec![self.runtime_call(self.str_to_string, &[pointer, length])]
            }
        }
    }
    /// Compare the words of two structural records field by field. The checker
    /// admits only scalar leaves and nested structural rows, so every compared
    /// word is a copyable representation word.
    fn struct_eq_words(&mut self, ty: Type, left: &[Value], right: &[Value]) -> Value {
        let layout = ty
            .layout()
            .expect("checked structural equality has a layout");
        let types = self.program.enums[layout].variants[0].fields.clone();
        let mut result: Option<Value> = None;
        let mut offset = 1usize;
        for field in types {
            let width = self.program.width(field);
            if width > 0 {
                let equal = if field.layout().is_some() {
                    self.struct_eq_words(
                        field,
                        &left[offset..offset + width],
                        &right[offset..offset + width],
                    )
                } else {
                    self.builder
                        .ins()
                        .icmp(IntCC::Equal, left[offset], right[offset])
                };
                result = Some(match result {
                    Some(previous) => self.builder.ins().band(previous, equal),
                    None => equal,
                });
            }
            offset += width;
        }
        match result {
            Some(value) => value,
            None => {
                let zero = self.constant(0);
                self.builder.ins().icmp_imm_s(IntCC::Equal, zero, 0i64)
            }
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn struct_coercion_words(
        &mut self,
        source: Type,
        target_fields: &[Type],
        kept: &[(usize, usize, Option<Coercion>)],
        drops: &[(usize, Type)],
        values: &[Value],
        out: &mut Vec<Value>,
    ) {
        let source_id = source.layout().expect("checked structural source layout");
        let source_fields = self.program.enums[source_id].variants[0].fields.clone();
        let mut offsets = Vec::with_capacity(source_fields.len());
        let mut offset = 1usize;
        for field in &source_fields {
            offsets.push(offset);
            offset += self.program.width(*field);
        }
        for (target_index, source_index, coercion) in kept {
            let start = offsets[*source_index];
            let field_width = self.program.width(source_fields[*source_index]);
            let field = &values[start..start + field_width];
            match coercion {
                Some(coercion) => out.extend(self.nested_coercion_words(
                    coercion,
                    target_fields[*target_index],
                    field,
                )),
                None => out.extend(field.iter().copied()),
            }
        }
        for (source_index, ty) in drops {
            let start = offsets[*source_index];
            let field_width = self.program.width(*ty);
            self.drop_value(*ty, &values[start..start + field_width]);
        }
    }
    fn nested_coercion_words(&mut self, coercion: &Coercion, to: Type, values: &[Value]) -> Words {
        let width = self.program.width(to);
        match coercion {
            Coercion::Inject { tag } => {
                let mut out = Vec::with_capacity(width);
                out.push(self.constant(*tag as i64));
                out.extend(values.iter().copied().take(width.saturating_sub(1)));
                while out.len() < width {
                    out.push(self.constant(0));
                }
                out
            }
            Coercion::Struct {
                source,
                kept,
                drops,
            } => {
                let target_id = to.layout().expect("checked nested structural target");
                let target_fields = self.program.enums[target_id].variants[0].fields.clone();
                let mut out = vec![self.constant(0)];
                self.struct_coercion_words(*source, &target_fields, kept, drops, values, &mut out);
                while out.len() < width {
                    out.push(self.constant(0));
                }
                out
            }
            Coercion::Repack { map } => {
                let exit = self.join(to).expect("nested repack target is not Never");
                for (source_tag, target_tag) in map.iter().enumerate() {
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    let condition =
                        self.builder
                            .ins()
                            .icmp_imm_s(IntCC::Equal, values[0], source_tag as i64);
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    let mut out = Vec::with_capacity(width);
                    out.push(self.constant(*target_tag as i64));
                    out.extend(values.iter().copied().skip(1).take(width.saturating_sub(1)));
                    while out.len() < width {
                        out.push(self.constant(0));
                    }
                    self.jump(exit, &out);
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                self.builder.switch_to_block(exit);
                self.builder.block_params(exit).to_vec()
            }
            Coercion::DynBox {
                member,
                member_type,
                ..
            } => {
                let pointer = self.allocate_dyn_payload(*member_type, values);
                vec![self.constant(*member as i64), pointer]
            }
            Coercion::Callable {
                function,
                capture,
                target,
            } => {
                let reference = self
                    .module
                    .declare_func_in_func(self.ids[*function], self.builder.func);
                let code = self.builder.ins().func_addr(I64, reference);
                if !matches!(target, Type::Once(_)) {
                    return vec![code];
                }
                let Some(capture_ty) = capture else {
                    return vec![code, self.constant(0)];
                };
                let types = vec![capture_ty.full()];
                let bytes = 8 + self.program.width(*capture_ty) * 8;
                let size = self.constant(bytes as i64);
                let environment = self.runtime_call(self.allocate, &[size]);
                let drop = self.closure_drops[&types];
                let drop = self.module.declare_func_in_func(drop, self.builder.func);
                let drop = self.builder.ins().func_addr(I64, drop);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), drop, environment, 0);
                let width = self.program.width(*capture_ty);
                for (index, value) in values.iter().take(width).enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *value,
                        environment,
                        8 + (index * 8) as i32,
                    );
                }
                vec![code, environment]
            }
        }
    }
    fn dyn_array_call(&mut self, op: DynArrayOp, element: Type, values: Words) -> Words {
        let pointer = values[0];
        let length = self
            .builder
            .ins()
            .load(I64, ir::MemFlagsData::new(), pointer, 0);
        match op {
            DynArrayOp::Len => vec![length],
            DynArrayOp::Get => {
                let index = values[1];
                let negative = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThan, index, 0);
                let past_end =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length);
                let bad = self.builder.ins().bor(negative, past_end);
                self.guard(bad);
                let width = self.program.width(element);
                let stride = self.builder.ins().imul_imm_s(index, (width * 8) as i64);
                let base = self.builder.ins().iadd(pointer, stride);
                (0..width)
                    .map(|word| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            base,
                            (8 + word * 8) as i32,
                        )
                    })
                    .collect()
            }
        }
    }
    fn slice_call(&mut self, op: SliceOp, element: Type, values: Words) -> Words {
        let element_width = self.program.width(element);
        let (pointer, length, stride, bytes) = (values[0], values[1], values[2], values[3]);
        if op == SliceOp::Len {
            return vec![length];
        }
        let index = values[4];
        if op == SliceOp::Set {
            let negative = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::SignedLessThan, index, 0);
            let beyond = self
                .builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, index, length);
            let invalid = self.builder.ins().bor(negative, beyond);
            self.guard(invalid);
            let offset = self.builder.ins().imul(index, stride);
            let address = self.builder.ins().iadd(pointer, offset);
            let value = values[5];
            if element_width != 1 {
                for word in 0..element_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        values[5 + word],
                        address,
                        (word * 8) as i32,
                    );
                }
            } else {
                let byte = self.builder.ins().icmp_imm_s(IntCC::NotEqual, bytes, 0);
                let scalar = self.builder.create_block();
                let words = self.builder.create_block();
                let join = self.builder.create_block();
                self.builder.ins().brif(byte, scalar, &[], words, &[]);
                self.builder.switch_to_block(scalar);
                let negative = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThan, value, 0);
                let too_large = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::SignedGreaterThan, value, 255);
                let invalid = self.builder.ins().bor(negative, too_large);
                self.guard(invalid);
                self.builder
                    .ins()
                    .istore8(ir::MemFlagsData::new(), value, address, 0);
                self.jump(join, &[]);
                self.builder.switch_to_block(words);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), value, address, 0);
                self.jump(join, &[]);
                self.builder.switch_to_block(join);
            }
            return vec![self.constant(0)];
        }
        if let SliceOp::TryGet {
            some_tag,
            none_tag,
            option,
        } = op
        {
            let negative = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::SignedLessThan, index, 0);
            let beyond = self
                .builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, index, length);
            let invalid = self.builder.ins().bor(negative, beyond);
            let valid = self.builder.ins().icmp_imm_s(IntCC::Equal, invalid, 0);
            // Use the real instantiated enum layout rather than deriving it
            // from the element width, so aggregate and union payloads keep
            // the exact ABI of `Option<T>`.
            let option_width = self.program.enums[option].words;
            let some = self.builder.create_block();
            let none = self.builder.create_block();
            let join = self.builder.create_block();
            for _ in 0..option_width {
                self.builder.append_block_param(join, I64);
            }
            self.builder.ins().brif(valid, some, &[], none, &[]);
            self.builder.switch_to_block(some);
            // The element is only read on the in-bounds branch; nothing is
            // loaded from the view before the bounds test.
            let offset = self.builder.ins().imul(index, stride);
            let address = self.builder.ins().iadd(pointer, offset);
            let payload: Vec<Value> = if element_width != 1 {
                self.load_words(address, 0, element_width)
            } else {
                let byte = self.builder.ins().icmp_imm_s(IntCC::NotEqual, bytes, 0);
                let scalar = self.builder.create_block();
                let words = self.builder.create_block();
                let loaded = self.builder.create_block();
                self.builder.append_block_param(loaded, I64);
                self.builder.ins().brif(byte, scalar, &[], words, &[]);
                self.builder.switch_to_block(scalar);
                let value = self
                    .builder
                    .ins()
                    .uload8(I64, ir::MemFlagsData::new(), address, 0);
                self.jump(loaded, &[value]);
                self.builder.switch_to_block(words);
                let value = self.load_words(address, 0, 1);
                self.jump(loaded, &value);
                self.builder.switch_to_block(loaded);
                self.builder.block_params(loaded).to_vec()
            };
            let mut some_values = Vec::with_capacity(option_width);
            some_values.push(self.constant(some_tag as i64));
            some_values.extend(payload);
            while some_values.len() < option_width {
                some_values.push(self.constant(0));
            }
            self.jump(join, &some_values);
            self.builder.switch_to_block(none);
            let none_values: Vec<Value> = (0..option_width)
                .map(|word| {
                    if word == 0 {
                        self.constant(none_tag as i64)
                    } else {
                        self.constant(0)
                    }
                })
                .collect();
            self.jump(join, &none_values);
            self.builder.switch_to_block(join);
            return self.builder.block_params(join).to_vec();
        }
        if op == SliceOp::Get {
            let negative = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::SignedLessThan, index, 0);
            let beyond = self
                .builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, index, length);
            let invalid = self.builder.ins().bor(negative, beyond);
            self.guard(invalid);
        }
        let offset = self.builder.ins().imul(index, stride);
        let address = self.builder.ins().iadd(pointer, offset);
        // Only byte-backed slices (`&[i64]` over Bytes) can set the flag, and
        // their elements are one word wide. Wider elements always use word loads.
        if element_width != 1 {
            return self.load_words(address, 0, element_width);
        }
        let byte = self.builder.ins().icmp_imm_s(IntCC::NotEqual, bytes, 0);
        let scalar = self.builder.create_block();
        let words = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, I64);
        self.builder.ins().brif(byte, scalar, &[], words, &[]);
        self.builder.switch_to_block(scalar);
        let value = self
            .builder
            .ins()
            .uload8(I64, ir::MemFlagsData::new(), address, 0);
        self.jump(join, &[value]);
        self.builder.switch_to_block(words);
        let loaded = self.load_words(address, 0, 1);
        self.jump(join, &loaded);
        self.builder.switch_to_block(join);
        self.builder.block_params(join).to_vec()
    }
    /// Lower allocator-backed vector operations. Metadata is one stable
    /// handle; element storage is a user-allocator block reached through the
    /// imported helpers, so growth and release always use the recorded pair.
    fn alloc_vec_call(&mut self, op: AllocVecOp, element: Type, values: Words) -> Words {
        let width = self.program.width(element);
        match op {
            AllocVecOp::Len => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                vec![self.runtime_call(self.alloc_ops.vec_len, &[handle])]
            }
            AllocVecOp::Get => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let out = self.stack_words(width);
                self.runtime_void(self.alloc_ops.vec_get, &[handle, values[1], out]);
                self.load_words(out, 0, width)
            }
            AllocVecOp::Push => {
                let item = self.stack_words(width);
                self.store_words(item, &values[1..1 + width]);
                let handle = self.runtime_call(self.alloc_ops.vec_push, &[values[0], item]);
                vec![handle]
            }
            AllocVecOp::Set => {
                let item = self.stack_words(width);
                self.store_words(item, &values[2..2 + width]);
                let old = self.stack_words(width);
                let handle =
                    self.runtime_call(self.alloc_ops.vec_set, &[values[0], values[1], item, old]);
                let previous = self.load_words(old, 0, width);
                self.drop_value(element, &previous);
                vec![handle]
            }
            AllocVecOp::Clear => {
                let handle = values[0];
                if self.program.owns(element) {
                    let length = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0);
                    let data = self.runtime_call(self.alloc_ops.vec_data, &[handle]);
                    let head = self.builder.create_block();
                    let body = self.builder.create_block();
                    let done = self.builder.create_block();
                    self.builder.append_block_param(head, I64);
                    self.jump(head, &[length]);
                    self.builder.switch_to_block(head);
                    let index = self.builder.block_params(head)[0];
                    let more = self.builder.ins().icmp_imm_s(IntCC::NotEqual, index, 0);
                    self.builder.ins().brif(more, body, &[], done, &[]);
                    self.builder.switch_to_block(body);
                    let previous = self.builder.ins().iadd_imm_s(index, -1);
                    let stride = self.builder.ins().imul_imm_s(previous, (width * 8) as i64);
                    let slot = self.builder.ins().iadd(data, stride);
                    let fields = self.load_words(slot, 0, width);
                    self.drop_value(element, &fields);
                    self.jump(head, &[previous]);
                    self.builder.switch_to_block(done);
                }
                self.runtime_void(self.alloc_ops.vec_clear, &[handle]);
                vec![handle]
            }
        }
    }
    fn vec_call(&mut self, op: VecOp, element: Type, values: Words) -> Words {
        let width = self.program.width(element);
        let call = |g: &mut Self, op: VecOp, args: &[Value]| {
            let callee = g
                .module
                .declare_func_in_func(g.vec_ops[&op], g.builder.func);
            let call = g.builder.ins().call(callee, args);
            g.builder.inst_results(call).to_vec()
        };
        match op {
            VecOp::WithCapacity => {
                let w = self.constant(width as i64);
                call(self, op, &[values[0], w])
            }
            VecOp::Reserve => call(self, op, &[values[0], values[1]]),
            VecOp::TryReserve { ok_tag, err_tag } => {
                let grown = call(
                    self,
                    VecOp::TryReserve {
                        ok_tag: 0,
                        err_tag: 0,
                    },
                    &[values[0], values[1]],
                )[0];
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, grown, 0);
                let ok = self.constant(ok_tag as i64);
                let error = self.constant(err_tag as i64);
                let tag = self.builder.ins().select(failed, error, ok);
                let owner = self.builder.ins().select(failed, values[0], grown);
                vec![tag, owner]
            }
            VecOp::ClearBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                if self.program.owns(element) {
                    let length = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0);
                    let head = self.builder.create_block();
                    let body = self.builder.create_block();
                    let done = self.builder.create_block();
                    self.builder.append_block_param(head, I64);
                    self.jump(head, &[length]);
                    self.builder.switch_to_block(head);
                    let index = self.builder.block_params(head)[0];
                    let more = self.builder.ins().icmp_imm_s(IntCC::NotEqual, index, 0);
                    self.builder.ins().brif(more, body, &[], done, &[]);
                    self.builder.switch_to_block(body);
                    let previous = self.builder.ins().iadd_imm_s(index, -1);
                    let stride = self.builder.ins().imul_imm_s(previous, (width * 8) as i64);
                    let slot = self.builder.ins().iadd(handle, stride);
                    let fields = self.load_words(slot, 24, width);
                    self.drop_value(element, &fields);
                    self.jump(head, &[previous]);
                    self.builder.switch_to_block(done);
                }
                let zero = self.constant(0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, handle, 0);
                vec![self.constant(0)]
            }
            VecOp::ReserveBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let grown = call(self, VecOp::Reserve, &[handle, values[1]])[0];
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), grown, reference, 0);
                vec![self.constant(0)]
            }
            VecOp::PushBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let item = self.stack_words(width);
                self.store_words(item, &values[1..1 + width]);
                let grown = call(self, VecOp::Push, &[handle, item])[0];
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), grown, reference, 0);
                vec![self.constant(0)]
            }
            VecOp::SetBorrowed => {
                let reference = values[0];
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let item = self.stack_words(width);
                self.store_words(item, &values[2..2 + width]);
                let old = self.stack_words(width);
                call(self, VecOp::Set, &[handle, values[1], item, old]);
                let previous = self.load_words(old, 0, width);
                self.drop_value(element, &previous);
                vec![self.constant(0)]
            }
            VecOp::Clear => {
                let handle = values[0];
                if self.program.owns(element) {
                    // Release elements from the end. Each slot is dropped
                    // exactly once; the vector header and storage stay alive.
                    let length = self
                        .builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0);
                    let head = self.builder.create_block();
                    let body = self.builder.create_block();
                    let done = self.builder.create_block();
                    self.builder.append_block_param(head, I64);
                    self.jump(head, &[length]);
                    self.builder.switch_to_block(head);
                    let index = self.builder.block_params(head)[0];
                    let more = self.builder.ins().icmp_imm_s(IntCC::NotEqual, index, 0);
                    self.builder.ins().brif(more, body, &[], done, &[]);
                    self.builder.switch_to_block(body);
                    let previous = self.builder.ins().iadd_imm_s(index, -1);
                    let stride = self.builder.ins().imul_imm_s(previous, (width * 8) as i64);
                    let slot = self.builder.ins().iadd(handle, stride);
                    let fields = self.load_words(slot, 24, width);
                    self.drop_value(element, &fields);
                    self.jump(head, &[previous]);
                    self.builder.switch_to_block(done);
                }
                let zero = self.constant(0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, handle, 0);
                vec![handle]
            }
            VecOp::Len => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                call(self, op, &[handle])
            }
            VecOp::Get => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let out = self.stack_words(width);
                call(self, op, &[handle, values[1], out]);
                self.load_words(out, 0, width)
            }
            VecOp::At => {
                // Proved in bounds: direct load after the 24-byte header.
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let stride = self.builder.ins().imul_imm_s(values[1], (width * 8) as i64);
                let base = self.builder.ins().iadd(handle, stride);
                self.load_words(base, 24, width)
            }
            VecOp::Push => {
                let item = self.stack_words(width);
                self.store_words(item, &values[1..1 + width]);
                call(self, op, &[values[0], item])
            }
            VecOp::Set => {
                let item = self.stack_words(width);
                self.store_words(item, &values[2..2 + width]);
                let old = self.stack_words(width);
                let handle = call(self, op, &[values[0], values[1], item, old]);
                let previous = self.load_words(old, 0, width);
                self.drop_value(element, &previous);
                handle
            }
        }
    }
    /// Panic unless `value` (a 64-bit result) is in range for `kind`.
    fn check_int_range(&mut self, kind: IntKind, value: Value) -> Value {
        if kind.bits() == 64 {
            return value;
        }
        let canonical = self.canonical(kind, value);
        let wrong = self.builder.ins().icmp(IntCC::NotEqual, canonical, value);
        self.guard(wrong);
        value
    }
    /// Re-extend the low `bits` of a word into the kind's canonical form.
    fn canonical(&mut self, kind: IntKind, value: Value) -> Value {
        let narrow = match kind.bits() {
            8 => ir::types::I8,
            16 => ir::types::I16,
            32 => ir::types::I32,
            _ => return value,
        };
        let low = self.builder.ins().ireduce(narrow, value);
        if kind.signed() {
            self.builder.ins().sextend(I64, low)
        } else {
            self.builder.ins().uextend(I64, low)
        }
    }
    fn int_binary(
        &mut self,
        kind: IntKind,
        op: &Kind,
        left: Value,
        right: Value,
        right_kind: Option<IntKind>,
    ) -> Value {
        let signed = kind.signed();
        let wide = kind.bits() == 64;
        match op {
            Kind::Plus | Kind::Minus | Kind::Star => {
                let (value, overflow) = match (op, signed || !wide) {
                    // Narrow kinds compute exactly in 64 bits, then range-check.
                    (Kind::Plus, true) => self.builder.ins().sadd_overflow(left, right),
                    (Kind::Minus, true) => self.builder.ins().ssub_overflow(left, right),
                    (Kind::Star, true) => self.builder.ins().smul_overflow(left, right),
                    (Kind::Plus, false) => self.builder.ins().uadd_overflow(left, right),
                    (Kind::Minus, false) => self.builder.ins().usub_overflow(left, right),
                    (Kind::Star, false) => self.builder.ins().umul_overflow(left, right),
                    _ => unreachable!(),
                };
                self.guard(overflow);
                self.check_int_range(kind, value)
            }
            Kind::Slash | Kind::Percent => {
                let zero = self.builder.ins().icmp_imm_s(IntCC::Equal, right, 0);
                self.guard(zero);
                if signed {
                    if wide || *op == Kind::Percent {
                        let min_value = kind.encode(kind.min()).unwrap();
                        let min = self.builder.ins().icmp_imm_s(IntCC::Equal, left, min_value);
                        let neg = self.builder.ins().icmp_imm_s(IntCC::Equal, right, -1);
                        let invalid = self.builder.ins().band(min, neg);
                        self.guard(invalid);
                    }
                    let value = if *op == Kind::Slash {
                        self.builder.ins().sdiv(left, right)
                    } else {
                        self.builder.ins().srem(left, right)
                    };
                    self.check_int_range(kind, value)
                } else if *op == Kind::Slash {
                    self.builder.ins().udiv(left, right)
                } else {
                    self.builder.ins().urem(left, right)
                }
            }
            Kind::Amp => self.builder.ins().band(left, right),
            Kind::Pipe => self.builder.ins().bor(left, right),
            Kind::Caret => self.builder.ins().bxor(left, right),
            Kind::Shl | Kind::Shr => {
                // The amount is checked against 0..bits in its own kind.
                let amount_signed = right_kind.is_some_and(IntKind::signed);
                if amount_signed {
                    let negative = self
                        .builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThan, right, 0);
                    self.guard(negative);
                }
                let too_far = self.builder.ins().icmp_imm_u(
                    IntCC::UnsignedGreaterThanOrEqual,
                    right,
                    i64::from(kind.bits()),
                );
                self.guard(too_far);
                let value = if *op == Kind::Shl {
                    self.builder.ins().ishl(left, right)
                } else if signed {
                    self.builder.ins().sshr(left, right)
                } else {
                    self.builder.ins().ushr(left, right)
                };
                self.canonical(kind, value)
            }
            _ => {
                let condition = match (op, signed) {
                    (Kind::Lt, true) => IntCC::SignedLessThan,
                    (Kind::Le, true) => IntCC::SignedLessThanOrEqual,
                    (Kind::Gt, true) => IntCC::SignedGreaterThan,
                    (Kind::Ge, true) => IntCC::SignedGreaterThanOrEqual,
                    (Kind::Lt, false) => IntCC::UnsignedLessThan,
                    (Kind::Le, false) => IntCC::UnsignedLessThanOrEqual,
                    (Kind::Gt, false) => IntCC::UnsignedGreaterThan,
                    (Kind::Ge, false) => IntCC::UnsignedGreaterThanOrEqual,
                    (Kind::EqEq, _) => IntCC::Equal,
                    (Kind::Ne, _) => IntCC::NotEqual,
                    _ => unreachable!(),
                };
                let value = self.builder.ins().icmp(condition, left, right);
                self.builder.ins().uextend(I64, value)
            }
        }
    }
    /// Explicit conversions and wrapping/saturating/checked arithmetic.
    fn int_builtin(
        &mut self,
        op: crate::int::IntOp,
        source: IntKind,
        target: IntKind,
        values: &[Value],
        ty: Type,
    ) -> Words {
        use crate::int::{ArithOp, IntOp};
        // `in_range(v)` for a 64-bit word that holds an exact mathematical
        // value interpreted in `source`'s signedness.
        let in_target = |g: &mut Self, value: Value, value_signed: bool| -> Value {
            // value fits target  <=>  target.min <= v <= target.max
            let lo = target.min();
            let hi = target.max();
            let (lt_min, gt_max) = if value_signed {
                let lt = if lo <= i128::from(i64::MIN) {
                    g.builder.ins().iconst(ir::types::I8, 0)
                } else {
                    g.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedLessThan, value, lo as i64)
                };
                let gt = if hi >= i128::from(i64::MAX) {
                    g.builder.ins().iconst(ir::types::I8, 0)
                } else {
                    g.builder
                        .ins()
                        .icmp_imm_s(IntCC::SignedGreaterThan, value, hi as i64)
                };
                (lt, gt)
            } else {
                let lt = g.builder.ins().iconst(ir::types::I8, 0);
                let gt = if hi >= i128::from(u64::MAX) {
                    g.builder.ins().iconst(ir::types::I8, 0)
                } else {
                    g.builder
                        .ins()
                        .icmp_imm_u(IntCC::UnsignedGreaterThan, value, hi as u64 as i64)
                };
                (lt, gt)
            };
            let bad = g.builder.ins().bor(lt_min, gt_max);
            g.builder.ins().icmp_imm_s(IntCC::Equal, bad, 0)
        };
        let option =
            |g: &mut Self, present: Value, payload: Value, some: usize, none: usize| -> Words {
                let some_tag = g.constant(some as i64);
                let none_tag = g.constant(none as i64);
                let tag = g.builder.ins().select(present, some_tag, none_tag);
                let zero = g.constant(0);
                let payload = g.builder.ins().select(present, payload, zero);
                let mut words = vec![tag, payload];
                while words.len() < g.program.width(ty) {
                    words.push(g.constant(0));
                }
                words
            };
        let a = values[0];
        match op {
            IntOp::Convert => vec![a],
            IntOp::Truncate => vec![self.canonical(target, a)],
            IntOp::TryConvert { some_tag, none_tag } => {
                // u64 values above i64::MAX are negative words; reject them for
                // any signed target and for any narrower unsigned target.
                let ok = in_target(self, a, source.signed());
                let high_half =
                    (!source.signed() && source == IntKind::U64 && target != IntKind::U64)
                        || (source.signed() && !target.signed());
                let ok = if high_half {
                    let small =
                        self.builder
                            .ins()
                            .icmp_imm_s(IntCC::SignedGreaterThanOrEqual, a, 0);
                    self.builder.ins().band(ok, small)
                } else {
                    ok
                };
                option(self, ok, a, some_tag, none_tag)
            }
            IntOp::CharFromCode { some_tag, none_tag } => {
                let max =
                    self.builder
                        .ins()
                        .icmp_imm_u(IntCC::UnsignedLessThanOrEqual, a, 0x10FFFF);
                let below = self
                    .builder
                    .ins()
                    .icmp_imm_u(IntCC::UnsignedLessThan, a, 0xD800);
                let above = self
                    .builder
                    .ins()
                    .icmp_imm_u(IntCC::UnsignedGreaterThan, a, 0xDFFF);
                let not_surrogate = self.builder.ins().bor(below, above);
                let ok = self.builder.ins().band(max, not_surrogate);
                option(self, ok, a, some_tag, none_tag)
            }
            IntOp::Wrapping(arith) | IntOp::Saturating(arith) | IntOp::Checked(arith, _, _) => {
                let b = values[1];
                let kind = source;
                let signed = kind.signed();
                let wide = kind.bits() == 64;
                let (value, overflow) = match (arith, signed || !wide) {
                    (ArithOp::Add, true) => self.builder.ins().sadd_overflow(a, b),
                    (ArithOp::Sub, true) => self.builder.ins().ssub_overflow(a, b),
                    (ArithOp::Mul, true) => self.builder.ins().smul_overflow(a, b),
                    (ArithOp::Add, false) => self.builder.ins().uadd_overflow(a, b),
                    (ArithOp::Sub, false) => self.builder.ins().usub_overflow(a, b),
                    (ArithOp::Mul, false) => self.builder.ins().umul_overflow(a, b),
                };
                // Exact result fits the kind: no 64-bit overflow and in range.
                let canonical = self.canonical(kind, value);
                let same = self.builder.ins().icmp(IntCC::Equal, canonical, value);
                let no_overflow = self.builder.ins().icmp_imm_s(IntCC::Equal, overflow, 0);
                let fits = self.builder.ins().band(same, no_overflow);
                match op {
                    IntOp::Wrapping(_) => vec![canonical],
                    IntOp::Checked(_, some, none) => option(self, fits, value, some, none),
                    _ => {
                        // Saturate toward the bound in the direction of the
                        // true result: for unsigned, sub underflows to 0 and
                        // add/mul overflow to max; for signed, the sign of
                        // the exact result decides.
                        let max = self.constant(kind.encode(kind.max()).unwrap());
                        let min = self.constant(kind.encode(kind.min()).unwrap());
                        let bound = if !signed {
                            if arith == ArithOp::Sub { min } else { max }
                        } else {
                            let negative = match arith {
                                ArithOp::Add => {
                                    self.builder.ins().icmp_imm_s(IntCC::SignedLessThan, b, 0)
                                }
                                ArithOp::Sub => {
                                    self.builder
                                        .ins()
                                        .icmp_imm_s(IntCC::SignedGreaterThan, b, 0)
                                }
                                ArithOp::Mul => {
                                    let x = self.builder.ins().bxor(a, b);
                                    self.builder.ins().icmp_imm_s(IntCC::SignedLessThan, x, 0)
                                }
                            };
                            self.builder.ins().select(negative, min, max)
                        };
                        vec![self.builder.ins().select(fits, value, bound)]
                    }
                }
            }
        }
    }
    fn short_circuit(&mut self, op: &Kind, left: Value, right: &Expr) -> Option<Words> {
        let rhs = self.builder.create_block();
        let shortcut = self.builder.create_block();
        let join = self.join(Type::Bool).unwrap();
        if *op == Kind::AmpAmp {
            self.builder.ins().brif(left, rhs, &[], shortcut, &[]);
        } else {
            self.builder.ins().brif(left, shortcut, &[], rhs, &[]);
        }
        self.builder.switch_to_block(shortcut);
        let value = self.constant(i64::from(*op == Kind::PipePipe));
        self.jump(join, &[value]);
        self.builder.switch_to_block(rhs);
        if let Some(value) = self.scalar(right) {
            self.jump(join, &[value]);
        }
        self.builder.switch_to_block(join);
        Some(self.builder.block_params(join).to_vec())
    }
    fn pattern(&mut self, pattern: &Pattern, values: &[Value]) -> Value {
        match pattern {
            Pattern::Any | Pattern::Bind(_) => self.builder.ins().iconst(ir::types::I8, 1),
            Pattern::Literal(n) => self.builder.ins().icmp_imm_s(IntCC::Equal, values[0], *n),
            Pattern::Variant { tag, fields } => {
                let mut result =
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, values[0], *tag as i64);
                for (offset, p) in fields {
                    let field = self.pattern(p, &values[*offset..]);
                    result = self.builder.ins().band(result, field);
                }
                result
            }
            Pattern::Type { tag, inner, .. } => {
                let result = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::Equal, values[0], *tag as i64);
                let narrowed = self.pattern(inner, &values[1..]);
                self.builder.ins().band(result, narrowed)
            }
            Pattern::Or(ps) => {
                let mut result = self.builder.ins().iconst(ir::types::I8, 0);
                for p in ps {
                    let p = self.pattern(p, values);
                    result = self.builder.ins().bor(result, p);
                }
                result
            }
        }
    }
    fn dispose_pattern(&mut self, pattern: &Pattern, ty: Type, values: &[Value]) {
        match pattern {
            Pattern::Any => self.drop_value(ty, values),
            Pattern::Bind(slot) => self.activate_local(*slot),
            Pattern::Variant { tag, fields } => {
                let Some(id) = ty.layout() else {
                    unreachable!()
                };
                for ((offset, p), ty) in fields
                    .iter()
                    .zip(self.program.enums[id].variants[*tag].fields.clone())
                    .rev()
                {
                    self.dispose_pattern(p, ty, &values[*offset..]);
                }
            }
            Pattern::Type { member, inner, .. } => {
                self.dispose_pattern(inner, *member, &values[1..]);
            }
            Pattern::Or(ps) => {
                let join = self.builder.create_block();
                for p in ps {
                    let condition = self.pattern(p, values);
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    self.dispose_pattern(p, ty, values);
                    self.jump(join, &[]);
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                self.builder.switch_to_block(join);
            }
            _ => {}
        }
    }
    fn bind_pattern(&mut self, pattern: &Pattern, values: &[Value]) {
        match pattern {
            Pattern::Bind(slot) => {
                let width = self.variables[*slot].len();
                self.assign(*slot, &values[..width]);
            }
            Pattern::Variant { fields, .. } => {
                for (offset, p) in fields {
                    self.bind_pattern(p, &values[*offset..]);
                }
            }
            Pattern::Type { inner, .. } => self.bind_pattern(inner, &values[1..]),
            Pattern::Or(ps) if ps.iter().any(has_bindings) => {
                let join = self.builder.create_block();
                for p in ps {
                    let condition = self.pattern(p, values);
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    self.bind_pattern(p, values);
                    self.jump(join, &[]);
                    self.builder.switch_to_block(next);
                }
                self.builder.ins().trap(TrapCode::unwrap_user(2));
                self.builder.switch_to_block(join);
            }
            _ => {}
        }
    }
}
fn has_bindings(p: &Pattern) -> bool {
    match p {
        Pattern::Bind(_) => true,
        Pattern::Variant { fields, .. } => fields.iter().any(|(_, p)| has_bindings(p)),
        Pattern::Type { inner, .. } => has_bindings(inner),
        Pattern::Or(ps) => ps.iter().any(has_bindings),
        _ => false,
    }
}
