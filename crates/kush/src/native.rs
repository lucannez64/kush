//! Cranelift AOT code generation for the checked scalar IR. The C shim only
//! supplies process entry, standard-stream I/O, allocation, byte operations, and abort;
//! user functions are CLIF.
use crate::float::FloatKind;
use crate::grades::Grade;
use crate::int::IntKind;
use crate::{
    Diagnostic, Span,
    executable::{
        self as ex, AllocVecOp, BytesOp, Coercion, DynArrayOp, Executable, Expr, ExprKind, HostOp,
        IoOp, Pattern, ReceiverMode, SliceOp, StrOp, StringOp, Target, Type, VecOp,
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

mod deferred;
mod llvm;
mod runtime_cache;
/// Every native stack slot is word aligned (`1 << 3` bytes). References to
/// locals point into these slots, so with the runtime's allocation contract
/// (`KUSH_POINTER_ALIGN` in the C runtime) every `Box`, `&T` and `&mut T` is a
/// nonzero multiple of 8. Pointer niches (unboxing-certificates.md section 6)
/// rely on this; change it only together with the certificate value sets.
pub(crate) const STACK_SLOT_ALIGN_SHIFT: u8 = 3;
/// The pointer alignment every native allocation path and stack reference
/// guarantees, in bytes.
pub(crate) const POINTER_ALIGN: u64 = 1 << STACK_SLOT_ALIGN_SHIFT;
/// The Cranelift comparison for a certificate decoder.
fn decoder_test(decoder: crate::layout_cert::Decoder) -> (IntCC, i64) {
    match decoder {
        crate::layout_cert::Decoder::Equal(constant) => (IntCC::Equal, constant),
        crate::layout_cert::Decoder::NotEqual(constant) => (IntCC::NotEqual, constant),
    }
}

type Result<T> = std::result::Result<T, Diagnostic>;
fn error(message: impl std::fmt::Display) -> Diagnostic {
    Diagnostic::new(Span::default(), message.to_string())
}
const RUNTIME: &str = r#"
#define _GNU_SOURCE
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <signal.h>
#include <stdio.h>
#include <math.h>
#include <locale.h>
#include <fcntl.h>
#include <dirent.h>
#include <poll.h>
#include <time.h>
#include <netdb.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
extern char **environ;
extern int64_t kush_entry(void);
/* Diagnostic/error-path writes intentionally do not retry or alter control
   flow on failure. Assign the result so fortified libc headers also accept
   the explicit best-effort policy under -Werror. */
static void kush_best_effort_write(int fd, const void *data, size_t length) {
    ssize_t result = write(fd, data, length);
    (void)result;
}
_Noreturn void kush_panic(void) {
    static const char message[] = "panic: checked arithmetic, memory, or I/O failure\n";
    kush_best_effort_write(2, message, sizeof(message) - 1);
    abort();
}
/* Stack exhaustion is a panic, not a bare SIGSEGV. Every stack (the process
   stack and each task stack) ends in an unmapped guard, and generated code
   probes each page of a large frame, so running out always faults just
   below the stack pointer. The handler runs on its own stack, recognizes
   that fault by its distance from the interrupted stack pointer, and
   reports it. Any other fault is left to the default action. */
#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__))
#include <ucontext.h>
#define KUSH_STACK_GUARD 1
static char kush_signal_stack[1 << 16];
static uintptr_t kush_stack_ceiling = UINTPTR_MAX;
static void kush_fault(int number, siginfo_t *info, void *raw) {
    ucontext_t *context = (ucontext_t *)raw;
#if defined(__x86_64__)
    uintptr_t sp = (uintptr_t)context->uc_mcontext.gregs[REG_RSP];
#else
    uintptr_t sp = (uintptr_t)context->uc_mcontext.sp;
#endif
    uintptr_t address = (uintptr_t)info->si_addr;
    /* Exhaustion faults in the frame being set up: a probe or a push just
       below the stack pointer, or a store into a frame smaller than the
       probe interval just above it. Anything further up is some other
       access, and so is anything above the frame the process started in
       (a write running off the top of the stack). A signal sent by another
       process (si_code <= 0) is never a fault of ours. */
    uintptr_t below = UINT64_C(1) << 16, above = UINT64_C(2) << 12;
    if (info->si_code > 0 && address + below >= sp && address < sp + above
        && address < kush_stack_ceiling) {
        static const char message[] = "panic: stack exhausted\n";
        kush_best_effort_write(2, message, sizeof(message) - 1);
        abort();
    }
    /* Not ours: give the signal its default action. A fault repeats when
       the instruction is retried; a sent signal has to be raised again, and
       is delivered once this handler returns. */
    signal(number, SIG_DFL);
    if (info->si_code <= 0) raise(number);
}
static void kush_stack_guard_init(void) {
    stack_t stack;
    kush_stack_ceiling = (uintptr_t)__builtin_frame_address(0);
    struct sigaction action;
    memset(&stack, 0, sizeof(stack));
    stack.ss_sp = kush_signal_stack;
    stack.ss_size = sizeof(kush_signal_stack);
    if (sigaltstack(&stack, NULL) != 0) kush_panic();
    memset(&action, 0, sizeof(action));
    action.sa_sigaction = kush_fault;
    action.sa_flags = SA_SIGINFO | SA_ONSTACK;
    if (sigemptyset(&action.sa_mask) != 0) kush_panic();
    if (sigaction(SIGSEGV, &action, NULL) != 0) kush_panic();
    if (sigaction(SIGBUS, &action, NULL) != 0) kush_panic();
}
#else
static void kush_stack_guard_init(void) {}
#endif
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
   Every native allocation carries a 16-byte header in front of its payload.
   The header size is a multiple of the 16-byte alignment requested from the
   system allocator, so payloads stay 16-byte aligned. `usable` records the
   payload capacity in bytes. A union stores either the live-block marker
   (including pool eligibility) or the free-list link while retained. The marker
   is not a general detector for invalid pointers or stale handles after block
   reuse. Requests up to
   KUSH_POOL_MAX bytes use 16-byte size classes; a freed block returns to its
   class only while the retained total (header plus padded payload) stays at or
   below KUSH_POOL_RETAIN_CAP, with a per-class block limit. Pooling is a
   physical optimization only: the logical counters still count one kush_alloc/kush_free call, so
   allocation-stats stays byte-identical. Headers also let buffer growth copy
   exactly the live capacity. All retained storage is drained back to the
   system on a normal exit. */
#define KUSH_ALLOC_ALIGN ((uint64_t)16)
/* Pointer contract: every pointer handed to generated code as a Box payload,
   buffer, arena payload, allocator block or reference is nonzero and a
   multiple of KUSH_POINTER_ALIGN. Layout value sets (unboxing-certificates.md
   section 3) may rely on it; the Rust side mirrors it as POINTER_ALIGN. */
#define KUSH_POINTER_ALIGN ((uint64_t)8)
_Static_assert(KUSH_ALLOC_ALIGN % KUSH_POINTER_ALIGN == 0,
               "allocator alignment must be a multiple of the pointer alignment");
#define KUSH_POOL_MAX ((uint64_t)1024)
#define KUSH_POOL_CLASSES ((size_t)(KUSH_POOL_MAX / KUSH_ALLOC_ALIGN))
#define KUSH_POOL_RETAIN_CAP ((uint64_t)1024 * 1024)
#define KUSH_POOL_CLASS_CAP ((size_t)64)
#define KUSH_ALLOC_MAGIC UINT64_C(0x4b555348414c4c4f)
typedef struct KushAllocHeader KushAllocHeader;
/* A live block never needs a next pointer. The alternate live marker keeps
   exact/unpooled blocks distinct without another header word. Free-list links
   only occupy the union after the owner has been released. */
#define KUSH_ALLOC_UNPOOLED (KUSH_ALLOC_MAGIC ^ UINT64_C(1))
struct KushAllocHeader {
    uint64_t usable;
    union {
        uint64_t magic;
        KushAllocHeader *next;
    };
};
_Static_assert(sizeof(KushAllocHeader) == 16,
               "compact header must preserve 16-byte payload alignment");
static int kush_block_live(const KushAllocHeader *header) {
    return header->magic == KUSH_ALLOC_MAGIC || header->magic == KUSH_ALLOC_UNPOOLED;
}
static KushAllocHeader *kush_pool_lists[KUSH_POOL_CLASSES];
/* Headerless ordinary buffers have their own intrusive lists. Both families
   share the existing per-class count and global physical-byte budget. */
static uint64_t *kush_buffer_lists[KUSH_POOL_CLASSES];
static size_t kush_pool_counts[KUSH_POOL_CLASSES];
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
    header->magic = usable <= KUSH_POOL_MAX ? KUSH_ALLOC_MAGIC : KUSH_ALLOC_UNPOOLED;
    header->usable = usable;
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
    --kush_pool_counts[class];
    kush_pool_retained -= kush_block_bytes(header->usable);
    header->magic = KUSH_ALLOC_MAGIC;
    header->usable = class_size;
    ++kush_pool_hits;
    return header;
}
/* Physical release. Small blocks are retained only under the byte cap; every
   other block goes straight back to the system allocator exactly once. */
static void kush_block_release(KushAllocHeader *header) {
    uint64_t usable = header->usable, block = kush_block_bytes(usable);
    int poolable = header->magic == KUSH_ALLOC_MAGIC && usable >= KUSH_ALLOC_ALIGN
        && usable <= KUSH_POOL_MAX && usable % KUSH_ALLOC_ALIGN == 0;
    header->magic = 0;
    size_t class = poolable ? kush_pool_class(usable) : 0;
    if (poolable && kush_pool_counts[class] < KUSH_POOL_CLASS_CAP
        && kush_pool_retained + block <= KUSH_POOL_RETAIN_CAP) {
        header->next = kush_pool_lists[class];
        kush_pool_lists[class] = header;
        ++kush_pool_counts[class];
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
        kush_pool_counts[class] = 0;
        while (header != NULL) {
            KushAllocHeader *next = header->next;
            free(header);
            ++kush_pool_drains;
            header = next;
        }
        uint64_t *buffer = kush_buffer_lists[class];
        kush_buffer_lists[class] = NULL;
        while (buffer != NULL) {
            uint64_t *next = (uint64_t *)(uintptr_t)buffer[0];
            free(buffer);
            ++kush_pool_drains;
            buffer = next;
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
    if (!kush_block_live(header)) kush_panic();
    kush_note_deallocation();
    kush_block_release(header);
}
/* Header-aware grow for owning buffers. This replaces `realloc` exactly as far
   as diagnostics are concerned: the logical allocation counters are untouched
   and the caller keeps its own logical growth counter. The payload contents
   and alignment are preserved, and the old block is released once. */
void *kush_grow(void *payload, uint64_t bytes) {
    KushAllocHeader *header = (KushAllocHeader *)payload - 1;
    if (!kush_block_live(header)) kush_panic();
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
        --kush_pool_counts[class];
        kush_pool_retained -= kush_block_bytes(header->usable);
        header->magic = KUSH_ALLOC_MAGIC;
        header->usable = class_size;
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
    if (!kush_block_live(header)) return NULL;
    uint64_t copy = header->usable;
    if (bytes <= copy) return payload;
    if (kush_try_refuses()) return NULL;
    KushAllocHeader *replacement = kush_try_system_block(bytes);
    if (replacement == NULL) return NULL;
    if (copy != 0) memcpy((void *)(replacement + 1), payload, (size_t)copy);
    kush_block_release(header);
    return (void *)(replacement + 1);
}
/* Small ordinary buffers need no separate KushAllocHeader. The high byte of
   their capacity word stores 0x80 | class (1..64); the low bits store logical
   capacity. Such capacities are bounded by the <=1024-byte allocation itself.
   Large or exact fallible-grown buffers keep the ordinary header and their
   full positive capacity word. Size classes, not libc usable-size guesses,
   preserve deterministic retained-capacity/refusal behavior after map changes. */
#define KUSH_BUFFER_RAW UINT64_C(0x8000000000000000)
#define KUSH_BUFFER_CAP_MASK UINT64_C(0xffff)
static uint64_t kush_buffer_capacity(const void *payload) {
    uint64_t word = ((const uint64_t *)payload)[1];
    return (word & KUSH_BUFFER_RAW) ? word & KUSH_BUFFER_CAP_MASK : word;
}
static void kush_buffer_set_capacity(void *payload, uint64_t capacity) {
    uint64_t *words = (uint64_t *)payload;
    if (words[1] & KUSH_BUFFER_RAW) {
        if (capacity > KUSH_BUFFER_CAP_MASK) kush_panic();
        words[1] = (words[1] & ~KUSH_BUFFER_CAP_MASK) | capacity;
    } else {
        if (capacity > (uint64_t)INT64_MAX) kush_panic();
        words[1] = capacity;
    }
}
static uint64_t kush_buffer_usable(const void *payload) {
    uint64_t word = ((const uint64_t *)payload)[1];
    if (word & KUSH_BUFFER_RAW) {
        uint64_t code = (word >> 56) & 127;
        if (code == 0 || code > KUSH_POOL_CLASSES) kush_panic();
        return code * KUSH_ALLOC_ALIGN;
    }
    const KushAllocHeader *header = (const KushAllocHeader *)payload - 1;
    if (!kush_block_live(header)) kush_panic();
    return header->usable;
}
static void *kush_buffer_claim(uint64_t bytes, uint64_t capacity) {
    if (bytes < 16 || capacity > (uint64_t)INT64_MAX || capacity > bytes - 16) kush_panic();
    if (bytes > KUSH_POOL_MAX) {
        KushAllocHeader *header = kush_try_system_block(bytes);
        if (header == NULL) return NULL;
        uint64_t *payload = (uint64_t *)(header + 1);
        payload[1] = capacity;
        return payload;
    }
    uint64_t usable = (bytes + KUSH_ALLOC_ALIGN - 1) & ~(KUSH_ALLOC_ALIGN - 1);
    size_t class = kush_pool_class(usable);
    uint64_t *payload = kush_buffer_lists[class];
    if (payload != NULL) {
        kush_buffer_lists[class] = (uint64_t *)(uintptr_t)payload[0];
        --kush_pool_counts[class];
        kush_pool_retained -= usable;
        ++kush_pool_hits;
    } else {
        ++kush_pool_misses;
        payload = (uint64_t *)aligned_alloc((size_t)KUSH_ALLOC_ALIGN, (size_t)usable);
        if (payload == NULL) return NULL;
    }
    payload[1] = ((UINT64_C(0x80) | (uint64_t)(class + 1)) << 56) | capacity;
    return payload;
}
static void kush_buffer_release(void *payload) {
    uint64_t *words = (uint64_t *)payload;
    if (!(words[1] & KUSH_BUFFER_RAW)) {
        KushAllocHeader *header = (KushAllocHeader *)payload - 1;
        if (!kush_block_live(header)) kush_panic();
        kush_block_release(header);
        return;
    }
    uint64_t usable = kush_buffer_usable(payload);
    size_t class = kush_pool_class(usable);
    /* Invalid class zero makes a retained double release fail before any
       pointer-prefix access. Reclaim initializes the complete capacity word. */
    words[1] = KUSH_BUFFER_RAW;
    if (kush_pool_counts[class] < KUSH_POOL_CLASS_CAP
        && kush_pool_retained + usable <= KUSH_POOL_RETAIN_CAP) {
        words[0] = (uint64_t)(uintptr_t)kush_buffer_lists[class];
        kush_buffer_lists[class] = words;
        ++kush_pool_counts[class];
        kush_pool_retained += usable;
        if (kush_pool_retained > kush_pool_peak_retained) kush_pool_peak_retained = kush_pool_retained;
        ++kush_pool_retains;
    } else {
        free(payload);
        ++kush_pool_releases;
    }
}
uint64_t kush_buffer_alloc(uint64_t bytes, uint64_t capacity, int fallible) {
    if (fallible && kush_try_refuses()) return 0;
    void *payload = kush_buffer_claim(bytes, capacity);
    if (payload == NULL) {
        if (fallible) return 0;
        kush_panic();
    }
    kush_note_allocation();
    return (uint64_t)(uintptr_t)payload;
}
void kush_buffer_free(uint64_t handle) {
    if (handle == 0 || kush_live_allocations == 0) kush_panic();
    kush_buffer_release((void *)(uintptr_t)handle);
    kush_note_deallocation();
}
static void *kush_buffer_grow(void *payload, uint64_t bytes) {
    uint64_t copy = kush_buffer_usable(payload);
    if (bytes <= copy) return payload;
    void *replacement = kush_buffer_claim(bytes, kush_buffer_capacity(payload));
    if (replacement == NULL) kush_panic();
    uint64_t encoding = ((uint64_t *)replacement)[1];
    memcpy(replacement, payload, (size_t)copy);
    ((uint64_t *)replacement)[1] = encoding;
    kush_buffer_release(payload);
    return replacement;
}
static void *kush_buffer_try_grow(void *payload, uint64_t bytes) {
    uint64_t copy = kush_buffer_usable(payload);
    if (bytes <= copy) return payload;
    if (kush_try_refuses()) return NULL;
    /* Exact fallible growth intentionally keeps a header even for small
       requests. Subsequent no-ops must not silently round its capacity. */
    KushAllocHeader *header = kush_try_system_block(bytes);
    if (header == NULL) return NULL;
    uint64_t *replacement = (uint64_t *)(header + 1);
    uint64_t capacity = kush_buffer_capacity(payload);
    memcpy(replacement, payload, (size_t)copy);
    replacement[1] = capacity;
    kush_buffer_release(payload);
    return replacement;
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
/* Arena payloads follow an 8-byte region pointer inside a 16-aligned slot. */
_Static_assert(8 % KUSH_POINTER_ALIGN == 0, "arena payloads must be pointer aligned");
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
_Static_assert(sizeof(KushBytes) % KUSH_POINTER_ALIGN == 0,
               "allocator blocks expose pointer-aligned data");
#define KUSH_MAX_CAPACITY ((uint64_t)INT64_MAX - (uint64_t)sizeof(KushBytes))
/* Byte buffers never change element width or shrink logical capacity. Their
   physical class is exactly round_up(sizeof(KushBytes)+capacity,16), including
   growth that fits existing class slack. Keep the hot capacity word plain;
   reconstruct the generic pool encoding only at growth/release boundaries.
   Vectors still need their encoded class because maps may change width. */
static void kush_bytes_encode(KushBytes *b) {
    if (b->capacity <= KUSH_POOL_MAX - sizeof(KushBytes)) {
        uint64_t bytes = sizeof(KushBytes) + b->capacity;
        uint64_t code = (bytes + KUSH_ALLOC_ALIGN - 1) / KUSH_ALLOC_ALIGN;
        b->capacity |= (UINT64_C(0x80) | code) << 56;
    }
}
void kush_bytes_free(uint64_t handle) {
    if (handle == 0) kush_panic();
    kush_bytes_encode((KushBytes *)(uintptr_t)handle);
    kush_buffer_free(handle);
}
uint64_t kush_bytes_with_capacity(int64_t capacity) {
    if (capacity < 0 || (uint64_t)capacity > KUSH_MAX_CAPACITY) kush_panic();
    KushBytes *b = (KushBytes *)(uintptr_t)kush_buffer_alloc(sizeof(KushBytes) + (uint64_t)capacity, (uint64_t)capacity, 0);
    b->length = 0; b->capacity = (uint64_t)capacity; return (uint64_t)(uintptr_t)b;
}
uint64_t kush_try_bytes_with_capacity(int64_t capacity) {
    if (capacity < 0 || (uint64_t)capacity > KUSH_MAX_CAPACITY) return 0;
    uint64_t handle = kush_buffer_alloc(sizeof(KushBytes) + (uint64_t)capacity, (uint64_t)capacity, 1);
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
   A checked allocator value is a group of noncapturing code pointers:
   `alloc(bytes) -> Bytes` supplies a block with at least `bytes` capacity, and
   `free(block) -> Unit` releases it. A smaller returned block is a refusal and
   is released through the same pair. Containers store the pair themselves, so
   dropping or moving the allocator binding cannot strand an allocation, and
   release always uses the allocator that supplied the block. */
typedef uint64_t (*KushAllocBlockFn)(uint64_t bytes);
typedef void (*KushFreeBlockFn)(uint64_t block);
typedef uint64_t (*KushReallocBlockFn)(uint64_t block, uint64_t old_bytes, uint64_t bytes);
/* One checked, reference-counted allocator instance. `state` points at a
   compiler-allocated block holding the concrete instance words; the drop thunk
   loads those words, runs the instance's drop glue, and frees the block. The
   allocate/release/grow thunks are ordinary generated `&mut Self` methods with
   the state address as their receiver. */
typedef struct {
    uint64_t references;
    uint64_t state;
    uint64_t drop;
    uint64_t alloc;
    uint64_t release;
    uint64_t grow;
} KushAllocContext;
typedef uint64_t (*KushContextAllocFn)(uint64_t state, uint64_t bytes);
typedef void (*KushContextFreeFn)(uint64_t state, uint64_t block);
typedef uint64_t (*KushContextGrowFn)(uint64_t state, uint64_t block,
                                      uint64_t old_bytes, uint64_t bytes);
typedef void (*KushContextDropFn)(uint64_t state);
uint64_t kush_alloc_context_new(uint64_t state, uint64_t drop, uint64_t alloc,
                                uint64_t release, uint64_t grow) {
    if (state == 0 || drop == 0 || alloc == 0 || release == 0 || grow == 0) kush_panic();
    KushAllocContext *context = (KushAllocContext *)(uintptr_t)kush_alloc(sizeof(KushAllocContext));
    context->references = 1;
    context->state = state;
    context->drop = drop;
    context->alloc = alloc;
    context->release = release;
    context->grow = grow;
    return (uint64_t)(uintptr_t)context;
}
uint64_t kush_alloc_context_share(uint64_t handle) {
    KushAllocContext *context = (KushAllocContext *)(uintptr_t)handle;
    ++context->references;
    return handle;
}
void kush_alloc_context_release(uint64_t handle) {
    if (handle == 0) return;
    KushAllocContext *context = (KushAllocContext *)(uintptr_t)handle;
    if (context->references == 0) kush_panic();
    if (--context->references != 0) return;
    ((KushContextDropFn)(uintptr_t)context->drop)(context->state);
    kush_free(handle);
}
static uint64_t kush_allocator_context_alloc(uint64_t context, uint64_t bytes) {
    KushAllocContext *state = (KushAllocContext *)(uintptr_t)context;
    uint64_t out = ((KushContextAllocFn)(uintptr_t)state->alloc)(state->state, bytes);
    return out;
}
static void kush_allocator_context_free(uint64_t context, uint64_t block) {
    if (block == 0) return;
    KushAllocContext *state = (KushAllocContext *)(uintptr_t)context;
    ((KushContextFreeFn)(uintptr_t)state->release)(state->state, block);
}
static uint64_t kush_allocator_context_grow(uint64_t context, uint64_t block,
                                            uint64_t old_bytes, uint64_t bytes) {
    KushAllocContext *state = (KushAllocContext *)(uintptr_t)context;
    uint64_t out = ((KushContextGrowFn)(uintptr_t)state->grow)(state->state, block, old_bytes, bytes);
    return out;
}
unsigned char *kush_alloc_block_data(uint64_t block) {
    return ((KushBytes *)(uintptr_t)block)->data;
}
static void kush_alloc_block_release(uint64_t release, uint64_t context, uint64_t block) {
    if (block == 0) return;
    if (context != 0) {
        kush_allocator_context_free(context, block);
        return;
    }
    if (release == 0) kush_panic();
    ((KushFreeBlockFn)(uintptr_t)release)(block);
}
uint64_t kush_alloc_block_try(uint64_t allocator, uint64_t release, uint64_t context,
                              uint64_t bytes) {
    uint64_t block;
    if (context != 0) {
        block = kush_allocator_context_alloc(context, bytes);
    } else {
        if (allocator == 0) kush_panic();
        block = ((KushAllocBlockFn)(uintptr_t)allocator)(bytes);
    }
    if (block == 0) return 0;
    if (((const KushBytes *)(uintptr_t)block)->capacity < bytes) {
        kush_alloc_block_release(release, context, block);
        return 0;
    }
    return block;
}
uint64_t kush_alloc_block(uint64_t allocator, uint64_t release, uint64_t context,
                          uint64_t bytes) {
    uint64_t block = kush_alloc_block_try(allocator, release, context, bytes);
    if (block == 0) kush_panic();
    return block;
}
typedef struct {
    uint64_t allocator; uint64_t release; uint64_t context; uint64_t block;
} KushAllocBox;
uint64_t kush_alloc_box_create(uint64_t allocator, uint64_t release, uint64_t block,
                               uint64_t context) {
    KushAllocBox *box = (KushAllocBox *)(uintptr_t)kush_alloc(sizeof(KushAllocBox));
    box->allocator = allocator; box->release = release; box->context = context;
    box->block = block;
    return (uint64_t)(uintptr_t)box;
}
unsigned char *kush_alloc_box_payload(uint64_t handle) {
    return kush_alloc_block_data(((KushAllocBox *)(uintptr_t)handle)->block);
}
void kush_alloc_box_release(uint64_t handle) {
    KushAllocBox *box = (KushAllocBox *)(uintptr_t)handle;
    kush_alloc_block_release(box->release, box->context, box->block);
    kush_alloc_context_release(box->context);
    kush_free(handle);
}
typedef struct {
    uint64_t length; uint64_t capacity; uint64_t width;
    uint64_t allocator; uint64_t release; uint64_t realloc; uint64_t context;
    uint64_t block;
} KushAllocVec;
static uint64_t kush_alloc_vec_block_bytes(uint64_t capacity, uint64_t width) {
    if (width == 0 || capacity > ((uint64_t)INT64_MAX) / 8 / width) kush_panic();
    return capacity * width * 8;
}
/* The callback manages storage, never the representation of live typed
   elements. Preserve the payload privately and expose only zeroed readable
   bytes to the hook, then restore the typed prefix into the returned block. */
static uint64_t kush_alloc_block_grow(uint64_t grow, uint64_t context, uint64_t block,
                                      uint64_t old_bytes, uint64_t bytes) {
    if ((grow == 0 && context == 0) || block == 0) kush_panic();
    unsigned char *saved = NULL;
    if (old_bytes != 0) {
        saved = (unsigned char *)malloc((size_t)old_bytes);
        if (saved == NULL) kush_panic();
        memcpy(saved, kush_alloc_block_data(block), (size_t)old_bytes);
        memset(kush_alloc_block_data(block), 0, (size_t)old_bytes);
    }
    ((KushBytes *)(uintptr_t)block)->length = old_bytes;
    uint64_t grown;
    if (context != 0) {
        grown = kush_allocator_context_grow(context, block, old_bytes, bytes);
    } else {
        grown = ((KushReallocBlockFn)(uintptr_t)grow)(block, old_bytes, bytes);
    }
    if (grown == 0 || ((const KushBytes *)(uintptr_t)grown)->capacity < bytes) {
        free(saved);
        kush_panic();
    }
    if (old_bytes != 0) memcpy(kush_alloc_block_data(grown), saved, (size_t)old_bytes);
    free(saved);
    return grown;
}
uint64_t kush_alloc_vec_create(uint64_t allocator, uint64_t release, uint64_t realloc,
                               uint64_t context, int64_t capacity, int64_t width) {
    if (capacity < 0 || width <= 0) kush_panic();
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)kush_alloc(sizeof(KushAllocVec));
    v->length = 0; v->capacity = (uint64_t)capacity; v->width = (uint64_t)width;
    v->allocator = allocator; v->release = release; v->realloc = realloc;
    v->context = context; v->block = 0;
    if (capacity > 0) {
        v->block = kush_alloc_block(allocator, release, context,
                                    kush_alloc_vec_block_bytes(v->capacity, v->width));
    }
    return (uint64_t)(uintptr_t)v;
}
static void kush_alloc_vec_grow(KushAllocVec *v, uint64_t next) {
    uint64_t bytes = kush_alloc_vec_block_bytes(next, v->width);
    uint64_t block;
    uint64_t can_grow = v->context != 0 ? v->block != 0
                                        : v->realloc != 0 && v->block != 0;
    if (can_grow) {
        block = kush_alloc_block_grow(v->realloc, v->context, v->block,
                                      v->length * v->width * 8, bytes);
    } else {
        block = kush_alloc_block(v->allocator, v->release, v->context, bytes);
        if (v->length != 0) {
            memcpy(kush_alloc_block_data(block), kush_alloc_block_data(v->block),
                   (size_t)(v->length * v->width * 8));
        }
        kush_alloc_block_release(v->release, v->context, v->block);
    }
    v->block = block; v->capacity = next; ++kush_buffer_growths;
}
static int kush_alloc_vec_try_grow(KushAllocVec *v, uint64_t next) {
    uint64_t bytes = kush_alloc_vec_block_bytes(next, v->width);
    /* A fallible append never uses the growth hook: a hook that cannot honor
       the request has already consumed the old block, so refusal could not
       preserve the vector. The fresh-block path keeps every element. */
    uint64_t block = kush_alloc_block_try(v->allocator, v->release, v->context, bytes);
    if (block == 0) return 0;
    if (v->length != 0) {
        memcpy(kush_alloc_block_data(block), kush_alloc_block_data(v->block),
               (size_t)(v->length * v->width * 8));
    }
    kush_alloc_block_release(v->release, v->context, v->block);
    v->block = block; v->capacity = next; ++kush_buffer_growths;
    return 1;
}
uint64_t kush_alloc_vec_try_push(uint64_t handle, const uint64_t *item) {
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)handle;
    if (v->length == v->capacity) {
        uint64_t next = v->capacity == 0 ? 4 : v->capacity * 2;
        if (next <= v->capacity) return 0;
        if (!kush_alloc_vec_try_grow(v, next)) return 0;
    }
    memcpy(kush_alloc_block_data(v->block) + v->length * v->width * 8, item,
           (size_t)(v->width * 8));
    v->length++;
    return 1;
}
void kush_alloc_vec_pop(uint64_t handle, uint64_t *out) {
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)handle;
    if (v->length == 0) kush_panic();
    uint64_t index = --v->length;
    memcpy(out, kush_alloc_block_data(v->block) + index * v->width * 8,
           (size_t)(v->width * 8));
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
    kush_alloc_block_release(v->release, v->context, v->block);
    kush_alloc_context_release(v->context);
    kush_free(handle);
}
int64_t kush_bytes_len(uint64_t handle) { return (int64_t)((KushBytes *)(uintptr_t)handle)->length; }
int64_t kush_bytes_capacity(uint64_t handle) { return (int64_t)((const KushBytes *)(uintptr_t)handle)->capacity; }
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
        kush_bytes_encode(b);
        b = (KushBytes *)kush_buffer_grow(b, sizeof(KushBytes) + next);
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
/* Writes through an exclusive &mut str view. ASCII case changes touch only
   bytes below 0x80, and set_scalar replaces one scalar by another of the same
   UTF-8 width at a checked boundary, so the owner stays valid UTF-8 and keeps
   its length. */
int64_t kush_str_ascii_upper(unsigned char *data, int64_t length) {
    for (int64_t i = 0; i < length; ++i) {
        if (data[i] >= 'a' && data[i] <= 'z') data[i] = (unsigned char)(data[i] - 32);
    }
    return 0;
}
int64_t kush_str_ascii_lower(unsigned char *data, int64_t length) {
    for (int64_t i = 0; i < length; ++i) {
        if (data[i] >= 'A' && data[i] <= 'Z') data[i] = (unsigned char)(data[i] + 32);
    }
    return 0;
}
int64_t kush_str_set_scalar(unsigned char *data, int64_t length, int64_t index, int64_t code) {
    if (index < 0 || index >= length || (data[index] & 0xC0) == 0x80) kush_panic();
    unsigned char lead = data[index];
    int64_t width = lead < 0x80 ? 1 : (lead & 0xE0) == 0xC0 ? 2 : (lead & 0xF0) == 0xE0 ? 3 : 4;
    int64_t wanted = code < 0x80 ? 1 : code < 0x800 ? 2 : code < 0x10000 ? 3 : 4;
    if (width != wanted || index + width > length) kush_panic();
    uint32_t c = (uint32_t)code;
    if (width == 1) {
        data[index] = (unsigned char)c;
    } else if (width == 2) {
        data[index] = (unsigned char)(0xC0 | (c >> 6));
        data[index + 1] = (unsigned char)(0x80 | (c & 0x3F));
    } else if (width == 3) {
        data[index] = (unsigned char)(0xE0 | (c >> 12));
        data[index + 1] = (unsigned char)(0x80 | ((c >> 6) & 0x3F));
        data[index + 2] = (unsigned char)(0x80 | (c & 0x3F));
    } else {
        data[index] = (unsigned char)(0xF0 | (c >> 18));
        data[index + 1] = (unsigned char)(0x80 | ((c >> 12) & 0x3F));
        data[index + 2] = (unsigned char)(0x80 | ((c >> 6) & 0x3F));
        data[index + 3] = (unsigned char)(0x80 | (c & 0x3F));
    }
    return 0;
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
        if (received < 0) { int code = errno; kush_bytes_free(handle); return code; }
        if (received == 0) return 0;
        if (full) { kush_bytes_free(handle); return EFBIG; }
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
        if (received < 0) { int code = errno; kush_bytes_free(handle); return code; }
        if (received == 0) return 0;
        if (b->length == b->capacity) { kush_bytes_free(handle); return EFBIG; }
        b->data[b->length++] = byte;
        if (byte == '\n') return 0;
    }
}
/* One successful read, never an excess-byte probe. Full input is EFBIG. */
int64_t kush_io_read_chunk(int64_t stream, uint64_t handle) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (b->length == b->capacity) { kush_bytes_free(handle); return EFBIG; }
    for (;;) {
        ssize_t n = read((int)stream, b->data + b->length, (size_t)(b->capacity - b->length));
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { int code = errno; kush_bytes_free(handle); return code; }
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
/* ---- Checked host operations ---------------------------------------------
   Filesystem, environment, clock, subprocess, and TCP operations are
   synchronous. Each entry point returns zero on success or a positive Linux
   errno and writes its success payload through `out`. Owned buffers are
   released on failure; borrowed buffers are never modified or freed. */
static int kush_host_argc = 0;
static char **kush_host_argv = NULL;
static void kush_host_init(int argc, char **argv) {
    kush_host_argc = argc;
    kush_host_argv = argv;
}
/* Copy a non-NUL-terminated checked path/value into a temporary C string.
   Embedded NUL bytes are rejected because the OS interface is C-string based. */
static char *kush_host_c_path(const KushBytes *b, int *code) {
    if (memchr(b->data, 0, (size_t)b->length) != NULL) { *code = EINVAL; return NULL; }
    char *text = (char *)malloc((size_t)b->length + 1);
    if (text == NULL) { *code = ENOMEM; return NULL; }
    memcpy(text, b->data, (size_t)b->length);
    text[b->length] = 0;
    return text;
}
static int kush_host_open(const char *path, int flags, int with_mode, mode_t mode) {
    for (;;) {
        int fd = with_mode ? open(path, flags, mode) : open(path, flags);
        if (fd >= 0 || errno != EINTR) return fd;
    }
}
static int64_t kush_host_append(KushBytes *b, const unsigned char *data, uint64_t length) {
    if (b->length > b->capacity || length > b->capacity - b->length) return EFBIG;
    if (length != 0) memcpy(b->data + b->length, data, (size_t)length);
    b->length += length;
    return 0;
}
int64_t kush_fs_read(uint64_t path_handle, uint64_t buffer_handle, uint64_t *out) {
    int code = 0;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) { kush_bytes_free(buffer_handle); return code; }
    int fd = kush_host_open(path, O_RDONLY | O_CLOEXEC, 0, 0);
    free(path);
    if (fd < 0) { code = errno; kush_bytes_free(buffer_handle); return code; }
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    unsigned char probe;
    for (;;) {
        int full = b->length == b->capacity;
        void *destination = full ? (void *)&probe : (void *)(b->data + b->length);
        size_t count = full ? 1 : (size_t)(b->capacity - b->length);
        ssize_t received = read(fd, destination, count);
        if (received < 0 && errno == EINTR) continue;
        if (received < 0) { code = errno; break; }
        if (received == 0) { code = 0; break; }
        if (full) { code = EFBIG; break; }
        b->length += (uint64_t)received;
    }
    (void)close(fd);
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    *out = buffer_handle;
    return 0;
}
static int64_t kush_host_write_file(uint64_t path_handle, uint64_t data_handle, int append, uint64_t *out) {
    int code = 0;
    const KushBytes *data = (const KushBytes *)(uintptr_t)data_handle;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) return code;
    int flags = O_WRONLY | O_CREAT | O_CLOEXEC | (append ? O_APPEND : O_TRUNC);
    int fd = kush_host_open(path, flags, 1, 0666);
    free(path);
    if (fd < 0) return errno;
    uint64_t offset = 0;
    while (offset < data->length) {
        ssize_t written = write(fd, data->data + offset, (size_t)(data->length - offset));
        if (written < 0 && errno == EINTR) continue;
        if (written < 0) { code = errno; break; }
        if (written == 0) { code = EIO; break; }
        offset += (uint64_t)written;
    }
    if (code != 0) {
        (void)close(fd);
        return code;
    }
    if (close(fd) != 0) {
        int failure = errno;
        if (failure != EINTR) return failure;
    }
    *out = (uint64_t)data->length;
    return 0;
}
int64_t kush_fs_write(uint64_t path_handle, uint64_t data_handle, uint64_t *out) {
    return kush_host_write_file(path_handle, data_handle, 0, out);
}
static int64_t kush_host_write_file_exclusive(uint64_t path_handle, uint64_t data_handle, uint64_t *out) {
    int code = 0;
    const KushBytes *data = (const KushBytes *)(uintptr_t)data_handle;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) return code;
    int fd = kush_host_open(path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 1, 0600);
    free(path);
    if (fd < 0) return errno;
    uint64_t offset = 0;
    while (offset < data->length) {
        ssize_t written = write(fd, data->data + offset, (size_t)(data->length - offset));
        if (written < 0 && errno == EINTR) continue;
        if (written < 0) { code = errno; break; }
        if (written == 0) { code = EIO; break; }
        offset += (uint64_t)written;
    }
    if (code != 0) {
        (void)close(fd);
        return code;
    }
    if (close(fd) != 0) {
        int failure = errno;
        if (failure != EINTR) return failure;
    }
    *out = (uint64_t)data->length;
    return 0;
}
int64_t kush_fs_write_exclusive(uint64_t path_handle, uint64_t data_handle, uint64_t *out) {
    return kush_host_write_file_exclusive(path_handle, data_handle, out);
}
int64_t kush_fs_append(uint64_t path_handle, uint64_t data_handle, uint64_t *out) {
    return kush_host_write_file(path_handle, data_handle, 1, out);
}
static int64_t kush_host_unary_path(uint64_t path_handle, int operation, uint64_t *out) {
    int code = 0;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) return code;
    int result;
    for (;;) {
        result = operation == 0 ? unlink(path) : operation == 1 ? mkdir(path, 0777) : rmdir(path);
        if (result == 0 || errno != EINTR) break;
    }
    code = result == 0 ? 0 : errno;
    free(path);
    if (code == 0) *out = 0;
    return code;
}
/* File handles (STD-FILE). Only descriptors returned by kush_fs_open are
 * accepted by the handle operations, so a program cannot reach stdin, stdout
 * or a runtime descriptor by passing a number. */
#define KUSH_MAX_FILES 65536
static unsigned char kush_open_files[KUSH_MAX_FILES / 8];
static int kush_file_known(int64_t fd) {
    return fd >= 0 && fd < KUSH_MAX_FILES && (kush_open_files[fd / 8] >> (fd % 8)) & 1;
}
int64_t kush_fs_open(uint64_t path_handle, uint64_t mode, uint64_t *out) {
    int flags;
    mode_t permissions = 0666;
    switch ((int64_t)mode) {
        case 0: flags = O_RDONLY; break;
        case 1: flags = O_RDWR | O_CREAT; break;
        case 2: flags = O_RDWR; break;
        case 3: flags = O_RDWR | O_CREAT | O_EXCL; permissions = 0600; break;
        default: return EINVAL;
    }
    int code = 0;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) return code;
    int fd = kush_host_open(path, flags | O_CLOEXEC, 1, permissions);
    free(path);
    if (fd < 0) return errno;
    if (fd >= KUSH_MAX_FILES) { (void)close(fd); return EMFILE; }
    kush_open_files[fd / 8] |= (unsigned char)(1u << (fd % 8));
    *out = (uint64_t)fd;
    return 0;
}
int64_t kush_fs_read_at(uint64_t fd, uint64_t offset, uint64_t length, uint64_t buffer_handle, uint64_t *out) {
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    int code = 0;
    if (!kush_file_known((int64_t)fd)) code = EBADF;
    else if ((int64_t)offset < 0 || (int64_t)length < 0) code = EINVAL;
    else if (length > b->capacity - b->length) code = EFBIG;
    uint64_t done = 0;
    while (code == 0 && done < length) {
        ssize_t received = pread((int)fd, b->data + b->length, (size_t)(length - done), (off_t)(offset + done));
        if (received < 0 && errno == EINTR) continue;
        if (received < 0) { code = errno; break; }
        if (received == 0) break;
        b->length += (uint64_t)received;
        done += (uint64_t)received;
    }
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    *out = buffer_handle;
    return 0;
}
int64_t kush_fs_write_at(uint64_t fd, uint64_t offset, uint64_t data_handle, uint64_t *out) {
    const KushBytes *data = (const KushBytes *)(uintptr_t)data_handle;
    if (!kush_file_known((int64_t)fd)) return EBADF;
    if ((int64_t)offset < 0 || data->length > (uint64_t)INT64_MAX - offset) return EINVAL;
    uint64_t done = 0;
    while (done < data->length) {
        ssize_t written = pwrite((int)fd, data->data + done, (size_t)(data->length - done), (off_t)(offset + done));
        if (written < 0 && errno == EINTR) continue;
        if (written < 0) return errno;
        if (written == 0) return EIO;
        done += (uint64_t)written;
    }
    *out = data->length;
    return 0;
}
int64_t kush_fs_sync(uint64_t fd, uint64_t *out) {
    if (!kush_file_known((int64_t)fd)) return EBADF;
    for (;;) {
        if (fsync((int)fd) == 0) break;
        if (errno != EINTR) return errno;
    }
    *out = 0;
    return 0;
}
int64_t kush_fs_truncate(uint64_t fd, uint64_t length, uint64_t *out) {
    if (!kush_file_known((int64_t)fd)) return EBADF;
    if ((int64_t)length < 0) return EINVAL;
    for (;;) {
        if (ftruncate((int)fd, (off_t)length) == 0) break;
        if (errno != EINTR) return errno;
    }
    *out = 0;
    return 0;
}
int64_t kush_fs_file_size(uint64_t fd, uint64_t *out) {
    if (!kush_file_known((int64_t)fd)) return EBADF;
    struct stat info;
    if (fstat((int)fd, &info) != 0) return errno;
    *out = (uint64_t)info.st_size;
    return 0;
}
int64_t kush_fs_close(uint64_t fd, uint64_t *out) {
    if (!kush_file_known((int64_t)fd)) return EBADF;
    kush_open_files[fd / 8] &= (unsigned char)~(1u << (fd % 8));
    /* Linux releases the descriptor even when close reports EINTR. */
    if (close((int)fd) != 0 && errno != EINTR) return errno;
    *out = 0;
    return 0;
}
int64_t kush_fs_sync_dir(uint64_t path_handle, uint64_t *out) {
    int code = 0;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) return code;
    int fd = kush_host_open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC, 0, 0);
    free(path);
    if (fd < 0) return errno;
    for (;;) {
        if (fsync(fd) == 0) break;
        if (errno != EINTR) { code = errno; break; }
    }
    (void)close(fd);
    if (code != 0) return code;
    *out = 0;
    return 0;
}
int64_t kush_fs_remove(uint64_t path_handle, uint64_t *out) {
    return kush_host_unary_path(path_handle, 0, out);
}
int64_t kush_fs_mkdir(uint64_t path_handle, uint64_t *out) {
    return kush_host_unary_path(path_handle, 1, out);
}
int64_t kush_fs_remove_dir(uint64_t path_handle, uint64_t *out) {
    return kush_host_unary_path(path_handle, 2, out);
}
int64_t kush_fs_rename(uint64_t from_handle, uint64_t to_handle, uint64_t *out) {
    int code = 0;
    char *from = kush_host_c_path((const KushBytes *)(uintptr_t)from_handle, &code);
    if (from == NULL) return code;
    char *to = kush_host_c_path((const KushBytes *)(uintptr_t)to_handle, &code);
    if (to == NULL) { free(from); return code; }
    int result;
    for (;;) {
        result = rename(from, to);
        if (result == 0 || errno != EINTR) break;
    }
    code = result == 0 ? 0 : errno;
    free(from); free(to);
    if (code == 0) *out = 0;
    return code;
}
int64_t kush_fs_list(uint64_t path_handle, uint64_t buffer_handle, uint64_t *out) {
    int code = 0;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) { kush_bytes_free(buffer_handle); return code; }
    DIR *directory = opendir(path);
    free(path);
    if (directory == NULL) { code = errno; kush_bytes_free(buffer_handle); return code; }
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    for (;;) {
        errno = 0;
        struct dirent *entry = readdir(directory);
        if (entry == NULL) { if (errno != 0) code = errno; break; }
        const char *name = entry->d_name;
        if (strcmp(name, ".") == 0 || strcmp(name, "..") == 0) continue;
        uint64_t length = (uint64_t)strlen(name);
        int status = (int)kush_host_append(b, (const unsigned char *)name, length);
        if (status != 0) { code = status; break; }
        status = (int)kush_host_append(b, (const unsigned char *)"\n", 1);
        if (status != 0) { code = status; break; }
    }
    (void)closedir(directory);
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    *out = buffer_handle;
    return 0;
}
static int64_t kush_host_stat_flags(uint64_t path_handle, int kind, uint64_t *out) {
    int code = 0;
    char *path = kush_host_c_path((const KushBytes *)(uintptr_t)path_handle, &code);
    if (path == NULL) return code;
    struct stat info;
    int result;
    for (;;) {
        result = stat(path, &info);
        if (result == 0 || errno != EINTR) break;
    }
    code = result == 0 ? 0 : errno;
    free(path);
    if (code != 0) {
        if (kind != 2 && (code == ENOENT || code == ENOTDIR)) { *out = 0; return 0; }
        return code;
    }
    if (kind == 0) *out = S_ISREG(info.st_mode) ? 1 : 0;
    else if (kind == 1) *out = S_ISDIR(info.st_mode) ? 1 : 0;
    else if (kind == 2) *out = (uint64_t)info.st_size;
    else *out = 1;
    return 0;
}
int64_t kush_fs_is_file(uint64_t path_handle, uint64_t *out) {
    return kush_host_stat_flags(path_handle, 0, out);
}
int64_t kush_fs_is_dir(uint64_t path_handle, uint64_t *out) {
    return kush_host_stat_flags(path_handle, 1, out);
}
int64_t kush_fs_size(uint64_t path_handle, uint64_t *out) {
    return kush_host_stat_flags(path_handle, 2, out);
}
int64_t kush_fs_exists(uint64_t path_handle, uint64_t *out) {
    return kush_host_stat_flags(path_handle, 3, out);
}
int64_t kush_env_arg_count(uint64_t *out) {
    *out = (uint64_t)(kush_host_argc < 0 ? 0 : kush_host_argc);
    return 0;
}
int64_t kush_env_arg(int64_t index, uint64_t buffer_handle, uint64_t *out) {
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    if (index < 0 || index >= (int64_t)kush_host_argc || kush_host_argv == NULL) {
        kush_bytes_free(buffer_handle); return ENOENT;
    }
    const char *value = kush_host_argv[index];
    int64_t code = kush_host_append(b, (const unsigned char *)value, (uint64_t)strlen(value));
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    *out = buffer_handle;
    return 0;
}
int64_t kush_env_var_count(uint64_t *out) {
    uint64_t count = 0;
    if (environ != NULL) {
        for (char **entry = environ; *entry != NULL; ++entry) {
            if (strchr(*entry, '=') != NULL) ++count;
        }
    }
    *out = count;
    return 0;
}
int64_t kush_env_var(const KushBytes *name, uint64_t buffer_handle, uint64_t *out) {
    int code = 0;
    char *text = kush_host_c_path(name, &code);
    if (text == NULL) { kush_bytes_free(buffer_handle); return code; }
    const char *value = getenv(text);
    free(text);
    if (value == NULL) { kush_bytes_free(buffer_handle); return ENOENT; }
    code = (int)kush_host_append((KushBytes *)(uintptr_t)buffer_handle,
        (const unsigned char *)value, (uint64_t)strlen(value));
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    *out = buffer_handle;
    return 0;
}
static int64_t kush_host_now_ns(clockid_t clock, uint64_t *out) {
    struct timespec now;
    if (clock_gettime(clock, &now) != 0) return errno;
    if (now.tv_sec < 0 || (uint64_t)now.tv_sec > (uint64_t)INT64_MAX / UINT64_C(1000000000)) {
        return EOVERFLOW;
    }
    uint64_t seconds = (uint64_t)now.tv_sec * UINT64_C(1000000000);
    if (seconds > (uint64_t)INT64_MAX - (uint64_t)now.tv_nsec) return EOVERFLOW;
    *out = seconds + (uint64_t)now.tv_nsec;
    return 0;
}
int64_t kush_time_unix_seconds(uint64_t *out) {
    struct timespec now;
    if (clock_gettime(CLOCK_REALTIME, &now) != 0) return errno;
    *out = (uint64_t)now.tv_sec;
    return 0;
}
int64_t kush_time_monotonic_ns(uint64_t *out) {
    return kush_host_now_ns(CLOCK_MONOTONIC, out);
}
int64_t kush_time_sleep_ms(int64_t milliseconds, uint64_t *out) {
    if (milliseconds < 0) return EINVAL;
    struct timespec request;
    request.tv_sec = (time_t)(milliseconds / 1000);
    request.tv_nsec = (long)((milliseconds % 1000) * 1000000);
    while (nanosleep(&request, &request) != 0) {
        if (errno != EINTR) return errno;
    }
    *out = 0;
    return 0;
}
int64_t kush_os_strerror(int64_t code, uint64_t buffer_handle, uint64_t *out) {
    if (code < 0 || code > 4095) { kush_bytes_free(buffer_handle); return EINVAL; }
    const char *text = strerror((int)code);
    if (text == NULL) text = "Unknown error";
    int64_t status = kush_host_append((KushBytes *)(uintptr_t)buffer_handle,
        (const unsigned char *)text, (uint64_t)strlen(text));
    if (status != 0) { kush_bytes_free(buffer_handle); return status; }
    *out = buffer_handle;
    return 0;
}
static int64_t kush_host_now_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}
/* -1 means no deadline; zero means the budget is exhausted. */
static int kush_host_remaining(int64_t deadline) {
    if (deadline < 0) return -1;
    int64_t now = kush_host_now_ms();
    if (now < 0) return 0;
    if (now >= deadline) return 0;
    int64_t left = deadline - now;
    return left > 60000 ? 60000 : (int)left;
}
/* Saturates instead of wrapping: an enormous timeout is effectively unbounded,
 * and wrapped C arithmetic would turn it into "no deadline" by accident. */
static int64_t kush_host_deadline(int64_t timeout_ms) {
    if (timeout_ms == 0) return -1;
    int64_t now = kush_host_now_ms();
    if (now < 0) return 0;
    if (timeout_ms > INT64_MAX - now) return INT64_MAX;
    return now + timeout_ms;
}
static void kush_host_reap(pid_t child, int *status) {
    for (;;) {
        pid_t result = waitpid(child, status, 0);
        if (result == child || (result < 0 && errno != EINTR)) return;
    }
}
/* Split NUL-separated arguments. Empty segments and a trailing NUL are
   ignored. The program text itself must be one nonempty C-compatible path. */
static char **kush_host_proc_argv(const KushBytes *program, const KushBytes *arguments,
                                  int *count, int *code) {
    char *path = kush_host_c_path(program, code);
    if (path == NULL) return NULL;
    if (program->length == 0 || memchr(program->data, 0, (size_t)program->length) != NULL) {
        free(path); *code = EINVAL; return NULL;
    }
    uint64_t total = 1;
    uint64_t start = 0;
    for (uint64_t i = 0; i < arguments->length; ++i) {
        if (arguments->data[i] == 0) {
            if (i > start) ++total;
            start = i + 1;
        }
    }
    if (start < arguments->length) ++total;
    char **argv = (char **)calloc((size_t)total + 1, sizeof(char *));
    if (argv == NULL) { free(path); *code = ENOMEM; return NULL; }
    argv[0] = path;
    uint64_t at = 1;
    start = 0;
    for (uint64_t i = 0; i <= arguments->length; ++i) {
        int boundary = i == arguments->length || arguments->data[i] == 0;
        if (!boundary) continue;
        if (i > start) {
            uint64_t length = i - start;
            char *text = (char *)malloc((size_t)length + 1);
            if (text == NULL) {
                for (uint64_t j = 0; j < at; ++j) free(argv[j]);
                free(argv); *code = ENOMEM; return NULL;
            }
            memcpy(text, arguments->data + start, (size_t)length);
            text[length] = 0;
            argv[at++] = text;
        }
        start = i + 1;
    }
    *count = (int)at;
    return argv;
}
static void kush_host_proc_free(char **argv, int count) {
    if (argv == NULL) return;
    for (int i = 0; i < count; ++i) free(argv[i]);
    free(argv);
}
int64_t kush_proc_run(uint64_t program_handle, uint64_t args_handle,
                      uint64_t buffer_handle, int64_t timeout_ms, uint64_t *out) {
    if (timeout_ms < 0) { return EINVAL; }
    int code = 0;
    int count = 0;
    char **argv = kush_host_proc_argv((const KushBytes *)(uintptr_t)program_handle,
                                      (const KushBytes *)(uintptr_t)args_handle, &count, &code);
    if (argv == NULL) { return code; }
    int outpipe[2] = {-1, -1}, errpipe[2] = {-1, -1};
    if (pipe2(outpipe, O_CLOEXEC) != 0 || pipe2(errpipe, O_CLOEXEC) != 0) {
        code = errno;
        if (outpipe[0] >= 0) { (void)close(outpipe[0]); (void)close(outpipe[1]); }
        kush_host_proc_free(argv, count);
        return code;
    }
    pid_t child = fork();
    if (child < 0) {
        code = errno;
        (void)close(outpipe[0]); (void)close(outpipe[1]);
        (void)close(errpipe[0]); (void)close(errpipe[1]);
        kush_host_proc_free(argv, count);
        return code;
    }
    if (child == 0) {
        int devnull = open("/dev/null", O_RDWR);
        if (devnull >= 0) {
            (void)dup2(devnull, 0);
            (void)dup2(devnull, 2);
            if (devnull > 2) (void)close(devnull);
        }
        (void)dup2(outpipe[1], 1);
        (void)close(outpipe[0]);
        if (outpipe[1] > 2) (void)close(outpipe[1]);
        (void)close(errpipe[0]);
        execvp(argv[0], argv);
        int failure = errno;
        kush_best_effort_write(errpipe[1], &failure, sizeof(failure));
        _exit(127);
    }
    (void)close(outpipe[1]);
    (void)close(errpipe[1]);
    (void)fcntl(outpipe[0], F_SETFL, O_NONBLOCK);
    (void)fcntl(errpipe[0], F_SETFL, O_NONBLOCK);
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    uint64_t length = b->length;
    int64_t deadline = kush_host_deadline(timeout_ms);
    int failed = 0, timed_out = 0;
    for (;;) {
        int full = length == b->capacity;
        struct pollfd waiting = { outpipe[0], POLLIN | POLLHUP, 0 };
        int ready = poll(&waiting, 1, kush_host_remaining(deadline));
        if (ready < 0) {
            if (errno == EINTR) continue;
            code = errno; failed = 1; break;
        }
        if (ready == 0) {
            /* poll() returns 0 after at most 60s; only a drained budget is a
             * timeout, so long budgets stay valid. */
            if (deadline >= 0 && kush_host_remaining(deadline) != 0) continue;
            timed_out = 1; break;
        }
        if (full) {
            unsigned char probe;
            ssize_t received = read(outpipe[0], &probe, 1);
            if (received < 0 && (errno == EINTR || errno == EAGAIN)) continue;
            if (received < 0) { code = errno; failed = 1; break; }
            if (received == 0) break;
            code = EFBIG; failed = 1; break;
        }
        ssize_t received = read(outpipe[0], b->data + length, (size_t)(b->capacity - length));
        if (received < 0 && (errno == EINTR || errno == EAGAIN)) continue;
        if (received < 0) { code = errno; failed = 1; break; }
        if (received == 0) break;
        length += (uint64_t)received;
        b->length = length;
    }
    int status = 0;
    int exec_error = 0;
    if (!failed && !timed_out) {
        for (;;) {
            pid_t result = waitpid(child, &status, WNOHANG);
            if (result == child) break;
            if (result < 0 && errno != EINTR) { code = errno; failed = 1; break; }
            if (kush_host_remaining(deadline) == 0) { timed_out = 1; break; }
            struct timespec pause = {0, 2000000};
            (void)nanosleep(&pause, NULL);
        }
    }
    if (failed || timed_out) {
        (void)kill(child, SIGKILL);
        kush_host_reap(child, &status);
    }
    for (;;) {
        int failure = 0;
        ssize_t received = read(errpipe[0], &failure, sizeof(failure));
        if (received == (ssize_t)sizeof(failure)) { exec_error = failure; continue; }
        if (received < 0 && errno == EINTR) continue;
        break;
    }
    (void)close(outpipe[0]);
    (void)close(errpipe[0]);
    kush_host_proc_free(argv, count);
    if (timed_out) { return ETIMEDOUT; }
    if (failed) { return code; }
    if (exec_error != 0) { return exec_error; }
    if (WIFEXITED(status)) {
        *out = (uint64_t)WEXITSTATUS(status);
    } else if (WIFSIGNALED(status)) {
        *out = (uint64_t)(128 + WTERMSIG(status));
    } else {
        return EIO;
    }
    return 0;
}
static int64_t kush_host_connect(struct addrinfo *address, int64_t deadline) {
    int fd = socket(address->ai_family, address->ai_socktype | SOCK_CLOEXEC,
                    address->ai_protocol);
    if (fd < 0) return -errno;
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) {
        int code = errno; (void)close(fd); return -code;
    }
    if (connect(fd, address->ai_addr, address->ai_addrlen) != 0) {
        if (errno != EINPROGRESS) {
            int code = errno; (void)close(fd); return -code;
        }
        struct pollfd waiting = { fd, POLLOUT, 0 };
        int ready;
        for (;;) {
            ready = poll(&waiting, 1, kush_host_remaining(deadline));
            if (ready < 0 && errno == EINTR) continue;
            if (ready == 0 && deadline >= 0 && kush_host_remaining(deadline) != 0) continue;
            break;
        }
        if (ready < 0) { int code = errno; (void)close(fd); return -code; }
        if (ready == 0) { (void)close(fd); return -ETIMEDOUT; }
        int error = 0; socklen_t length = sizeof(error);
        if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &error, &length) != 0) {
            int code = errno; (void)close(fd); return -code;
        }
        if (error != 0) { (void)close(fd); return -error; }
    }
    return fd;
}
int64_t kush_net_tcp_exchange(uint64_t host_handle, int64_t port,
                              uint64_t request_handle, uint64_t response_handle,
                              int64_t timeout_ms, uint64_t *out) {
    if (timeout_ms < 0 || port <= 0 || port > 65535) {
        return EINVAL;
    }
    int code = 0;
    char *host = kush_host_c_path((const KushBytes *)(uintptr_t)host_handle, &code);
    if (host == NULL) { return code; }
    if (!kush_utf8_valid_data((const unsigned char *)host, (uint64_t)strlen(host))) {
        free(host);
        return EINVAL;
    }
    char service[8];
    (void)snprintf(service, sizeof(service), "%lld", (long long)port);
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    struct addrinfo *addresses = NULL;
    int resolved = getaddrinfo(host, service, &hints, &addresses);
    free(host);
    if (resolved != 0) {
        int failure = resolved == EAI_MEMORY ? ENOMEM : resolved == EAI_SYSTEM ? errno : EINVAL;
        return failure == 0 ? EINVAL : failure;
    }
    int64_t deadline = kush_host_deadline(timeout_ms);
    int fd = -1;
    int last = ECONNREFUSED;
    for (struct addrinfo *address = addresses; address != NULL; address = address->ai_next) {
        int64_t opened = kush_host_connect(address, deadline);
        if (opened >= 0) { fd = (int)opened; break; }
        last = (int)(-opened);
        if (last == ETIMEDOUT) break;
    }
    freeaddrinfo(addresses);
    if (fd < 0) { return last; }
    const KushBytes *request = (const KushBytes *)(uintptr_t)request_handle;
    uint64_t sent = 0;
    while (sent < request->length) {
        ssize_t written = send(fd, request->data + sent, (size_t)(request->length - sent),
                               MSG_NOSIGNAL);
        if (written < 0 && errno == EINTR) continue;
        if (written < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            struct pollfd waiting = { fd, POLLOUT, 0 };
            int ready = poll(&waiting, 1, kush_host_remaining(deadline));
            if (ready < 0 && errno == EINTR) continue;
            if (ready < 0) { code = errno; break; }
            if (ready == 0) {
                if (deadline >= 0 && kush_host_remaining(deadline) != 0) continue;
                code = ETIMEDOUT; break;
            }
            continue;
        }
        if (written < 0) { code = errno; break; }
        if (written == 0) { code = EIO; break; }
        sent += (uint64_t)written;
    }
    if (code == 0) (void)shutdown(fd, SHUT_WR);
    KushBytes *b = (KushBytes *)(uintptr_t)response_handle;
    uint64_t length = b->length;
    uint64_t received_total = 0;
    while (code == 0) {
        int full = length == b->capacity;
        struct pollfd waiting = { fd, POLLIN | POLLHUP, 0 };
        int ready = poll(&waiting, 1, kush_host_remaining(deadline));
        if (ready < 0) { if (errno == EINTR) continue; code = errno; break; }
        if (ready == 0) {
            if (deadline >= 0 && kush_host_remaining(deadline) != 0) continue;
            code = ETIMEDOUT; break;
        }
        unsigned char probe;
        void *destination = full ? (void *)&probe : (void *)(b->data + length);
        size_t room = full ? 1 : (size_t)(b->capacity - length);
        ssize_t count = recv(fd, destination, room, 0);
        if (count < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK)) continue;
        if (count < 0) { code = errno; break; }
        if (count == 0) break;
        if (full) { code = EFBIG; break; }
        length += (uint64_t)count;
        received_total += (uint64_t)count;
        b->length = length;
    }
    (void)close(fd);
    if (code != 0) { return code; }
    *out = received_total;
    return 0;
}
/* Vectors store fixed-width elements of `width` 64-bit words each. */
typedef struct { uint64_t length; uint64_t capacity; uint64_t data[]; } KushVec;
static uint64_t kush_vec_bytes(uint64_t capacity, uint64_t width) {
    if (width == 0 || capacity > ((uint64_t)INT64_MAX - sizeof(KushVec)) / 8 / width) kush_panic();
    return sizeof(KushVec) + capacity * width * 8;
}
uint64_t kush_vec_with_capacity(int64_t capacity, int64_t width) {
    if (capacity < 0 || width <= 0) kush_panic();
    KushVec *v = (KushVec *)(uintptr_t)kush_buffer_alloc(kush_vec_bytes((uint64_t)capacity, (uint64_t)width), (uint64_t)capacity, 0);
    v->length = 0;
    return (uint64_t)(uintptr_t)v;
}
int64_t kush_vec_len(uint64_t handle) { return (int64_t)((KushVec *)(uintptr_t)handle)->length; }
void kush_vec_get(uint64_t handle, int64_t index, uint64_t *out, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= v->length) kush_panic();
    memcpy(out, v->data + (uint64_t)index * width, (size_t)(width * 8));
}
uint64_t kush_vec_push(uint64_t handle, const uint64_t *item, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (v->length == kush_buffer_capacity(v)) {
        uint64_t next = kush_buffer_capacity(v) == 0 ? 4 : kush_buffer_capacity(v) * 2;
        if (next <= kush_buffer_capacity(v)) kush_panic();
        uint64_t bytes = kush_vec_bytes(next, width);
        v = (KushVec *)kush_buffer_grow(v, bytes);
        kush_buffer_set_capacity(v, next); ++kush_buffer_growths;
    }
    memcpy(v->data + v->length * width, item, (size_t)(width * 8));
    v->length++;
    return (uint64_t)(uintptr_t)v;
}
uint64_t kush_vec_set(uint64_t handle, int64_t index, const uint64_t *item, uint64_t *old, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= v->length) kush_panic();
    uint64_t *slot = v->data + (uint64_t)index * width;
    memcpy(old, slot, (size_t)(width * 8));
    memcpy(slot, item, (size_t)(width * 8));
    return handle;
}
/* Address of one checked vector element. The reference evaluator and native
   backend agree that an element reference is only formed while the vector
   owner is loaned, so no growth can move this storage. */
uint64_t kush_vec_element(uint64_t handle, int64_t index, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (index < 0 || (uint64_t)index >= v->length) kush_panic();
    return (uint64_t)(uintptr_t)(v->data + (uint64_t)index * width);
}
/* Ensure room for `additional` elements after the current length. Growth
   happens at most once, to exactly the requested length, and only when the
   retained capacity is insufficient. Negative or overflowing requests panic. */
uint64_t kush_vec_reserve(uint64_t handle, int64_t additional, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (additional < 0) kush_panic();
    uint64_t needed;
    if (__builtin_add_overflow(v->length, (uint64_t)additional, &needed)) kush_panic();
    if (needed <= kush_buffer_capacity(v)) return handle;
    KushVec *replacement = (KushVec *)kush_buffer_grow(v, kush_vec_bytes(needed, width));
    kush_buffer_set_capacity(replacement, needed);
    ++kush_buffer_growths;
    return (uint64_t)(uintptr_t)replacement;
}
/* On refusal or invalid capacity, the original allocation/header/elements
   remain untouched. Zero is an out-of-band failure handle, never an owner. */
uint64_t kush_vec_try_reserve(uint64_t handle, int64_t additional, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (additional < 0) return 0;
    uint64_t needed;
    if (__builtin_add_overflow(v->length, (uint64_t)additional, &needed)) return 0;
    if (needed <= kush_buffer_capacity(v)) return handle;
    if (width == 0 || needed > ((uint64_t)INT64_MAX - sizeof(KushVec)) / 8 / width) return 0;
    uint64_t bytes = sizeof(KushVec) + needed * width * 8;
    KushVec *replacement = (KushVec *)kush_buffer_try_grow(v, bytes);
    if (replacement == NULL) return 0;
    kush_buffer_set_capacity(replacement, needed);
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
    uint64_t bytes = kush_vec_bytes(kush_buffer_capacity(v), (uint64_t)target_width);
    KushVec *replacement = (KushVec *)kush_buffer_grow(v, bytes);
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
   Declared effect operations use a small per-task stack of handler code
   pointers and optional owned one-shot environments. A lexical handle pushes one entry for
   the duration of its body; a `perform` in a called function resolves the
   innermost matching entry. A one-shot entry transfers its environment on
   lookup, or drops it when popped without being consumed. */
#define KUSH_HANDLER_MAX 1024
typedef struct {
    int64_t operation;
    int64_t code;
    int64_t environment;
    int64_t once;
    int64_t consumed;
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
/* Drop an unconsumed owning handler environment. The closure environment
   header stores its drop function at offset zero, exactly like a `once`
   closure value produced by the checked backend. */
static void kush_handler_drop_frame(kush_handler_frame *frame) {
    if (frame->environment != 0) {
        void (*drop)(void *) =
            *(void (**)(void *))(uintptr_t)frame->environment;
        int64_t environment = frame->environment;
        frame->environment = 0;
        drop((void *)(uintptr_t)environment);
    }
}
/* E-ABORT-PROPAGATE: nonzero while an abort travels up the stack; the value
   is the payload buffer of the addressed abortive handle activation. Tasks
   share one OS thread and an abort never yields or crosses a task. */
int64_t kush_abort_word = 0;
int64_t kush_handler_depth(void) {
    return kush_handlers()->depth;
}
void kush_handler_restore(int64_t depth) {
    if (depth < 0) depth = 0;
    kush_handler_context *handlers = kush_handlers();
    while (handlers->depth > depth) {
        handlers->depth -= 1;
        kush_handler_drop_frame(&handlers->frames[handlers->depth]);
    }
}
void kush_handler_push(int64_t operation, int64_t code, int64_t environment,
                       int64_t once) {
    kush_handler_context *handlers = kush_handlers();
    if (handlers->depth >= KUSH_HANDLER_MAX) kush_panic();
    handlers->frames[handlers->depth].operation = operation;
    handlers->frames[handlers->depth].code = code;
    handlers->frames[handlers->depth].environment = environment;
    handlers->frames[handlers->depth].once = once;
    handlers->frames[handlers->depth].consumed = 0;
    handlers->depth += 1;
}
void kush_handler_pop(void) {
    kush_handler_context *handlers = kush_handlers();
    if (handlers->depth > 0) {
        handlers->depth -= 1;
        kush_handler_drop_frame(&handlers->frames[handlers->depth]);
    }
}
/* A resumed continuation of a declared-operation handle hides the frames its
   handler pushed around `resume`: a redirect frame (operation -1) sends the
   lookup below `code`, the depth recorded at the suspension. It is pushed
   only when such frames exist, owns nothing, and is a task-inheritance
   barrier. Returns the depth to restore after the continuation. */
int64_t kush_handler_redirect(int64_t target) {
    kush_handler_context *handlers = kush_handlers();
    int64_t before = handlers->depth;
    if (before > target) {
        if (handlers->depth >= KUSH_HANDLER_MAX) kush_panic();
        handlers->frames[handlers->depth].operation = -1;
        handlers->frames[handlers->depth].code = target;
        handlers->frames[handlers->depth].environment = 0;
        handlers->frames[handlers->depth].once = 1;
        handlers->frames[handlers->depth].consumed = 1;
        handlers->depth += 1;
    }
    return before;
}
int64_t kush_handler_lookup(int64_t operation, int64_t *out) {
    kush_handler_context *handlers = kush_handlers();
    for (int64_t index = handlers->depth - 1; index >= 0; --index) {
        kush_handler_frame *frame = &handlers->frames[index];
        if (frame->operation == -1) {
            index = frame->code;
            continue;
        }
        if (frame->operation != operation) continue;
        /* A consumed once frame still discharges its operation: a later
           perform must not fall through to an outer handler. */
        if (frame->consumed) return 0;
        out[0] = frame->code;
        out[1] = frame->environment;
        out[2] = frame->once;
        if (frame->once) {
            /* A once handler transfers its environment to this call. The
               callee frees it, so the frame must never drop it again. */
            frame->consumed = 1;
            frame->environment = 0;
        }
        return 1;
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
    /* Inherit the parent's copyable noncapturing dynamic handler frames.
       A capturing or one-shot frame is a task boundary: its environment is
       owned by the parent's dynamic extent, so only the longest inheritable
       innermost contiguous suffix crosses. Frames below a barrier must not
       become visible to a child merely because their shadowing frame cannot
       be inherited. */
    {
        kush_handler_context *parent = kush_handlers();
        kush_handler_context *child = &kush_handler_contexts[id];
        child->depth = 0;
        /* Walk the frames visible to the parent: a redirect frame (pushed by
           a resumed continuation) skips the frames its handler pushed. */
        static int64_t picked[KUSH_HANDLER_MAX];
        int64_t count = 0;
        int64_t index = parent->depth - 1;
        while (index >= 0) {
            kush_handler_frame *frame = &parent->frames[index];
            if (frame->operation == -1) {
                index = frame->code - 1;
                continue;
            }
            if (frame->environment != 0 || frame->once) break;
            picked[count++] = index;
            index -= 1;
        }
        for (int64_t i = count - 1; i >= 0; --i) {
            child->frames[child->depth] = parent->frames[picked[i]];
            child->depth += 1;
        }
    }
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
int main(int argc, char **argv) {
    kush_host_init(argc, argv);
    /* Broken pipes become recoverable EPIPE results instead of process signals. */
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) kush_panic();
    kush_stack_guard_init();
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
        if (length > 0) kush_best_effort_write(2, line, (size_t)(length < (int)sizeof(line) ? length : (int)sizeof(line) - 1));
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
        if (length > 0) kush_best_effort_write(2, line, (size_t)(length < (int)sizeof(line) ? length : (int)sizeof(line) - 1));
    }
#endif
    if (kush_live_allocations != 0) {
        static const char message[] = "panic: live owning allocations after normal exit\n";
        kush_best_effort_write(2, message, sizeof(message)-1); abort();
    }
    return (int)((uint64_t)result & UINT64_C(255));
}
"#;

/// The vector locals a loop touches through `v = Vec.push(v, e)` and
/// read-only length or element reads alone, so that nothing else in the loop
/// can change their length or capacity. Loops containing an expression kind
/// this does not know the shape of yield nothing.
fn push_only_vectors(condition: &Expr, body: &ex::Block) -> Vec<usize> {
    #[derive(Default)]
    struct Uses {
        pushed: std::collections::BTreeSet<usize>,
        /// Mentioned some other way, or declared inside the loop.
        other: std::collections::BTreeSet<usize>,
        unknown: bool,
    }
    fn slot_of(expr: &Expr) -> Option<usize> {
        match expr.kind {
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::Peek(slot) => Some(slot),
            _ => None,
        }
    }
    fn block(block: &ex::Block, uses: &mut Uses) {
        for statement in &block.statements {
            match statement {
                ex::Statement::Let(slot, value) => {
                    uses.other.insert(*slot);
                    expr(value, uses);
                }
                ex::Statement::Expr(value) => expr(value, uses),
                ex::Statement::Declare(slot) => {
                    uses.other.insert(*slot);
                }
            }
        }
        if let Some(tail) = &block.tail {
            expr(tail, uses);
        }
    }
    fn expr(e: &Expr, uses: &mut Uses) {
        match &e.kind {
            ExprKind::Constant(_) => {}
            ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::Borrow(slot)
            | ExprKind::Peek(slot) => {
                uses.other.insert(*slot);
            }
            ExprKind::Assign(slot, value) => {
                if let ExprKind::Call(Target::Vec(VecOp::Push, _), arguments) = &value.kind
                    && let [vector, item] = arguments.as_slice()
                    && matches!(vector.kind, ExprKind::Move(moved) | ExprKind::Local(moved) if moved == *slot)
                {
                    uses.pushed.insert(*slot);
                    expr(item, uses);
                } else {
                    uses.other.insert(*slot);
                    expr(value, uses);
                }
            }
            ExprKind::Call(target, arguments) => {
                let reads = matches!(target, Target::Vec(VecOp::Len | VecOp::Get, _));
                for (index, argument) in arguments.iter().enumerate() {
                    if reads && index == 0 && slot_of(argument).is_some() {
                        continue;
                    }
                    expr(argument, uses);
                }
            }
            ExprKind::Unary(_, operand) => expr(operand, uses),
            ExprKind::Binary(_, left, right) => {
                expr(left, uses);
                expr(right, uses);
            }
            ExprKind::If(test, then_block, else_block) => {
                expr(test, uses);
                block(then_block, uses);
                block(else_block, uses);
            }
            ExprKind::Block(inner) => block(inner, uses),
            ExprKind::While(test, inner) => {
                expr(test, uses);
                block(inner, uses);
            }
            ExprKind::Break(None, _) | ExprKind::Continue(_) => {}
            _ => uses.unknown = true,
        }
    }
    let mut uses = Uses::default();
    expr(condition, &mut uses);
    block(body, &mut uses);
    if uses.unknown {
        return Vec::new();
    }
    uses.pushed.difference(&uses.other).copied().collect()
}

/// Extra inputs for the native link step. Every path is passed to `cc` as one
/// argument (no shell interpolation); library names are validated identifiers
/// for `cc -l<name>`.
///
/// The compiler never invents search paths. Explicit Cargo adapters may resolve
/// their declared dependencies through Cargo. A project
/// manifest should turn its declared native dependencies into one of these
/// values and pass it to [`build_with_options`].
#[derive(Debug, Clone, Default)]
pub struct LinkSpec {
    /// Additional object files or static archives, linked before libraries.
    pub objects: Vec<PathBuf>,
    /// Static/shared libraries by absolute or caller-relative path.
    pub libraries: Vec<PathBuf>,
    /// Additional `-L` search directories.
    pub library_dirs: Vec<PathBuf>,
    /// Additional `-l` names (for example `pthread`), each a bare identifier.
    pub system_libraries: Vec<String>,
}
impl LinkSpec {
    /// Validate link inputs without touching the filesystem. Paths may not be
    /// empty and library names cannot smuggle flags or shell syntax.
    pub fn validate(&self) -> Result<()> {
        for path in self.objects.iter().chain(&self.libraries) {
            if path.as_os_str().is_empty() {
                return Err(error("a native link input path must not be empty"));
            }
            if path.to_string_lossy().starts_with(['-', '@']) {
                return Err(error(format!(
                    "native link input '{}' must not start with '-' or '@'; write an explicit path",
                    path.display()
                )));
            }
        }
        for path in &self.library_dirs {
            if path.as_os_str().is_empty() {
                return Err(error("a native library search directory must not be empty"));
            }
        }
        for name in &self.system_libraries {
            let valid = !name.is_empty()
                && !name.starts_with('-')
                && name
                    .chars()
                    .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '+' | '.'));
            if !valid {
                return Err(error(format!(
                    "native library name '{name}' must be a bare -l name without flags or path separators"
                )));
            }
        }
        Ok(())
    }
    /// Map the reserved project manifest fields to concrete link inputs.
    ///
    /// * `libraries` entries that look like a path (contain a separator or end
    ///   in `.a`/`.o`/`.so`/`.dylib`) become explicit paths, resolved against
    ///   `root` when relative. Other entries are bare `-l` names.
    /// * `library_paths` become `-L` directories.
    /// * every `cargo_manifests` entry is built as a release static library
    ///   with `cargo build --release --lib --message-format=json`; the emitted
    ///   `.a` is linked explicitly. Rust std static libraries also need
    ///   `pthread` and `dl` on the Linux backend, so those are added once.
    ///
    /// This is deliberately a pure mapping/validation step plus the explicit
    /// Cargo subprocess for manifests the project author opted into. It never
    /// searches the host for libraries, downloads crates implicitly, or shells
    /// out through a command string.
    pub fn from_project_native(
        root: &Path,
        libraries: &[String],
        library_paths: &[PathBuf],
        cargo_manifests: &[PathBuf],
    ) -> Result<Self> {
        let mut spec = Self {
            library_dirs: library_paths.to_vec(),
            ..Self::default()
        };
        for library in libraries {
            if library.is_empty() || library.contains('\0') {
                return Err(error("a native library entry must not be empty"));
            }
            if library.starts_with('-') {
                return Err(error(format!(
                    "native library entry '{library}' must not start with '-'; write a bare name or an explicit path"
                )));
            }
            let path_like = library.contains('/')
                || library.contains('\\')
                || library.ends_with(".a")
                || library.ends_with(".o")
                || library.ends_with(".so")
                || library.contains(".so.")
                || library.ends_with(".dylib");
            if path_like {
                let path = Path::new(library);
                if path.is_absolute()
                    || path
                        .components()
                        .any(|part| matches!(part, std::path::Component::ParentDir))
                {
                    return Err(error(
                        "native library paths must be relative to their package and may not contain '..'",
                    ));
                }
                spec.libraries.push(root.join(library));
            } else {
                spec.system_libraries.push(library.clone());
            }
        }
        for manifest in cargo_manifests {
            spec.libraries.push(build_cargo_static_library(manifest)?);
            for library in ["pthread", "dl"] {
                if !spec.system_libraries.iter().any(|name| name == library) {
                    spec.system_libraries.push(library.to_owned());
                }
            }
        }
        spec.validate()?;
        Ok(spec)
    }
}

/// Build one Cargo adapter crate as a release static library and return the
/// emitted `.a` path. The manifest must set `crate-type = ["staticlib"]`.
/// Cargo's JSON artifact stream is the source of truth, so workspaces and custom
/// target directories work without guessing paths.
pub fn build_cargo_static_library(manifest: &Path) -> Result<PathBuf> {
    let manifest = manifest.canonicalize().map_err(error)?;
    let adapter_target = manifest
        .parent()
        .expect("manifest parent")
        .join("target/kush-adapter");
    let output = Command::new("cargo")
        // Adapter Cargo outputs must never overwrite mbx's read-only compiler cache.
        .env("CARGO_TARGET_DIR", adapter_target)
        .arg("build")
        .arg("--jobs")
        .arg("2")
        .arg("--release")
        .arg("--lib")
        .arg("--message-format=json")
        .arg("--manifest-path")
        .arg(&manifest)
        .output()
        .map_err(|e| {
            error(format!(
                "cannot start cargo for '{}': {e}",
                manifest.display()
            ))
        })?;
    if !output.status.success() {
        return Err(error(format!(
            "cargo build failed for native adapter '{}': {}",
            manifest.display(),
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        let Ok(message) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if message["reason"] != "compiler-artifact" {
            continue;
        }
        let Some(path) = message["manifest_path"].as_str() else {
            continue;
        };
        if Path::new(path) != manifest {
            continue;
        }
        if !message["target"]["crate_types"]
            .as_array()
            .is_some_and(|types| types.iter().any(|ty| ty == "staticlib"))
        {
            continue;
        }
        if let Some(archive) = message["filenames"].as_array().and_then(|files| {
            files
                .iter()
                .filter_map(|file| file.as_str())
                .find(|file| Path::new(file).extension().is_some_and(|ext| ext == "a"))
        }) {
            return Ok(PathBuf::from(archive));
        }
    }
    Err(error(format!(
        "native adapter '{}' did not emit a static library; set `crate-type = [\"staticlib\"]` in its [lib] section",
        manifest.display()
    )))
}

/// Compile and link atomically in the output's directory. No shell expansion or
/// user-supplied flags; a failed build leaves the previous output intact.
/// Native optimization controls. Defaults preserve the existing fast-build path.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Optimization {
    #[default]
    None,
    Speed,
}

/// Which code generator consumes the lowered program. Both receive the same
/// verified Cranelift IR from the one lowering in this module.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Backend {
    /// Cranelift machine code: fast builds, the default.
    #[default]
    Cranelift,
    /// LLVM IR optimized by `clang`, with runtime accessors inlined into
    /// user code: slower builds, fastest programs. Requires `clang`;
    /// `llvm-link` from the same LLVM enables the inlining.
    Llvm,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CodegenOptions {
    pub optimization: Optimization,
    pub inline_scalar_callbacks: bool,
    pub backend: Backend,
    /// Defer overflow panics of side-effect-free loop arithmetic to the end
    /// of a bounded chunk of iterations so LLVM can vectorize it. Observable
    /// behaviour is unchanged: the program still panics exactly when checked
    /// arithmetic would. `None` follows the backend: on for LLVM, off for
    /// Cranelift.
    pub deferred_overflow: Option<bool>,
    /// Tune LLVM code for the build machine's CPU (`-march=native`).
    pub native_cpu: bool,
}
impl CodegenOptions {
    /// Cranelift with explicit, independent controls.
    pub const fn cranelift(optimization: Optimization, inline_scalar_callbacks: bool) -> Self {
        Self {
            optimization,
            inline_scalar_callbacks,
            backend: Backend::Cranelift,
            deferred_overflow: None,
            native_cpu: false,
        }
    }
    pub const fn release() -> Self {
        Self {
            optimization: Optimization::Speed,
            inline_scalar_callbacks: true,
            backend: Backend::Cranelift,
            deferred_overflow: None,
            native_cpu: false,
        }
    }
    /// `KUSH_BACKEND=llvm|cranelift` overrides the backend of every native
    /// build in this process, so an entire test suite can be replayed on the
    /// other backend without changing its sources.
    fn with_environment(mut self) -> Result<Self> {
        match std::env::var("KUSH_BACKEND").ok().as_deref() {
            None | Some("") => {}
            Some("cranelift") => self.backend = Backend::Cranelift,
            Some("llvm") => self.backend = Backend::Llvm,
            // Also at release settings, whatever the build asked for.
            Some("llvm-release") => {
                self.backend = Backend::Llvm;
                self.optimization = Optimization::Speed;
                self.inline_scalar_callbacks = true;
            }
            Some(other) => {
                return Err(error(format!(
                    "KUSH_BACKEND must be 'cranelift', 'llvm' or 'llvm-release', not '{other}'"
                )));
            }
        }
        Ok(self)
    }
    /// Whether loops are lowered with deferred overflow checks.
    fn defers_overflow(self) -> bool {
        self.deferred_overflow
            .unwrap_or(self.backend == Backend::Llvm)
    }
    /// The backend a build with these options uses, for messages. Honours
    /// the `KUSH_BACKEND` override.
    pub fn backend_name(self) -> &'static str {
        match self.with_environment().map(|options| options.backend) {
            Ok(Backend::Llvm) => "LLVM",
            _ => "Cranelift",
        }
    }
    /// Whether generated code may assume a native 64-bit vector multiply:
    /// only when tuning for this machine and it has AVX-512DQ.
    fn wide_multiply(self) -> bool {
        #[cfg(target_arch = "x86_64")]
        {
            self.native_cpu && std::arch::is_x86_feature_detected!("avx512dq")
        }
        #[cfg(not(target_arch = "x86_64"))]
        {
            false
        }
    }
    /// Release settings on the LLVM backend.
    pub const fn release_llvm() -> Self {
        Self {
            optimization: Optimization::Speed,
            inline_scalar_callbacks: true,
            backend: Backend::Llvm,
            deferred_overflow: None,
            native_cpu: false,
        }
    }
}

pub fn build(program: &Executable, output: &Path) -> Result<()> {
    build_with_options(program, output, false, &LinkSpec::default())
}

/// Build an executable that reports allocation diagnostics to stderr on a
/// normal exit. The program's own stdout and exit status are unchanged.
pub fn build_with_stats(program: &Executable, output: &Path, stats: bool) -> Result<()> {
    build_with_options(program, output, stats, &LinkSpec::default())
}

/// Build with explicit native link inputs. `LinkSpec::validate` runs before any
/// file is written or `cc` is started.
pub fn build_with_options(
    program: &Executable,
    output: &Path,
    stats: bool,
    links: &LinkSpec,
) -> Result<()> {
    build_with_codegen(program, output, stats, links, CodegenOptions::default())
}

/// Build with explicit, independently selectable optimization controls.
pub fn build_with_codegen(
    program: &Executable,
    output: &Path,
    stats: bool,
    links: &LinkSpec,
    codegen: CodegenOptions,
) -> Result<()> {
    links.validate()?;
    let codegen = codegen.with_environment()?;
    let parent = output
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let scratch = Scratch::new(parent)?;
    let mut defines = Vec::new();
    if program.uses_tasks {
        defines.push("-DKUSH_HAS_TASKS=1".to_owned());
    }
    if stats {
        defines.push("-DKUSH_STATS=1".to_owned());
        defines.push(format!("-DKUSH_FUSION_COUNT={}", program.fusion_count()));
    }
    let objects = match codegen.backend {
        Backend::Cranelift => {
            let object = object(program, codegen)?;
            let object_path = scratch.path.join("program.o");
            let runtime_object = runtime_cache::compile(RUNTIME, &defines, &scratch)?;
            fs::write(&object_path, object).map_err(error)?;
            vec![object_path, runtime_object]
        }
        Backend::Llvm => llvm_objects(program, codegen, &defines, &scratch)?,
    };
    let binary_path = scratch.path.join("program");
    let mut command = Command::new("cc");
    command.arg("-std=c11").arg("-O2").args(&objects);
    for path in &links.objects {
        command.arg(path);
    }
    for path in &links.libraries {
        command.arg(path);
    }
    for dir in &links.library_dirs {
        command.arg("-L").arg(dir);
    }
    for name in &links.system_libraries {
        command.arg(format!("-l{name}"));
    }
    command.arg("-o").arg(&binary_path).arg("-lm");
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

/// The LLVM toolchain used by the release backend. `clang` comes from
/// `KUSH_CLANG` or `PATH`; `llvm-link` is the one that same `clang` reports,
/// so the IR versions always agree.
struct LlvmTools {
    clang: PathBuf,
    /// `llvm-link`, when whole-program optimization is available.
    link: Option<PathBuf>,
}
impl LlvmTools {
    fn find() -> Result<Self> {
        let clang = PathBuf::from(
            std::env::var_os("KUSH_CLANG").unwrap_or_else(|| std::ffi::OsString::from("clang")),
        );
        // The companion normally sits beside the real clang binary; finding
        // it there avoids starting clang just to ask.
        let resolved = if clang.components().count() > 1 {
            Some(clang.clone())
        } else {
            std::env::var_os("PATH").and_then(|path| {
                std::env::split_paths(&path)
                    .map(|directory| directory.join(&clang))
                    .find(|candidate| candidate.is_file())
            })
        };
        // Only beside a binary that is itself clang: a compiler wrapper
        // (ccache and the like) lives elsewhere than the LLVM it runs.
        let sibling = resolved
            .and_then(|path| fs::canonicalize(path).ok())
            .filter(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.starts_with("clang"))
            })
            .and_then(|path| Some(path.parent()?.join("llvm-link")))
            .filter(|path| path.is_file());
        let link = match sibling {
            Some(link) => link,
            None => {
                let probe = Command::new(&clang)
                    .arg("-print-prog-name=llvm-link")
                    .output()
                    .map_err(|e| {
                        error(format!(
                            "the LLVM backend needs clang (install it or set KUSH_CLANG): {e}"
                        ))
                    })?;
                if !probe.status.success() {
                    return Err(error(format!(
                        "the LLVM backend could not run '{}'",
                        clang.display()
                    )));
                }
                PathBuf::from(String::from_utf8_lossy(&probe.stdout).trim())
            }
        };
        let link = (std::env::var_os("KUSH_LLVM_NO_WHOLE_PROGRAM").is_none()
            && link.is_absolute()
            && link.is_file())
        .then_some(link);
        Ok(Self { clang, link })
    }
}

fn run_tool(command: &mut Command, what: &str) -> Result<()> {
    let output = command
        .output()
        .map_err(|e| error(format!("could not start {what}: {e}")))?;
    if !output.status.success() {
        return Err(error(format!(
            "{what} failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    Ok(())
}

/// The program's own LLVM module as text, before it is merged with the
/// runtime and optimized. Needs `clang` to learn the runtime's signatures.
pub fn emit_llvm_ir(program: &Executable, codegen: CodegenOptions) -> Result<String> {
    let tools = LlvmTools::find()?;
    let scratch = Scratch::new(&std::env::temp_dir())?;
    let mut defines = Vec::new();
    if program.uses_tasks {
        defines.push("-DKUSH_HAS_TASKS=1".to_owned());
    }
    let runtime = runtime_cache::compile_llvm(RUNTIME, &defines, &scratch, &tools.clang)?;
    let interface = llvm::RuntimeInterface::parse(&runtime.interface);
    match lower(program, codegen, Some(interface))? {
        Lowered::Llvm(text) => Ok(text),
        Lowered::Object(_) => unreachable!("the LLVM backend lowers to LLVM IR"),
    }
}

/// Lower through the LLVM backend and return the objects to link.
///
/// The runtime is compiled once (and cached) into an ordinary object plus a
/// bitcode file of the same definitions marked `available_externally`. Each
/// build links the definitions the program reaches into the program module,
/// where LLVM may inline them into user code and then discards them; anything
/// not inlined is called in the runtime object. Only program code is
/// optimized and compiled per build, like a Rust program against its
/// precompiled standard library. Without `llvm-link` the program module is
/// compiled alone and runtime operations stay calls.
fn llvm_objects(
    program: &Executable,
    codegen: CodegenOptions,
    defines: &[String],
    scratch: &Scratch,
) -> Result<Vec<PathBuf>> {
    let tools = LlvmTools::find()?;
    let runtime = runtime_cache::compile_llvm(RUNTIME, defines, scratch, &tools.clang)?;
    let interface = llvm::RuntimeInterface::parse(&runtime.interface);
    let Lowered::Llvm(text) = lower(program, codegen, Some(interface))? else {
        unreachable!("the LLVM backend lowers to LLVM IR")
    };
    let program_ir = scratch.path.join("program.ll");
    fs::write(&program_ir, text).map_err(error)?;
    if let Some(path) = std::env::var_os("KUSH_EMIT_LLVM") {
        fs::copy(&program_ir, path).map_err(error)?;
    }
    let object = scratch.path.join("program.o");
    let level = match codegen.optimization {
        Optimization::None => "-O1",
        Optimization::Speed => "-O3",
    };
    let mut compile = Command::new(&tools.clang);
    compile.arg(level).arg("-fPIC").arg("-c");
    if codegen.native_cpu {
        compile.arg("-march=native");
    }
    // The module is generated; clang's note about overriding its target
    // triple is not a user diagnostic.
    compile.arg("-Wno-override-module");
    let input = match &tools.link {
        Some(link) => {
            let linked = scratch.path.join("linked.bc");
            // A linker from another LLVM cannot read this clang's bitcode.
            // Inlining the runtime is an optimization; do without it.
            match run_tool(
                Command::new(link)
                    .arg(&program_ir)
                    .arg(&runtime.inline)
                    .arg("--only-needed")
                    .arg("-o")
                    .arg(&linked),
                "llvm-link",
            ) {
                Ok(()) => linked,
                Err(_) => program_ir,
            }
        }
        None => program_ir,
    };
    compile.arg(&input).arg("-o").arg(&object);
    run_tool(&mut compile, "clang (LLVM backend)")?;
    Ok(vec![object, runtime.object])
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

/// Only HandlerPush changes the local dynamic-handler depth. The exhaustive
/// child walker includes guards, initializers, conditions and capture operands;
/// separately compiled callback bodies perform their own analysis.
fn block_installs_handler(block: &ex::Block) -> bool {
    fn expression(expr: &Expr) -> bool {
        if matches!(
            expr.kind,
            ExprKind::HandlerPush { .. }
                | ExprKind::HandlerRedirect { .. }
                | ExprKind::AbortScope {
                    operation: Some(_),
                    ..
                }
        ) {
            return true;
        }
        let mut found = false;
        expr.for_each_child(&mut |child| found |= expression(child));
        found
    }
    block.statements.iter().any(|statement| match statement {
        ex::Statement::Let(_, value) | ex::Statement::Expr(value) => expression(value),
        ex::Statement::Declare(_) => false,
    }) || block.tail.as_ref().is_some_and(|value| expression(value))
}

/// What one lowering produced.
enum Lowered {
    Object(Vec<u8>),
    Llvm(String),
}

/// The module `Generator` lowers into. Declarations, signatures and function
/// bodies are always built with Cranelift's module and IR builders. With the
/// LLVM backend selected, each verified function body is translated to LLVM
/// IR instead of being compiled by Cranelift.
struct CodeModule {
    object: ObjectModule,
    llvm: Option<llvm::LlvmModule>,
    failure: Option<Diagnostic>,
    /// Functions referred to by the bodies defined so far.
    referenced: std::collections::BTreeSet<FuncId>,
}
impl Module for CodeModule {
    fn isa(&self) -> &dyn cranelift_codegen::isa::TargetIsa {
        self.object.isa()
    }
    fn declarations(&self) -> &cranelift_module::ModuleDeclarations {
        self.object.declarations()
    }
    fn declare_function(
        &mut self,
        name: &str,
        linkage: Linkage,
        signature: &ir::Signature,
    ) -> cranelift_module::ModuleResult<FuncId> {
        self.object.declare_function(name, linkage, signature)
    }
    fn declare_anonymous_function(
        &mut self,
        signature: &ir::Signature,
    ) -> cranelift_module::ModuleResult<FuncId> {
        self.object.declare_anonymous_function(signature)
    }
    fn declare_data(
        &mut self,
        name: &str,
        linkage: Linkage,
        writable: bool,
        tls: bool,
    ) -> cranelift_module::ModuleResult<DataId> {
        self.object.declare_data(name, linkage, writable, tls)
    }
    fn declare_anonymous_data(
        &mut self,
        writable: bool,
        tls: bool,
    ) -> cranelift_module::ModuleResult<DataId> {
        self.object.declare_anonymous_data(writable, tls)
    }
    fn define_function_with_control_plane(
        &mut self,
        func: FuncId,
        ctx: &mut cranelift_codegen::Context,
        ctrl_plane: &mut cranelift_codegen::control::ControlPlane,
    ) -> cranelift_module::ModuleResult<()> {
        for (_, name) in ctx.func.params.user_named_funcs().iter() {
            if name.namespace == 0 {
                self.referenced.insert(FuncId::from_u32(name.index));
            }
        }
        let Some(llvm) = &mut self.llvm else {
            return self
                .object
                .define_function_with_control_plane(func, ctx, ctrl_plane);
        };
        // Same acceptance rule as the Cranelift backend: only verified IR.
        cranelift_codegen::verify_function(&ctx.func, self.object.isa()).map_err(|errors| {
            cranelift_module::ModuleError::Compilation(cranelift_codegen::CodegenError::Verifier(
                errors,
            ))
        })?;
        if let Err(diagnostic) = llvm.define_function(func, &ctx.func, self.object.declarations()) {
            self.failure.get_or_insert(diagnostic);
        }
        Ok(())
    }
    fn define_function_bytes(
        &mut self,
        func_id: FuncId,
        alignment: u64,
        bytes: &[u8],
        relocs: &[cranelift_module::ModuleReloc],
    ) -> cranelift_module::ModuleResult<()> {
        self.object
            .define_function_bytes(func_id, alignment, bytes, relocs)
    }
    fn define_data(
        &mut self,
        data_id: DataId,
        data: &DataDescription,
    ) -> cranelift_module::ModuleResult<()> {
        let Some(llvm) = &mut self.llvm else {
            return self.object.define_data(data_id, data);
        };
        let bytes = match &data.init {
            cranelift_module::Init::Bytes { contents } => contents.to_vec(),
            cranelift_module::Init::Zeros { size } => vec![0; *size],
            cranelift_module::Init::Uninitialized => Vec::new(),
        };
        llvm.define_data(data_id, bytes);
        Ok(())
    }
}

fn object(program: &Executable, codegen: CodegenOptions) -> Result<Vec<u8>> {
    match lower(program, codegen, None)? {
        Lowered::Object(bytes) => Ok(bytes),
        Lowered::Llvm(_) => unreachable!("no LLVM runtime interface was supplied"),
    }
}

fn lower(
    program: &Executable,
    codegen: CodegenOptions,
    llvm: Option<llvm::RuntimeInterface>,
) -> Result<Lowered> {
    if !cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        return Err(error(
            "the first native backend supports Linux x86-64 hosts only",
        ));
    }
    let entry = program.entry()?;
    let mut flags = settings::builder();
    flags.set("is_pic", "true").map_err(error)?;
    // A frame larger than a page must touch every page on the way down, or
    // it could step over the guard below the stack.
    flags.set("enable_probestack", "true").map_err(error)?;
    flags.set("probestack_strategy", "inline").map_err(error)?;
    flags
        .set(
            "opt_level",
            match codegen.optimization {
                Optimization::None => "none",
                Optimization::Speed => "speed",
            },
        )
        .map_err(error)?;
    let isa = cranelift_native::builder_with_options(false)
        .map_err(error)?
        .finish(settings::Flags::new(flags))
        .map_err(error)?;
    let mut module = CodeModule {
        object: ObjectModule::new(
            ObjectBuilder::new(isa, "kush", default_libcall_names()).map_err(error)?,
        ),
        llvm: llvm.map(llvm::LlvmModule::new),
        failure: None,
        referenced: std::collections::BTreeSet::new(),
    };
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
    let bytes_free = module
        .declare_function("kush_bytes_free", Linkage::Import, &free_sig)
        .map_err(error)?;
    let buffer_free = module
        .declare_function("kush_buffer_free", Linkage::Import, &free_sig)
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
        .extend((0..4).map(|_| AbiParam::new(I64)));
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
        .extend((0..6).map(|_| AbiParam::new(I64)));
    alloc_vec_create_sig.returns.push(AbiParam::new(I64));
    let alloc_vec_create = module
        .declare_function(
            "kush_alloc_vec_create",
            Linkage::Import,
            &alloc_vec_create_sig,
        )
        .map_err(error)?;
    let mut alloc_context_new_sig = module.make_signature();
    alloc_context_new_sig
        .params
        .extend((0..5).map(|_| AbiParam::new(I64)));
    alloc_context_new_sig.returns.push(AbiParam::new(I64));
    let alloc_context_new = module
        .declare_function(
            "kush_alloc_context_new",
            Linkage::Import,
            &alloc_context_new_sig,
        )
        .map_err(error)?;
    let alloc_context_share = module
        .declare_function(
            "kush_alloc_context_share",
            Linkage::Import,
            &alloc_unary_sig,
        )
        .map_err(error)?;
    let alloc_context_release = module
        .declare_function("kush_alloc_context_release", Linkage::Import, &free_sig)
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
    let alloc_vec_try_push = module
        .declare_function(
            "kush_alloc_vec_try_push",
            Linkage::Import,
            &alloc_vec_push_sig,
        )
        .map_err(error)?;
    let mut alloc_vec_pop_sig = module.make_signature();
    alloc_vec_pop_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64)]);
    let alloc_vec_pop = module
        .declare_function("kush_alloc_vec_pop", Linkage::Import, &alloc_vec_pop_sig)
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
        context_new: alloc_context_new,
        context_share: alloc_context_share,
        context_release: alloc_context_release,
        block_data: alloc_block_data,
        box_create: alloc_box_create,
        box_payload: alloc_box_payload,
        box_release: alloc_box_release,
        vec_create: alloc_vec_create,
        vec_push: alloc_vec_push,
        vec_try_push: alloc_vec_try_push,
        vec_pop: alloc_vec_pop,
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
    let str_ascii_upper = module
        .declare_function("kush_str_ascii_upper", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let str_ascii_lower = module
        .declare_function("kush_str_ascii_lower", Linkage::Import, &str_range_sig)
        .map_err(error)?;
    let mut str_set_sig = module.make_signature();
    str_set_sig.params.extend([
        AbiParam::new(I64),
        AbiParam::new(I64),
        AbiParam::new(I64),
        AbiParam::new(I64),
    ]);
    str_set_sig.returns.push(AbiParam::new(I64));
    let str_set_scalar = module
        .declare_function("kush_str_set_scalar", Linkage::Import, &str_set_sig)
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
    let mut vec_element_sig = module.make_signature();
    vec_element_sig
        .params
        .extend([AbiParam::new(I64), AbiParam::new(I64), AbiParam::new(I64)]);
    vec_element_sig.returns.push(AbiParam::new(I64));
    let vec_element = module
        .declare_function("kush_vec_element", Linkage::Import, &vec_element_sig)
        .map_err(error)?;
    let mut vec_ops = BTreeMap::new();
    for (op, name, params, returns) in [
        (VecOp::WithCapacity, "kush_vec_with_capacity", 2, true),
        (VecOp::Reserve, "kush_vec_reserve", 3, true),
        (
            VecOp::TryReserve {
                ok_tag: 0,
                err_tag: 0,
            },
            "kush_vec_try_reserve",
            3,
            true,
        ),
        (VecOp::Len, "kush_vec_len", 1, true),
        (VecOp::Get, "kush_vec_get", 4, false),
        (VecOp::Push, "kush_vec_push", 3, true),
        (VecOp::Set, "kush_vec_set", 5, true),
        (VecOp::PushBorrowed, "kush_vec_push", 3, true),
        (VecOp::SetBorrowed, "kush_vec_set", 5, true),
        (VecOp::ReserveBorrowed, "kush_vec_reserve", 3, true),
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
    // Every checked host operation takes its source arguments plus one out
    // pointer and returns zero or a positive errno.
    let host_symbols = [
        HostOp::FsRead,
        HostOp::FsWrite,
        HostOp::FsWriteExclusive,
        HostOp::FsAppend,
        HostOp::FsRemove,
        HostOp::FsRename,
        HostOp::FsMkdir,
        HostOp::FsRemoveDir,
        HostOp::FsList,
        HostOp::FsIsFile,
        HostOp::FsIsDir,
        HostOp::FsSize,
        HostOp::FsExists,
        HostOp::FsOpen,
        HostOp::FsReadAt,
        HostOp::FsWriteAt,
        HostOp::FsSync,
        HostOp::FsTruncate,
        HostOp::FsFileSize,
        HostOp::FsClose,
        HostOp::FsSyncDir,
        HostOp::EnvArgCount,
        HostOp::EnvArg,
        HostOp::EnvVarCount,
        HostOp::EnvVar,
        HostOp::TimeUnixSeconds,
        HostOp::TimeMonotonicNs,
        HostOp::TimeSleepMs,
        HostOp::ProcRun,
        HostOp::NetTcpExchange,
        HostOp::OsStrerror,
    ];
    let mut host_ops = BTreeMap::new();
    for op in host_symbols {
        let mut sig = module.make_signature();
        sig.params
            .extend((0..=op.arity()).map(|_| AbiParam::new(I64)));
        sig.returns.push(AbiParam::new(I64));
        host_ops.insert(
            op,
            module
                .declare_function(op.symbol(), Linkage::Import, &sig)
                .map_err(error)?,
        );
    }
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
        .extend((0..4).map(|_| AbiParam::new(I64)));
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
    let mut handler_redirect_sig = module.make_signature();
    handler_redirect_sig.params.push(AbiParam::new(I64));
    handler_redirect_sig.returns.push(AbiParam::new(I64));
    let handler_redirect = module
        .declare_function(
            "kush_handler_redirect",
            Linkage::Import,
            &handler_redirect_sig,
        )
        .map_err(error)?;
    let abort_word = module
        .declare_data("kush_abort_word", Linkage::Import, true, false)
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
        (buffer_free, bytes_free),
        arena_release,
        arena_box_release,
        &alloc_ops,
    )?;
    let context_drops = synthesize_context_drops(&mut module, program, &drops, free)?;
    let task_types = collect_task_types(program);
    let (task_wrappers, task_pointer_drops) =
        synthesize_task_wrappers(&mut module, program, &task_types, &drops)?;
    let mut ids = Vec::new();
    let mut foreign_ids = Vec::new();
    for (index, f) in program.functions.iter().enumerate() {
        if let Some(Some(foreign)) = program.foreign_functions.get(index) {
            let sig = foreign_abi_signature(&mut module, program, foreign);
            let id = module
                .declare_function(&foreign.symbol, Linkage::Import, &sig)
                .map_err(error)?;
            ids.push(id);
            foreign_ids.push(Some(id));
            continue;
        }
        foreign_ids.push(None);
        let mut sig = module.make_signature();
        let mut exclusive_params = Vec::new();
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
        for position in captures..f.parameters {
            let slot = position;
            let local = &f.locals[f
                .parameter_slots
                .as_ref()
                .map_or(position, |slots| slots[position])];
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
            // The first word of an owning handle or exclusive borrow is a
            // pointer nothing else may use while the callee runs.
            let exclusive = matches!(
                local.ty,
                Type::Box(_)
                    | Type::RefMut(_)
                    | Type::Vec(_)
                    | Type::Bytes
                    | Type::String
                    | Type::SliceMut(_)
                    | Type::StrMut
            );
            for word in 0..program.width(local.ty) {
                if exclusive && word == 0 {
                    exclusive_params.push(sig.params.len());
                }
                sig.params.push(AbiParam::new(I64));
            }
        }
        let name = if index == entry {
            "kush_entry".to_owned()
        } else {
            format!("kush_fn_{index}")
        };
        let id = module
            .declare_function(
                &name,
                if index == entry {
                    Linkage::Export
                } else {
                    Linkage::Local
                },
                &sig,
            )
            .map_err(error)?;
        if let Some(llvm) = &mut module.llvm {
            llvm.exclusive_parameters(&name, exclusive_params);
        }
        ids.push(id);
    }
    // Lower only what the program can reach. Every reference to a function,
    // whether a call, a function value or a closure, goes through a
    // declaration in the referring body, and `CodeModule` records those as
    // bodies are defined; so the set grows from the entry point and from the
    // glue synthesized above until nothing new turns up. Library functions
    // the program never uses are neither lowered nor compiled.
    let index_of: BTreeMap<FuncId, usize> = ids
        .iter()
        .enumerate()
        .map(|(index, id)| (*id, index))
        .collect();
    let mut lowered = vec![false; program.functions.len()];
    let mut pending = vec![entry];
    loop {
        for id in std::mem::take(&mut module.referenced) {
            if let Some(index) = index_of.get(&id)
                && !lowered[*index]
            {
                pending.push(*index);
            }
        }
        let Some(index) = pending.pop() else {
            break;
        };
        if std::mem::replace(&mut lowered[index], true) {
            continue;
        }
        let f = &program.functions[index];
        if program
            .foreign_functions
            .get(index)
            .is_some_and(Option::is_some)
        {
            // The C import was declared above; there is no Kush body to define.
            continue;
        }
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
            foreign_ids: &foreign_ids,
            program,
            codegen,
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
            context_drops: &context_drops,
            tracked: vec![],
            function_index: index,
            deferred: None,
            checked_fuel: None,
            bytes_from,
            read_all,
            read_line,
            read_chunk,
            write,
            host_ops: &host_ops,
            bytes_ops: &bytes_ops,
            string_validate,
            string_scalar_len,
            string_scalar_at,
            str_scalar_len,
            str_byte_at,
            str_scalar_at,
            str_to_string,
            str_writes: [str_ascii_upper, str_ascii_lower, str_set_scalar],
            vec_ops: &vec_ops,
            vec_element,
            literal_data: &literal_data,
            abort_word,
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
            handler_redirect,
            handler_base: None,
            task_wrappers: &task_wrappers,
            task_pointer_drops: &task_pointer_drops,
            loops: Vec::new(),
            regions: Vec::new(),
            aborts: Vec::new(),
            slice_layouts: BTreeMap::new(),
            upper_bounds: Vec::new(),
            vec_shadows: BTreeMap::new(),
            pending_pushes: Vec::new(),
            push_shadow: None,
        };
        let entry = g.builder.create_block();
        g.builder.append_block_params_for_function_params(entry);
        g.builder.switch_to_block(entry);
        if block_installs_handler(&f.body) {
            let handler_base = g.builder.declare_var(I64);
            g.handler_base = Some(handler_base);
            let base = g.runtime_call(g.handler_depth, &[]);
            g.builder.def_var(handler_base, base);
        }
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
            if array || record || object || owner_handle || local.pinned {
                let width = program.width(local.ty);
                let slot = g.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (width * 8) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
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
                for position in 0..captures {
                    let i = f
                        .parameter_slots
                        .as_ref()
                        .map_or(position, |slots| slots[position]);
                    let width = g.variables[i].len();
                    if f.capture_refs.get(position).copied().unwrap_or(false) {
                        // The environment stores the caller's stack address.
                        // Reads and writes of this capture go through it.
                        let pointer = g.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            environment,
                            capture_offset,
                        );
                        g.locations[i] = Some(pointer);
                        let zero = g.constant(0);
                        for variable in &g.variables[i] {
                            g.builder.def_var(*variable, zero);
                        }
                        capture_offset += 8;
                        g.activate_local(i);
                        continue;
                    }
                    let values = g.load_words(environment, capture_offset, width);
                    capture_offset += (width * 8) as i32;
                    g.assign(i, &values);
                    g.activate_local(i);
                }
                emit_drop(&mut g.builder, g.module, free, &[environment]);
            }
        }
        for position in captures..f.parameters {
            let i = f
                .parameter_slots
                .as_ref()
                .map_or(position, |slots| slots[position]);
            if f.parameter_grades
                .get(position)
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
    // An object file must define every local symbol it declares, so the
    // functions that were not reached get a body that only traps. (The LLVM
    // module simply omits them.)
    if module.llvm.is_none() {
        for (index, id) in ids.iter().enumerate() {
            // Imports have no body here whether or not they are reached.
            if lowered[index] || foreign_ids[index].is_some() {
                continue;
            }
            let mut context = module.make_context();
            context.func.signature = module
                .declarations()
                .get_function_decl(*id)
                .signature
                .clone();
            let mut function_context = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut context.func, &mut function_context);
            let block = builder.create_block();
            builder.append_block_params_for_function_params(block);
            builder.switch_to_block(block);
            builder.ins().trap(TrapCode::unwrap_user(2));
            builder.seal_all_blocks();
            builder.finalize(module.target_config());
            module.define_function(*id, &mut context).map_err(error)?;
        }
    }
    if let Some(failure) = module.failure {
        return Err(failure);
    }
    match module.llvm {
        Some(llvm) => Ok(Lowered::Llvm(llvm.finish(module.object.declarations())?)),
        None => Ok(Lowered::Object(
            module.object.finish().emit().map_err(error)?,
        )),
    }
}
fn aggregate_result(program: &Executable, ty: Type) -> bool {
    ty.layout().is_some() || program.width(ty) > 1
}
/// Exact C ABI scalar type for a supported bridge value. Narrow integers use
/// their real width so `cc`/C and Cranelift agree; the backend canonicalizes
/// them back to a checked Kush word at the call boundary.
fn abi_value_type(ty: Type) -> ir::Type {
    match ty {
        Type::Bool => ir::types::I32,
        Type::I64 => I64,
        Type::Int(kind) => match kind {
            IntKind::I8 => ir::types::I8,
            IntKind::I16 => ir::types::I16,
            IntKind::I32 => ir::types::I32,
            IntKind::I64 => I64,
            IntKind::U8 => ir::types::I8,
            IntKind::U16 => ir::types::I16,
            IntKind::U32 => ir::types::I32,
            IntKind::U64 => I64,
        },
        Type::Float(kind) => match kind {
            FloatKind::F32 => ir::types::F32,
            FloatKind::F64 => ir::types::F64,
        },
        // Foreign resources are opaque `void *` handles. Every other admitted
        // type is rejected by the checker before reaching the backend.
        Type::Enum(_) => I64,
        _ => I64,
    }
}
/// C ABI signature of one checked foreign import. Slices and `&str` become
/// `(const uint8_t *, int64_t)`. A fallible result becomes
/// `int64_t symbol(..., T *out)`: zero status means success and the out slot
/// holds `T`; any non-zero status is the checked `Err(i64)`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PointeeKind {
    Buffer,
    Resource,
}
/// References admitted at the foreign boundary are either buffer handles
/// (`&Bytes`/`&String`/`&mut Bytes`) or opaque resource handles. The backend
/// needs the distinction to know whether to pass `(pointer, length)` or one
/// handle word.
fn foreign_pointee_kind(program: &Executable, pointer: usize) -> PointeeKind {
    match program.pointees[pointer] {
        Type::Bytes | Type::String => PointeeKind::Buffer,
        _ => PointeeKind::Resource,
    }
}
fn foreign_abi_signature(
    module: &mut CodeModule,
    program: &Executable,
    foreign: &ex::ForeignFunction,
) -> ir::Signature {
    let mut sig = module.make_signature();
    for ty in &foreign.parameters {
        match ty {
            Type::Str => {
                sig.params.push(AbiParam::new(I64));
                sig.params.push(AbiParam::new(I64));
            }
            Type::Ref(pointer) | Type::RefMut(pointer)
                if matches!(foreign_pointee_kind(program, *pointer), PointeeKind::Buffer) =>
            {
                sig.params.push(AbiParam::new(I64));
                sig.params.push(AbiParam::new(I64));
            }
            // The C ABI on x86-64 lets a callee assume that an argument
            // narrower than 32 bits arrives extended to 32; say how, so both
            // backends pass the canonical value and not a raw register.
            Type::Int(IntKind::I8 | IntKind::I16) => {
                sig.params.push(AbiParam::new(abi_value_type(*ty)).sext())
            }
            Type::Int(IntKind::U8 | IntKind::U16) => {
                sig.params.push(AbiParam::new(abi_value_type(*ty)).uext())
            }
            _ => sig.params.push(AbiParam::new(abi_value_type(*ty))),
        }
    }
    match foreign.fallible {
        Some(shape) => {
            sig.returns.push(AbiParam::new(I64));
            if shape.ok != Type::Unit {
                sig.params.push(AbiParam::new(I64));
            }
        }
        None if foreign.result == Type::Unit => {}
        None => sig
            .returns
            .push(AbiParam::new(abi_value_type(foreign.result))),
    }
    sig
}
fn collect_literals<'a>(block: &'a ex::Block, out: &mut Vec<(usize, &'a [u8])>) {
    for statement in &block.statements {
        match statement {
            ex::Statement::Let(_, value) | ex::Statement::Expr(value) => {
                collect_expr_literals(value, out)
            }
            ex::Statement::Declare(_) => {}
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
    module: &mut CodeModule,
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
                ex::Statement::Declare(_) => {}
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
    context_new: FuncId,
    context_share: FuncId,
    context_release: FuncId,
    block_data: FuncId,
    box_create: FuncId,
    box_payload: FuncId,
    box_release: FuncId,
    vec_create: FuncId,
    vec_push: FuncId,
    vec_try_push: FuncId,
    vec_pop: FuncId,
    vec_len: FuncId,
    vec_get: FuncId,
    vec_set: FuncId,
    vec_clear: FuncId,
    vec_data: FuncId,
    vec_release: FuncId,
}
type DropTables = (BTreeMap<Type, FuncId>, BTreeMap<Vec<Type>, FuncId>);
/// One drop thunk per allocator-context shape. The thunk receives the state
/// block address, runs the concrete instance's checked drop glue (if any), and
/// releases the block. It is called only when the final context reference goes
/// away, after every container block has been released.
fn synthesize_context_drops(
    module: &mut CodeModule,
    program: &Executable,
    drops: &BTreeMap<Type, FuncId>,
    free: FuncId,
) -> Result<Vec<FuncId>> {
    let mut ids = Vec::new();
    for (index, spec) in program.allocator_contexts.iter().enumerate() {
        let mut signature = module.make_signature();
        signature.params.push(AbiParam::new(I64));
        ids.push(
            module
                .declare_function(
                    &format!("kush_context_drop_{index}"),
                    Linkage::Local,
                    &signature,
                )
                .map_err(error)?,
        );
        let _ = spec;
    }
    for (index, spec) in program.allocator_contexts.iter().enumerate() {
        let id = ids[index];
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
        let state = builder.block_params(entry)[0];
        if program.owns(spec.state) {
            let words = (0..program.width(spec.state))
                .map(|word| {
                    builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), state, (word * 8) as i32)
                })
                .collect::<Vec<_>>();
            emit_drop(&mut builder, module, drops[&spec.state.full()], &words);
        }
        emit_drop(&mut builder, module, free, &[state]);
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize(module.target_config());
        module.define_function(id, &mut context).map_err(error)?;
    }
    Ok(ids)
}
fn synthesize_drops(
    module: &mut CodeModule,
    program: &Executable,
    free: FuncId,
    buffer_frees: (FuncId, FuncId),
    arena_release: FuncId,
    arena_box_release: FuncId,
    alloc_ops: &AllocOps,
) -> Result<DropTables> {
    let (buffer_free, bytes_free) = buffer_frees;
    let mut types = (0..program.pointees.len())
        .map(Type::Box)
        .chain((0..program.pointees.len()).map(Type::ArenaBox))
        .chain((0..program.pointees.len()).map(Type::AllocBox))
        .chain((0..program.pointees.len()).map(Type::AllocVec))
        .chain((0..program.pointees.len()).map(Type::Vec))
        .chain((0..program.pointees.len()).map(Type::Task))
        .chain([Type::Arena, Type::AllocatorContext])
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
                emit_drop(&mut builder, module, bytes_free, &args);
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
            Type::AllocatorContext => {
                emit_drop(&mut builder, module, alloc_ops.context_release, &args);
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
                                (16 + k * 8) as i32,
                            )
                        })
                        .collect::<Vec<_>>();
                    emit_drop(&mut builder, module, ids[&element.full()], &fields);
                    let next = builder.ins().iadd_imm_s(i, 1);
                    builder.ins().jump(head, &[next.into()]);
                    builder.switch_to_block(done);
                }
                emit_drop(&mut builder, module, buffer_free, &args);
                builder.ins().return_(&[]);
            }
            Type::Enum(index) => {
                if let Some(foreign) = program.enums[index].foreign.clone() {
                    // The one-word handle is released by the trusted foreign
                    // contract exactly once. Linear foreign resources cannot be
                    // implicitly dropped, so this path only runs for affine
                    // resources (or when a linear value is explicitly consumed
                    // by a compiled drop after a checked transfer).
                    let mut signature = module.make_signature();
                    signature.params.push(AbiParam::new(I64));
                    let release = module
                        .declare_function(&foreign.release, Linkage::Import, &signature)
                        .map_err(error)?;
                    emit_drop(&mut builder, module, release, &[args[0]]);
                    builder.ins().return_(&[]);
                } else if let Some((element, capacity)) = program.enums[index].dynamic_array {
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
                        let condition = if let Some(niche) = program.enums[index].niche() {
                            let (cc, constant) = decoder_test(niche.decoder(tag));
                            builder.ins().icmp_imm_s(cc, args[0], constant)
                        } else if program.enums[index].tag_words() == 0 {
                            builder.ins().iconst(ir::types::I8, 1)
                        } else {
                            builder.ins().icmp_imm_s(IntCC::Equal, args[0], tag as i64)
                        };
                        builder.ins().brif(condition, hit, &[], next, &[]);
                        builder.switch_to_block(hit);
                        let mut offset = program.enums[index].tag_words();
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
        if let ExprKind::TaskSpawn { body, .. } = &node.kind
            && let Type::Once(id) = body.ty
        {
            out.push(id);
        }
        node.for_each_child(&mut |child| walk(child, out));
    }
    let mut ids = Vec::new();
    for function in &program.functions {
        for statement in &function.body.statements {
            match statement {
                ex::Statement::Let(_, value) | ex::Statement::Expr(value) => walk(value, &mut ids),
                ex::Statement::Declare(_) => {}
            }
        }
        if let Some(tail) = &function.body.tail {
            walk(tail, &mut ids);
        }
    }
    ids.sort_unstable();
    ids.dedup();
    ids
}
/// Build the native task entry wrappers. A wrapper always has the C ABI
/// `(code, env, result_ptr) -> ()`, so the runtime can call a statically or
/// dynamically selected once callable without knowing its signature.
fn synthesize_task_wrappers(
    module: &mut CodeModule,
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
#[derive(Debug)]
enum ScalarCallback {
    Input,
    Constant(i64),
    Bitwise(Kind, Box<Self>, Box<Self>),
}
impl ScalarCallback {
    fn expression(expr: &Expr, budget: &mut usize) -> Option<Self> {
        if *budget == 0 || expr.ty != Type::I64 || expr.resource.is_some() {
            return None;
        }
        *budget -= 1;
        match &expr.kind {
            ExprKind::Local(0) | ExprKind::Peek(0) => Some(Self::Input),
            ExprKind::Constant(value) => Some(Self::Constant(*value)),
            ExprKind::Binary(op @ (Kind::Amp | Kind::Pipe | Kind::Caret), left, right) => {
                Some(Self::Bitwise(
                    op.clone(),
                    Box::new(Self::expression(left, budget)?),
                    Box::new(Self::expression(right, budget)?),
                ))
            }
            _ => None,
        }
    }
    fn callback(program: &Executable, callback: &Expr) -> Option<Self> {
        let ExprKind::FnValue { function, captures } = &callback.kind else {
            return None;
        };
        let Type::Fn(signature) = callback.ty else {
            return None;
        };
        let signature = &program.function_types[signature];
        let function = &program.functions[*function];
        if !captures.is_empty()
            || signature.effects != 0
            || signature.parameters != [Type::I64]
            || signature.result != Type::I64
            || signature.once
            || signature.linear
            || signature.parameter_erased(0)
            || signature.result_erased()
            || function.closure.is_some()
            || function.parameters != 1
            || function.locals.len() != 1
            || function.locals[0].ty != Type::I64
            || function.locals[0].grade.is_some_and(Grade::is_zero)
            || function.result_grade.is_some_and(Grade::is_zero)
            || function.locals[0].pinned
            || function.locals[0].mutable
            || function.result != Type::I64
            || !function.resources.is_empty()
            || !function.body.statements.is_empty()
        {
            return None;
        }
        Self::expression(function.body.tail.as_deref()?, &mut 32)
    }
    fn emit(&self, builder: &mut FunctionBuilder<'_>, input: Value) -> Value {
        match self {
            Self::Input => input,
            Self::Constant(value) => builder.ins().iconst(I64, *value),
            Self::Bitwise(op, left, right) => {
                let left = left.emit(builder, input);
                let right = right.emit(builder, input);
                match op {
                    Kind::Amp => builder.ins().band(left, right),
                    Kind::Pipe => builder.ins().bor(left, right),
                    Kind::Caret => builder.ins().bxor(left, right),
                    _ => unreachable!("validated scalar callback operator"),
                }
            }
        }
    }
}

struct Generator<'a, 'b> {
    builder: FunctionBuilder<'a>,
    module: &'b mut CodeModule,
    ids: &'b [FuncId],
    foreign_ids: &'b [Option<FuncId>],
    program: &'b Executable,
    codegen: CodegenOptions,
    // Runtime-guarded descriptor facts, scoped to one versioned loop.
    slice_layouts: BTreeMap<usize, usize>,
    // Dominating signed `index < length` tests, identified by SSA value.
    upper_bounds: Vec<(Value, Value)>,
    /// Vector locals whose length and capacity a loop keeps in variables:
    /// slot to (length, capacity). See [`Generator::lower_while`].
    vec_shadows: BTreeMap<usize, (Variable, Variable)>,
    /// Push expressions (by address) registered for a shadowed slot, and the
    /// shadow of the push being lowered right now.
    pending_pushes: Vec<(usize, usize)>,
    push_shadow: Option<(Variable, Variable)>,
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
    host_ops: &'b BTreeMap<HostOp, FuncId>,
    bytes_ops: &'b BTreeMap<BytesOp, FuncId>,
    string_validate: FuncId,
    string_scalar_len: FuncId,
    string_scalar_at: FuncId,
    str_scalar_len: FuncId,
    str_byte_at: FuncId,
    str_scalar_at: FuncId,
    str_to_string: FuncId,
    /// `&mut str` writes: ASCII upper case, ASCII lower case, set_scalar.
    str_writes: [FuncId; 3],
    vec_ops: &'b BTreeMap<VecOp, FuncId>,
    vec_element: FuncId,
    /// (continue target, break target, break carries a value, handler depth at
    /// loop entry). Break/continue restore the handler depth so a dynamic
    /// handler frame inside the body cannot survive an early loop exit.
    loops: Vec<(ir::Block, ir::Block, bool, Option<Variable>)>,
    /// (exit join, finish block, handler depth at entry) of each enclosing
    /// lowered suspendable region; `RegionExit` leaves the innermost one.
    regions: Vec<(Option<ir::Block>, Option<ir::Block>, Option<Variable>)>,
    /// Enclosing `AbortScope`s: label, the block receiving the payload, and
    /// the handler-stack depth at entry.
    aborts: Vec<AbortTarget>,
    literal_data: &'b BTreeMap<usize, DataId>,
    /// The runtime's `kush_abort_word`.
    abort_word: DataId,
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
    context_drops: &'b [FuncId],
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
    handler_redirect: FuncId,
    /// Entry handler-stack depth for this function; every return restores it so
    /// an early `return` cannot leave a dynamic handler frame visible.
    handler_base: Option<Variable>,
    task_wrappers: &'b BTreeMap<usize, FuncId>,
    task_pointer_drops: &'b BTreeMap<Type, FuncId>,
    tracked: Vec<Tracked>,
    function_index: usize,
    /// The innermost loop whose overflow panics are deferred to its exit.
    deferred: Option<DeferredLoop>,
    /// Fuel of a chunk of a deferred loop that runs with ordinary checks.
    checked_fuel: Option<Variable>,
}
/// State of one loop lowered with deferred overflow checks; see
/// [`deferred`] for the conditions and the argument that this is unobservable.
struct DeferredLoop {
    plan: deferred::Plan,
    /// Sign bit set once any `Exact` operation has overflowed.
    sticky: Variable,
    /// OR of the magnitude words of each tracked operand.
    leaves: BTreeMap<usize, Variable>,
    /// Iterations left before the loop must stop and report.
    fuel: Variable,
}
/// An enclosing `AbortScope` during code generation.
#[derive(Clone, Copy)]
struct AbortTarget {
    label: usize,
    /// Receives the payload words and runs the handler.
    aborted: ir::Block,
    /// Handler-stack depth before the scope pushed anything.
    depth: Option<Variable>,
    /// Payload buffer of a declared operation's activation; its address is
    /// the activation's abort word.
    buffer: Option<Value>,
    width: usize,
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
    fn abort_target(&self, label: usize) -> AbortTarget {
        *self
            .aborts
            .iter()
            .rev()
            .find(|target| target.label == label)
            .expect("an abort exit is inside its scope")
    }
    fn abort_word_address(&mut self) -> Value {
        let data = self
            .module
            .declare_data_in_func(self.abort_word, self.builder.func);
        self.builder.ins().symbol_value(I64, data)
    }
    /// Leave the function on an abort path: the caller ignores the result.
    fn return_dummy(&mut self) {
        let function = &self.program.functions[self.function_index];
        let width = if function.result_grade.is_some_and(Grade::is_zero) {
            0
        } else {
            self.program.width(function.result)
        };
        let words = (0..width).map(|_| self.constant(0)).collect::<Vec<_>>();
        self.return_value(&words);
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
                g.optional_words(ty, present, &[payload], some, none)
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
    /// Callees restore their own local frames. If this function never installs
    /// a handler, neither its returns nor loop exits can strand a local frame.
    fn capture_handler_depth(&mut self) -> Option<Variable> {
        self.handler_base?;
        let depth = self.builder.declare_var(I64);
        let value = self.runtime_call(self.handler_depth, &[]);
        self.builder.def_var(depth, value);
        Some(depth)
    }
    fn restore_handler_depth(&mut self, depth: Option<Variable>) {
        if let Some(depth) = depth {
            let value = self.builder.use_var(depth);
            self.runtime_void(self.handler_restore, &[value]);
        }
    }
    fn return_value(&mut self, values: &[Value]) {
        self.restore_handler_depth(self.handler_base);
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
    /// Map an owned object's member identifier from `from`'s member table to
    /// `to`'s through a compare-and-select chain. The payload pointer word is
    /// kept, so nothing is allocated, copied, or released.
    fn dyn_upcast(&mut self, from: usize, to: usize, values: &[Value]) -> Words {
        let source = self
            .program
            .dyn_members
            .get(from)
            .cloned()
            .unwrap_or_default();
        let target = self
            .program
            .dyn_members
            .get(to)
            .cloned()
            .unwrap_or_default();
        let mut mapped = self.constant(0);
        for (index, entry) in source.iter().enumerate() {
            let position = target
                .iter()
                .position(|candidate| candidate.member == entry.member)
                .expect("the checker registers every upcast member in the target object");
            let hit = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, values[0], index as i64);
            let value = self.constant(position as i64);
            mapped = self.builder.ins().select(hit, value, mapped);
        }
        vec![mapped, values[1]]
    }
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
                .get(&spec.key)
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
    /// Lower one checked foreign import. `values` is the flattened internal
    /// word list: slice/text parameters occupy their normal four-word
    /// descriptor, from which only `(pointer, length)` reaches the C ABI.
    fn foreign_call(&mut self, index: usize, values: &[Value]) -> Option<Words> {
        let foreign = self.program.foreign_functions[index]
            .as_ref()
            .expect("checked foreign target")
            .clone();
        let id = self.foreign_ids[index].expect("foreign import declared");
        let mut arguments = Vec::new();
        let mut position = 0usize;
        for ty in &foreign.parameters {
            match ty {
                Type::Str => {
                    // `&str` is a four-word checked view; only the contiguous
                    // byte pointer and byte length reach C.
                    arguments.push(values[position]);
                    arguments.push(values[position + 1]);
                    position += 4;
                }
                Type::Ref(pointer) | Type::RefMut(pointer) => {
                    let handle =
                        self.builder
                            .ins()
                            .load(I64, ir::MemFlagsData::new(), values[position], 0);
                    if foreign_pointee_kind(self.program, *pointer) == PointeeKind::Buffer {
                        // KushBytes/KushString: length at +0, capacity at +8,
                        // payload bytes at +16.
                        let data = self.builder.ins().iadd_imm_s(handle, 16);
                        let length = self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            handle,
                            if matches!(ty, Type::RefMut(_)) { 8 } else { 0 },
                        );
                        arguments.push(data);
                        arguments.push(length);
                    } else {
                        arguments.push(handle);
                    }
                    position += 1;
                }
                _ => {
                    let word = values[position];
                    position += 1;
                    match ty {
                        Type::Bool => {
                            arguments.push(self.builder.ins().ireduce(ir::types::I32, word))
                        }
                        Type::Int(kind) if !matches!(kind, IntKind::I64 | IntKind::U64) => {
                            arguments.push(self.builder.ins().ireduce(abi_value_type(*ty), word))
                        }
                        Type::Float(FloatKind::F64) => arguments.push(self.builder.ins().bitcast(
                            ir::types::F64,
                            ir::MemFlagsData::new(),
                            word,
                        )),
                        Type::Float(FloatKind::F32) => {
                            let bits = self.builder.ins().ireduce(ir::types::I32, word);
                            arguments.push(self.builder.ins().bitcast(
                                ir::types::F32,
                                ir::MemFlagsData::new(),
                                bits,
                            ));
                        }
                        _ => arguments.push(word),
                    }
                }
            }
        }
        let mut out = None;
        if let Some(shape) = foreign.fallible
            && shape.ok != Type::Unit
        {
            let width = self.program.width(shape.ok).max(1);
            let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                (width * 8) as u32,
                STACK_SLOT_ALIGN_SHIFT,
            ));
            let pointer = self.builder.ins().stack_addr(I64, slot, 0);
            arguments.push(pointer);
            out = Some((pointer, width));
        }
        let callee = self.module.declare_func_in_func(id, self.builder.func);
        let call = self.builder.ins().call(callee, &arguments);
        let returned = self.builder.inst_results(call).to_vec();
        if let Some(shape) = foreign.fallible {
            let status = returned[0];
            let join = self.join(foreign.result).unwrap();
            let success = self.builder.create_block();
            let failure = self.builder.create_block();
            let ok = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
            self.builder.ins().brif(ok, success, &[], failure, &[]);
            self.builder.switch_to_block(success);
            let mut values = vec![self.constant(shape.ok_tag as i64)];
            if let Some((pointer, width)) = out {
                values.extend(self.load_words(pointer, 0, width));
            }
            while values.len() < self.program.width(foreign.result) {
                values.push(self.constant(0));
            }
            self.jump(join, &values);
            self.builder.switch_to_block(failure);
            let mut values = vec![self.constant(shape.err_tag as i64)];
            if self.program.width(shape.error) == 1 {
                values.push(status);
            }
            while values.len() < self.program.width(foreign.result) {
                values.push(self.constant(0));
            }
            self.jump(join, &values);
            self.builder.switch_to_block(join);
            return Some(self.builder.block_params(join).to_vec());
        }
        if foreign.result == Type::Unit {
            return Some(vec![self.constant(0)]);
        }
        let value = returned[0];
        Some(vec![match foreign.result {
            Type::Float(FloatKind::F64) => {
                self.builder
                    .ins()
                    .bitcast(I64, ir::MemFlagsData::new(), value)
            }
            Type::Float(FloatKind::F32) => {
                let low =
                    self.builder
                        .ins()
                        .bitcast(ir::types::I32, ir::MemFlagsData::new(), value);
                self.builder.ins().uextend(I64, low)
            }
            // A foreign `int32_t` Bool may be any nonzero value; the proof
            // fragment relies on 0 or 1.
            Type::Bool => {
                let truth = self.builder.ins().icmp_imm_s(IntCC::NotEqual, value, 0);
                self.builder.ins().uextend(I64, truth)
            }
            Type::Int(IntKind::I64 | IntKind::U64) => value,
            Type::Int(kind) if kind.signed() => self.builder.ins().sextend(I64, value),
            Type::Int(_) => self.builder.ins().uextend(I64, value),
            _ => value,
        }])
    }
    fn function_call(&mut self, index: usize, mut values: Words) -> Words {
        let function = &self.program.functions[index];
        let result = function.result;
        let erased_result = function.result_grade.is_some_and(Grade::is_zero);
        let pointer = if !erased_result && aggregate_result(self.program, result) {
            let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                ir::StackSlotKind::ExplicitSlot,
                (self.program.width(result) * 8) as u32,
                STACK_SLOT_ALIGN_SHIFT,
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
    /// Emit an indirect call whose physical argument words (return pointer,
    /// environment, and arguments) are already assembled.
    fn finish_indirect_call(
        &mut self,
        id: usize,
        code: Value,
        pointer: Option<Value>,
        values: Vec<Value>,
    ) -> Words {
        let signature = self.program.function_types[id].clone();
        let result = signature.result;
        let result_erased = signature.result_erased();
        let ir_signature = self.indirect_signature(id);
        let ir_signature = self.builder.import_signature(ir_signature);
        let call = self
            .builder
            .ins()
            .call_indirect(ir_signature, code, &values);
        if result_erased {
            return vec![self.constant(0)];
        }
        if let Some(pointer) = pointer {
            return (0..self.program.width(result))
                .map(|i| {
                    self.builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), pointer, (i * 8) as i32)
                })
                .collect();
        }
        self.builder.inst_results(call).to_vec()
    }
    fn indirect_signature(&self, id: usize) -> ir::Signature {
        let once = self.program.function_types[id].once;
        self.indirect_signature_mode(id, once)
    }
    /// Build the indirect call ABI for a callable signature, overriding whether
    /// the environment word is part of the call. A dynamic handler frame picks
    /// the copyable `fn` shape or the owning `once` shape at run time.
    fn indirect_signature_mode(&self, id: usize, once: bool) -> ir::Signature {
        let signature = &self.program.function_types[id];
        let mut result = self.module.make_signature();
        let aggregate =
            !signature.result_erased() && aggregate_result(self.program, signature.result);
        if aggregate {
            result.params.push(AbiParam::new(I64));
        }
        if once {
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
    /// Trap when a runtime index is negative or outside `0..length`.
    fn check_index(&mut self, index: Value, length: i64) {
        let limit = self.constant(length);
        let negative = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, index, 0);
        let beyond = self
            .builder
            .ins()
            .icmp(IntCC::SignedGreaterThanOrEqual, index, limit);
        let invalid = self.builder.ins().bor(negative, beyond);
        self.guard(invalid);
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
                ex::Statement::Declare(slot) => {
                    // Backing storage for a temporary owner. The initializer
                    // runs at its source position; cleanup is guarded by the
                    // resource's activation flag.
                    slots.push(*slot);
                }
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
                    let capture_refs = self.program.functions[*function].capture_refs.clone();
                    let mut offset = 8;
                    for (index, capture) in captures.iter().enumerate() {
                        if capture_refs.get(index).copied().unwrap_or(false) {
                            let slot = match &capture.kind {
                                ExprKind::Local(slot)
                                | ExprKind::Peek(slot)
                                | ExprKind::Move(slot) => *slot,
                                _ => unreachable!("checked by-reference scalar capture"),
                            };
                            let pointer = self.local_address(slot);
                            self.builder.ins().store(
                                ir::MemFlagsData::new(),
                                pointer,
                                environment,
                                offset as i32,
                            );
                            self.consume(capture);
                            offset += 8;
                            continue;
                        }
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
                        STACK_SLOT_ALIGN_SHIFT,
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
                return Some(self.finish_indirect_call(id, callable[0], pointer, values));
            }
            ExprKind::Region { body, finish, .. } => {
                let exit = self.join(expr.ty);
                // The finish block receives the finish callable's argument:
                // the body value on completion, or a returned value from a
                // `RegionExit`/`TryExit`, even when the body itself never
                // completes (type Never).
                let finish_block = match finish {
                    Some(finish) => {
                        let input = match finish.ty {
                            Type::Fn(id) | Type::Once(id) => {
                                self.program.function_types[id].parameters[0]
                            }
                            _ => unreachable!("checked region finish callable"),
                        };
                        let block = self.builder.create_block();
                        for _ in 0..self.program.width(input) {
                            self.builder.append_block_param(block, I64);
                        }
                        Some(block)
                    }
                    None => None,
                };
                let depth = self.capture_handler_depth();
                self.regions.push((exit, finish_block, depth));
                let finished = self.block(body);
                self.regions.pop();
                if let Some(values) = finished {
                    match (finish_block, exit) {
                        (Some(block), _) => self.jump(block, &values),
                        (None, Some(exit)) => self.jump(exit, &values),
                        (None, None) => unreachable!("a completing region has a value"),
                    }
                }
                if let (Some(block), Some(finish)) = (finish_block, finish) {
                    self.builder.switch_to_block(block);
                    let arguments = self.builder.block_params(block).to_vec();
                    if let Some(callable) = self.expr(finish) {
                        self.consume(finish);
                        let Some((id, once)) = (match finish.ty {
                            Type::Fn(id) => Some((id, false)),
                            Type::Once(id) => Some((id, true)),
                            _ => None,
                        }) else {
                            unreachable!("checked region finish callable")
                        };
                        let result = self.program.function_types[id].result;
                        let pointer = aggregate_result(self.program, result).then(|| {
                            let slot =
                                self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                                    ir::StackSlotKind::ExplicitSlot,
                                    (self.program.width(result) * 8) as u32,
                                    STACK_SLOT_ALIGN_SHIFT,
                                ));
                            self.builder.ins().stack_addr(I64, slot, 0)
                        });
                        let mut values = Vec::new();
                        if let Some(pointer) = pointer {
                            values.push(pointer);
                        }
                        if once {
                            values.push(callable[1]);
                        }
                        values.extend(arguments);
                        let words = self.finish_indirect_call(id, callable[0], pointer, values);
                        match exit {
                            Some(exit) => self.jump(exit, &words),
                            None => {
                                self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                            }
                        }
                    }
                }
                let exit = exit?;
                self.builder.switch_to_block(exit);
                return Some(self.builder.block_params(exit).to_vec());
            }
            ExprKind::AbortScope {
                label,
                body,
                handler,
                operation,
            } => {
                let exit = self.join(expr.ty);
                let Some((id, once)) = (match handler.ty {
                    Type::Fn(id) => Some((id, false)),
                    Type::Once(id) => Some((id, true)),
                    _ => None,
                }) else {
                    unreachable!("checked abortive handler callable")
                };
                let payload = self.program.function_types[id].parameters[0];
                let aborted = self.builder.create_block();
                for _ in 0..self.program.width(payload) {
                    self.builder.append_block_param(aborted, I64);
                }
                let depth = self.capture_handler_depth();
                let width = self.program.width(payload);
                let buffer = operation.map(|operation| {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (width.max(1) * 8) as u32,
                        STACK_SLOT_ALIGN_SHIFT,
                    ));
                    let buffer = self.builder.ins().stack_addr(I64, slot, 0);
                    let op = self.constant(operation as i64);
                    let zero = self.constant(0);
                    self.runtime_void(self.handler_push, &[op, buffer, zero, zero]);
                    buffer
                });
                self.aborts.push(AbortTarget {
                    label: *label,
                    aborted,
                    depth,
                    buffer,
                    width,
                });
                let finished = self.block(body);
                self.aborts.pop();
                if let (Some(values), Some(exit)) = (finished, exit) {
                    if buffer.is_some() {
                        self.runtime_void(self.handler_pop, &[]);
                    }
                    self.jump(exit, &values);
                }
                self.builder.switch_to_block(aborted);
                let arguments = self.builder.block_params(aborted).to_vec();
                if let Some(callable) = self.expr(handler) {
                    self.consume(handler);
                    let result = self.program.function_types[id].result;
                    let pointer = aggregate_result(self.program, result).then(|| {
                        let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                            ir::StackSlotKind::ExplicitSlot,
                            (self.program.width(result) * 8) as u32,
                            STACK_SLOT_ALIGN_SHIFT,
                        ));
                        self.builder.ins().stack_addr(I64, slot, 0)
                    });
                    let mut values = Vec::new();
                    if let Some(pointer) = pointer {
                        values.push(pointer);
                    }
                    if once {
                        values.push(callable[1]);
                    }
                    values.extend(arguments);
                    let words = self.finish_indirect_call(id, callable[0], pointer, values);
                    match exit {
                        Some(exit) => self.jump(exit, &words),
                        None => {
                            self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                        }
                    }
                }
                let exit = exit?;
                self.builder.switch_to_block(exit);
                return Some(self.builder.block_params(exit).to_vec());
            }
            ExprKind::AbortExit {
                label,
                value,
                cleanup,
                ..
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                let target = self.abort_target(*label);
                self.restore_handler_depth(target.depth);
                self.jump(target.aborted, &values);
                return None;
            }
            ExprKind::AbortPerform { operation, value } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                let out = self.stack_words(3);
                let op = self.constant(*operation as i64);
                let found = self.runtime_call(self.handler_lookup, &[op, out]);
                let missing = self.builder.ins().icmp_imm_s(IntCC::Equal, found, 0);
                self.guard(missing);
                let buffer = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 0);
                for (index, word) in values.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        buffer,
                        (index * 8) as i32,
                    );
                }
                let word = self.abort_word_address();
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), buffer, word, 0);
                self.cleanup_all();
                self.return_dummy();
                return None;
            }
            ExprKind::AbortCall {
                call,
                exits,
                propagates,
            } => {
                let values = lower!(self.expr(call));
                let address = self.abort_word_address();
                let word = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), address, 0);
                let dispatch = self.builder.create_block();
                let normal = self.builder.create_block();
                self.builder.ins().brif(word, dispatch, &[], normal, &[]);
                self.builder.switch_to_block(dispatch);
                // The call's result words are meaningless on this path.
                self.consume(call);
                for (label, cleanup) in exits {
                    let target = self.abort_target(*label);
                    let Some(buffer) = target.buffer else {
                        continue;
                    };
                    let hit = self.builder.create_block();
                    let miss = self.builder.create_block();
                    let same = self.builder.ins().icmp(IntCC::Equal, word, buffer);
                    self.builder.ins().brif(same, hit, &[], miss, &[]);
                    self.builder.switch_to_block(hit);
                    let zero = self.constant(0);
                    let address = self.abort_word_address();
                    self.builder
                        .ins()
                        .store(ir::MemFlagsData::new(), zero, address, 0);
                    for id in cleanup {
                        self.cleanup(Some(*id));
                    }
                    self.restore_handler_depth(target.depth);
                    let payload = self.load_words(buffer, 0, target.width);
                    self.jump(target.aborted, &payload);
                    self.builder.switch_to_block(miss);
                }
                if *propagates {
                    self.cleanup_all();
                    self.return_dummy();
                } else {
                    self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                }
                self.builder.switch_to_block(normal);
                return Some(values);
            }
            ExprKind::RegionExit {
                value,
                finish,
                cleanup,
            } => {
                let values = lower!(self.expr(value));
                self.consume(value);
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                let (exit, finish_block, depth) = *self.regions.last().unwrap();
                self.restore_handler_depth(depth);
                let target = if *finish { finish_block } else { exit };
                match target {
                    Some(target) => self.jump(target, &values),
                    None => {
                        self.builder.ins().trap(ir::TrapCode::user(1).unwrap());
                    }
                }
                return None;
            }
            ExprKind::TryExit {
                value,
                input,
                output,
                cleanup,
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
                let (_, finish_block, depth) = *self.regions.last().unwrap();
                let finish_block = finish_block.expect("a resumable entry region has a finish");
                let width = self.builder.block_params(finish_block).len();
                let mut error = vec![self.constant(output.err_tag as i64)];
                error.extend_from_slice(&values[1..1 + self.program.width(input.error)]);
                while error.len() < width {
                    error.push(self.constant(0));
                }
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                self.restore_handler_depth(depth);
                self.jump(finish_block, &error);
                self.builder.switch_to_block(success);
                return Some(values[1..1 + self.program.width(input.ok)].to_vec());
            }
            ExprKind::HandlerDepth => self.runtime_call(self.handler_depth, &[]),
            ExprKind::HandlerRedirect { depth, body } => {
                let target = lower!(self.scalar(depth));
                let before = self.runtime_call(self.handler_redirect, &[target]);
                let values = self.block(body)?;
                self.runtime_void(self.handler_restore, &[before]);
                return Some(values);
            }
            ExprKind::Suspendable(_) | ExprKind::Suspend { .. } => {
                unreachable!("suspendable bodies are lowered before code generation")
            }
            ExprKind::HandlerPush {
                operation,
                handler,
                body,
            } => {
                let values = lower!(self.expr(handler));
                let code = values[0];
                let (environment, once) = if matches!(handler.ty, Type::Once(_)) {
                    let environment = values.get(1).copied().unwrap_or_else(|| self.constant(0));
                    (environment, self.constant(1))
                } else {
                    (self.constant(0), self.constant(0))
                };
                self.consume(handler);
                let op = self.constant(*operation as i64);
                self.runtime_void(self.handler_push, &[op, code, environment, once]);
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
                let out = self.stack_words(3);
                let op = self.constant(*operation as i64);
                let found = self.runtime_call(self.handler_lookup, &[op, out]);
                let missing = self.builder.ins().icmp_imm_s(IntCC::Equal, found, 0);
                self.guard(missing);
                let code = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 0);
                let environment = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 8);
                let once = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), out, 16);
                let signature = self.program.function_types[*handler].clone();
                let result = signature.result;
                let pointer = if aggregate_result(self.program, result) {
                    let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                        ir::StackSlotKind::ExplicitSlot,
                        (self.program.width(result) * 8) as u32,
                        STACK_SLOT_ALIGN_SHIFT,
                    ));
                    Some(self.builder.ins().stack_addr(I64, slot, 0))
                } else {
                    None
                };
                // A dynamic frame may hold either a copyable noncapturing `fn`
                // (no environment word in its ABI) or an owning `once` handler
                // (an environment word). The runtime frame records which, so
                // generate both checked call shapes and select at run time.
                let once_block = self.builder.create_block();
                let fn_block = self.builder.create_block();
                let Some(join) = self.join(result) else {
                    unreachable!("a declared effect result is never Never")
                };
                self.builder
                    .ins()
                    .brif(once, once_block, &[], fn_block, &[]);
                for (call_once, block) in [(false, fn_block), (true, once_block)] {
                    self.builder.switch_to_block(block);
                    let mut values = Vec::new();
                    if let Some(pointer) = pointer {
                        values.push(pointer);
                    }
                    if call_once {
                        values.push(environment);
                    }
                    values.extend(payload_values.iter().copied());
                    values.extend(resume_values.iter().copied());
                    let signature = self.indirect_signature_mode(*handler, call_once);
                    let signature = self.builder.import_signature(signature);
                    let call = self.builder.ins().call_indirect(signature, code, &values);
                    let results = match pointer {
                        Some(pointer) => (0..self.program.width(result))
                            .map(|i| {
                                self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    pointer,
                                    (i * 8) as i32,
                                )
                            })
                            .collect::<Vec<_>>(),
                        None => self.builder.inst_results(call).to_vec(),
                    };
                    self.jump(join, &results);
                }
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
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
            ExprKind::Borrow(slot) => return Some(self.borrow_local_value(*slot)),
            ExprKind::InitOwner { slot, value: init } => {
                let values = lower!(self.expr(init));
                self.consume(init);
                self.store_initialized_owner(*slot, &values);
                return Some(self.local_words(*slot));
            }
            ExprKind::BorrowInit { slot, value: init } => {
                let values = lower!(self.expr(init));
                self.consume(init);
                self.store_initialized_owner(*slot, &values);
                return Some(self.borrow_local_value(*slot));
            }
            ExprKind::BorrowPlace(place) => {
                return Some(vec![lower!(self.place_address(place))]);
            }
            ExprKind::PlaceIndex { .. } => {
                unreachable!("a checked place index appears only inside a borrow")
            }
            ExprKind::DerefWrite(reference, replacement) => {
                let pointer = lower!(self.scalar(reference));
                let value = lower!(self.expr(replacement));
                let pointer_ty = reference
                    .ty
                    .ref_pointee()
                    .expect("checked dereference write");
                let pointee = self.program.pointees[pointer_ty];
                if self.program.owns(pointee) {
                    let width = self.program.width(pointee);
                    let old = self.load_words(pointer, 0, width);
                    self.drop_value(pointee, &old);
                }
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
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                let allocator = lower!(self.expr(alloc));
                let release = lower!(self.expr(free));
                let grow = match realloc {
                    Some(realloc) => {
                        let realloc = lower!(self.expr(realloc));
                        realloc[0]
                    }
                    None => self.constant(0),
                };
                return Some(vec![allocator[0], release[0], grow]);
            }
            ExprKind::AllocatorContextNew { value, spec } => {
                let spec_index =
                    (*spec < self.program.allocator_contexts.len()).then_some(*spec)?;
                let checked = self.program.allocator_contexts[spec_index];
                let instance = lower!(self.expr(value));
                self.consume(value);
                let state_bytes =
                    self.constant((self.program.width(checked.state).max(1) * 8) as i64);
                let state = self.runtime_call(self.allocate, &[state_bytes]);
                for (index, word) in instance.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        state,
                        (index * 8) as i32,
                    );
                }
                let drop = self
                    .module
                    .declare_func_in_func(self.context_drops[spec_index], self.builder.func);
                let drop = self.builder.ins().func_addr(I64, drop);
                let alloc = self
                    .module
                    .declare_func_in_func(self.ids[checked.alloc], self.builder.func);
                let alloc = self.builder.ins().func_addr(I64, alloc);
                let release = self
                    .module
                    .declare_func_in_func(self.ids[checked.free], self.builder.func);
                let release = self.builder.ins().func_addr(I64, release);
                let grow = self
                    .module
                    .declare_func_in_func(self.ids[checked.grow], self.builder.func);
                let grow = self.builder.ins().func_addr(I64, grow);
                let context = self.runtime_call(
                    self.alloc_ops.context_new,
                    &[state, drop, alloc, release, grow],
                );
                return Some(vec![context]);
            }
            ExprKind::AllocatorContextShare(argument) => {
                let reference = lower!(self.scalar(argument));
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), reference, 0);
                let shared = self.runtime_call(self.alloc_ops.context_share, &[handle]);
                return Some(vec![shared]);
            }
            ExprKind::AllocBoxNew { allocator, value } => {
                let pair = self.allocator_words(allocator)?;
                let payload = lower!(self.expr(value));
                self.consume(allocator);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                self.consume(value);
                let block =
                    self.runtime_call(self.alloc_ops.block, &[pair[0], pair[1], pair[3], bytes]);
                let data = self.runtime_call(self.alloc_ops.block_data, &[block]);
                for (index, word) in payload.iter().enumerate() {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        *word,
                        data,
                        (index * 8) as i32,
                    );
                }
                let handle = self.runtime_call(
                    self.alloc_ops.box_create,
                    &[pair[0], pair[1], block, pair[3]],
                );
                return Some(vec![handle]);
            }
            ExprKind::AllocBoxTryNew {
                allocator,
                value,
                shape,
            } => {
                let pair = self.allocator_words(allocator)?;
                let payload = lower!(self.expr(value));
                self.consume(allocator);
                self.consume(value);
                let bytes = self.constant((self.program.width(value.ty) * 8) as i64);
                let block = self.runtime_call(
                    self.alloc_ops.block_try,
                    &[pair[0], pair[1], pair[3], bytes],
                );
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, block, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(expr.ty);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
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
                let owner = self.runtime_call(
                    self.alloc_ops.box_create,
                    &[pair[0], pair[1], block, pair[3]],
                );
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
                // Nothing retained the context on refusal; drop the operation's
                // reference before returning the untouched payload.
                self.runtime_void(self.alloc_ops.context_release, &[pair[3]]);
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
                let pair = self.allocator_words(allocator)?;
                let capacity = match capacity {
                    Some(capacity) => lower!(self.scalar(capacity)),
                    None => self.constant(0),
                };
                self.consume(allocator);
                let width = self.constant(self.program.width(*element) as i64);
                let handle = self.runtime_call(
                    self.alloc_ops.vec_create,
                    &[pair[0], pair[1], pair[2], pair[3], capacity, width],
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
                    STACK_SLOT_ALIGN_SHIFT,
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
                    STACK_SLOT_ALIGN_SHIFT,
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
                    STACK_SLOT_ALIGN_SHIFT,
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
                    STACK_SLOT_ALIGN_SHIFT,
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
                    Coercion::DynUpcast { from, to } => {
                        return Some(self.dyn_upcast(*from, *to, &values));
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
            ExprKind::DynArrayFill {
                length: length_expr,
                value,
                element,
                capacity,
                ..
            } => {
                let length = lower!(self.scalar(length_expr));
                self.consume(length_expr);
                let item = lower!(self.expr(value));
                self.consume(value);
                // A checked fill traps on a length outside 0..=capacity. A
                // proved fill keeps the same trap as a defensive check that
                // cannot fire (the unsigned compare also rejects negatives).
                let bad = self.builder.ins().icmp_imm_s(
                    IntCC::UnsignedGreaterThan,
                    length,
                    *capacity as i64,
                );
                self.guard(bad);
                let element_width = self.program.width(*element);
                let zero = self.constant(0);
                let mut out = vec![zero; 1 + element_width * capacity];
                out[0] = length;
                for slot in 0..*capacity {
                    let active = self.builder.ins().icmp_imm_s(
                        IntCC::SignedGreaterThan,
                        length,
                        slot as i64,
                    );
                    for (word, value) in item.iter().take(element_width).enumerate() {
                        let index = 1 + slot * element_width + word;
                        out[index] = self.builder.ins().select(active, *value, zero);
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
            ExprKind::DynArrayEqual {
                left,
                right,
                element,
                capacity,
                negate,
            } => {
                let left = lower!(self.expr(left));
                let right = lower!(self.expr(right));
                let width = self.program.width(*element);
                let one = self.constant(1);
                let length_equal = self.builder.ins().icmp(IntCC::Equal, left[0], right[0]);
                let mut equal = self.builder.ins().uextend(I64, length_equal);
                for slot in 0..*capacity {
                    // A slot participates only while it is inside the live
                    // length of both arrays; equal lengths make one test enough.
                    let active = self.builder.ins().icmp_imm_s(
                        IntCC::UnsignedGreaterThan,
                        left[0],
                        slot as i64,
                    );
                    let mut slot_equal = one;
                    for word in 0..width {
                        let a = left[1 + slot * width + word];
                        let b = right[1 + slot * width + word];
                        let comparison = if let Some(kind) = element.float_kind() {
                            let a = self.float_value(kind, a);
                            let b = self.float_value(kind, b);
                            self.float_binary(kind, &crate::lexer::Kind::EqEq, a, b)
                        } else {
                            let value = self.builder.ins().icmp(IntCC::Equal, a, b);
                            self.builder.ins().uextend(I64, value)
                        };
                        slot_equal = self.builder.ins().band(slot_equal, comparison);
                    }
                    let contribution = self.builder.ins().select(active, slot_equal, one);
                    equal = self.builder.ins().band(equal, contribution);
                }
                let result = if *negate {
                    let value = self.builder.ins().icmp_imm_s(IntCC::Equal, equal, 0);
                    self.builder.ins().uextend(I64, value)
                } else {
                    equal
                };
                return Some(vec![result]);
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
                field,
            } => {
                if *text {
                    let base_values = lower!(self.expr(base));
                    let (pointer, length) = match base.ty {
                        Type::Ref(p) | Type::RefMut(p) => match self.program.pointees[p] {
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
                        Type::Str | Type::StrMut => (base_values[0], base_values[1]),
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
                // A view over a record field points at the field's word offset
                // inside the pinned record storage.
                let dynamic_array_location = match &base.kind {
                    ExprKind::Borrow(slot)
                        if base
                            .ty
                            .ref_pointee()
                            .and_then(|pointee| self.program.pointees.get(pointee).copied())
                            .and_then(|pointee| pointee.layout())
                            .is_some_and(|id| self.program.enums[id].dynamic_array.is_some()) =>
                    {
                        self.locations[*slot].map(|location| (location, 0))
                    }
                    _ if field.is_some() => {
                        let (slot, offset) = projection_offset(base)
                            .expect("checked record-field DynArray view root");
                        let mut root = base.as_ref();
                        while let ExprKind::Project(inner, _) = &root.kind {
                            root = inner;
                        }
                        if root.ty.is_ref() {
                            // Through a record reference: the record lives at
                            // the reference's pointer, not in this frame.
                            let pointer = self.local_words(slot)[0];
                            Some((pointer, offset))
                        } else {
                            if let Some((slot, init)) = projection_root_init(base) {
                                // A temporary record root is initialized at the
                                // view's source position into its hidden slot.
                                let values = lower!(self.expr(init));
                                self.consume(init);
                                self.store_initialized_owner(slot, &values);
                            }
                            self.locations[slot].map(|location| (location, offset))
                        }
                    }
                    _ => None,
                };
                let base_values = if array_location.is_some() || dynamic_array_location.is_some() {
                    Vec::new()
                } else {
                    lower!(self.expr(base))
                };
                let (pointer, length, stride, bytes) =
                    if let Some((location, word_offset)) = dynamic_array_location {
                        // Word 0 is the runtime length; elements follow it.
                        let base_address = if word_offset == 0 {
                            location
                        } else {
                            self.builder
                                .ins()
                                .iadd_imm_s(location, (word_offset * 8) as i64)
                        };
                        let data = self.builder.ins().iadd_imm_s(base_address, 8);
                        let length =
                            self.builder
                                .ins()
                                .load(I64, ir::MemFlagsData::new(), base_address, 0);
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
                                    let data = self.builder.ins().iadd_imm_s(handle, 16);
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
                self.lower_while(condition, body);
                self.constant(0)
            }
            ExprKind::Loop(body) => {
                let head = self.builder.create_block();
                let exit = self.join(expr.ty);
                let depth = self.capture_handler_depth();
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
                self.restore_handler_depth(depth);
                self.jump(exit, &values);
                return None;
            }
            ExprKind::Continue(cleanup) => {
                let (head, _, _, depth) = *self.loops.last().unwrap();
                for id in cleanup {
                    self.cleanup(Some(*id));
                }
                self.restore_handler_depth(depth);
                self.jump(head, &[]);
                return None;
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot) => {
                return Some(self.local_words(*slot));
            }
            ExprKind::Block(block) => return self.block(block),
            ExprKind::Construct {
                enum_id,
                tag,
                fields,
            } => {
                let mut payload = Vec::new();
                for field in fields {
                    payload.extend(lower!(self.expr(field)));
                }
                for field in fields {
                    self.consume(field);
                }
                return Some(self.encode_variant(Type::Enum(*enum_id), *tag, &payload));
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
                        if self.deferral(expr).is_some() {
                            // A narrow value negates exactly in 64 bits.
                            let negated = self.builder.ins().isub(zero, value);
                            self.defer_int_range(kind, negated)
                        } else {
                            let (negated, overflow) = self.builder.ins().ssub_overflow(zero, value);
                            self.guard(overflow);
                            self.check_int_range(kind, negated)
                        }
                    } else {
                        let inverted = self.builder.ins().bnot(value);
                        self.canonical(kind, inverted)
                    }
                } else if *op == Kind::Bang && operand.ty == Type::I64 {
                    self.builder.ins().bnot(value)
                } else if *op == Kind::Minus {
                    let zero = self.constant(0);
                    if let Some(mode) = self.deferral(expr) {
                        let negated = self.builder.ins().isub(zero, value);
                        if mode == deferred::Mode::Exact {
                            // `0 - v` overflows exactly when `v` and the
                            // result are both negative (`v == i64::MIN`).
                            let overflow = self.builder.ins().band(value, negated);
                            self.defer_sign(overflow);
                        } else {
                            self.track_leaf(deferred::key(operand), value);
                        }
                        negated
                    } else {
                        let (value, overflow) = self.builder.ins().ssub_overflow(zero, value);
                        self.guard(overflow);
                        value
                    }
                } else {
                    let comparison = self.builder.ins().icmp_imm_s(IntCC::Equal, value, 0);
                    self.builder.ins().uextend(I64, comparison)
                }
            }
            ExprKind::Assign(slot, replacement) => {
                if self.vec_shadows.contains_key(slot) {
                    // By construction of the shadow, this is `v = push(v, e)`.
                    self.pending_pushes
                        .push((std::ptr::from_ref::<Expr>(replacement) as usize, *slot));
                }
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
                let left_key = deferred::key(left);
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
                let deferral = self.deferral(expr);
                if matches!(
                    deferral,
                    Some(deferred::Mode::Certified | deferred::Mode::Accumulate)
                ) {
                    self.track_leaf(left_key, left);
                    self.track_leaf(deferred::key(right_expr), right);
                }
                if let Some(kind) = left_kind {
                    return Some(vec![
                        self.int_binary(kind, op, left, right, right_kind, deferral),
                    ]);
                }
                match op {
                    Kind::Plus | Kind::Minus | Kind::Star if deferral.is_some() => {
                        self.deferred_i64(op, left, right, deferral.unwrap())
                    }
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
                let plans = callbacks
                    .iter()
                    .map(|callback| {
                        self.codegen
                            .inline_scalar_callbacks
                            .then(|| ScalarCallback::callback(self.program, callback))
                            .flatten()
                    })
                    .collect::<Vec<_>>();
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
                let mut current = self.load_words(address, 16, source_width);
                for ((code, callback), plan) in codes.iter().zip(callbacks.iter()).zip(&plans) {
                    if let Some(plan) = plan
                        && current.len() == 1
                    {
                        current = vec![plan.emit(&mut self.builder, current[0])];
                        continue;
                    }
                    let Type::Fn(id) = callback.ty else {
                        unreachable!("checked map callback")
                    };
                    let signature = self.program.function_types[id].clone();
                    let result = signature.result;
                    let pointer = if aggregate_result(self.program, result) {
                        let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                            ir::StackSlotKind::ExplicitSlot,
                            (self.program.width(result) * 8).max(1) as u32,
                            STACK_SLOT_ALIGN_SHIFT,
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
                        (16 + word * 8) as i32,
                    );
                }
                let next = self.builder.ins().iadd_imm_s(index, 1);
                self.jump(head, &[next]);
                self.builder.switch_to_block(done);
                // Subsequent monomorphized operations use the result's static width.
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
                        STACK_SLOT_ALIGN_SHIFT,
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
                let values = self.encode_variant(exit.result, exit.completed_tag, &payload);
                self.jump(join, &values);
                self.builder.switch_to_block(cancelled);
                let payload = self.load_words(out, 0, width);
                self.drop_value(exit.payload, &payload);
                let values = self.encode_variant(exit.result, exit.cancelled_tag, &[]);
                self.jump(join, &values);
                self.builder.switch_to_block(join);
                return Some(self.builder.block_params(join).to_vec());
            }
            ExprKind::Call(target, args) => {
                let erased_parameters = match target {
                    Target::Function(index) => {
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
                    Target::Host(op, shape) => {
                        let mut arguments = values.clone();
                        for (index, borrowed) in op.borrowed().iter().enumerate() {
                            if *borrowed {
                                arguments[index] = self.builder.ins().load(
                                    I64,
                                    ir::MemFlagsData::new(),
                                    arguments[index],
                                    0,
                                );
                            }
                        }
                        let out = self.stack_words(1);
                        arguments.push(out);
                        let status = self.runtime_call(self.host_ops[op], &arguments);
                        let success = self.builder.ins().icmp_imm_s(IntCC::Equal, status, 0);
                        let value = self
                            .builder
                            .ins()
                            .load(I64, ir::MemFlagsData::new(), out, 0);
                        let ok_tag = self.constant(shape.ok_tag as i64);
                        let err_tag = self.constant(shape.err_tag as i64);
                        let tag = self.builder.ins().select(success, ok_tag, err_tag);
                        let payload = self.builder.ins().select(success, value, status);
                        return Some(vec![tag, payload]);
                    }
                    Target::Bytes(op) => {
                        if op.borrowed() {
                            values[0] =
                                self.builder
                                    .ins()
                                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                        }
                        if matches!(op, BytesOp::Push | BytesOp::PushReserved)
                            && self.codegen.optimization == Optimization::Speed
                        {
                            self.push_bytes(values[0], values[1], *op)
                        } else if self.codegen.optimization == Optimization::Speed
                            // Checked indexed reads stay a runtime call. Inlining
                            // them moved the JSON benchmark's hot loop and cost
                            // ~6% on an older Zen 3 laptop for ~1% on Zen 5;
                            // see the plain-byte-capacity benchmark analysis.
                            && matches!(op, BytesOp::Len | BytesOp::Capacity | BytesOp::Clear)
                        {
                            self.bytes_access(*op, &values)
                        } else {
                            self.runtime_call(self.bytes_ops[op], &values)
                        }
                    }
                    Target::String(op) => {
                        if op.borrowed() {
                            values[0] =
                                self.builder
                                    .ins()
                                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                        }
                        match op {
                            StringOp::Len if self.codegen.optimization == Optimization::Speed => {
                                self.bytes_access(BytesOp::Len, &values)
                            }
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
                                return Some(self.optional_words(
                                    expr.ty,
                                    present,
                                    &[codepoint],
                                    *some_tag,
                                    *none_tag,
                                ));
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
                    Target::Str(op) => return Some(self.str_call(*op, values, expr.ty)),
                    Target::Foreign(index) => return self.foreign_call(*index, &values),
                    Target::Function(index) => return Some(self.function_call(*index, values)),
                    Target::DynCall { spec, .. } => return Some(self.dyn_call(*spec, values)),
                    Target::UnionBorrowCall { spec, .. } => {
                        return Some(self.union_borrow_call(*spec, values));
                    }
                    Target::Vec(op, element) => {
                        // The push a loop registered for one of its
                        // shadowed vectors is this very expression.
                        let address = std::ptr::from_ref(expr) as usize;
                        self.push_shadow = match self
                            .pending_pushes
                            .iter()
                            .position(|(pending, _)| *pending == address)
                        {
                            Some(at) if *op == VecOp::Push => {
                                let (_, slot) = self.pending_pushes.remove(at);
                                self.vec_shadows.get(&slot).copied()
                            }
                            _ => None,
                        };
                        let result = self.vec_call(*op, *element, values);
                        self.push_shadow = None;
                        return Some(result);
                    }
                    Target::AllocVec(op, element) => {
                        return Some(self.alloc_vec_call(*op, *element, values, expr.ty));
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
                // A borrowed DynArray scrutinee is a pointer: patterns test the
                // loaded words, and element names bind slot addresses.
                let borrowed = match input.ty {
                    Type::Ref(pointer) | Type::RefMut(pointer) => {
                        let pointee = self.program.pointees[pointer];
                        let words = self.program.width(pointee);
                        Some((value[0], self.load_words(value[0], 0, words)))
                    }
                    _ => None,
                };
                let tested = borrowed
                    .as_ref()
                    .map(|(_, words)| words.clone())
                    .unwrap_or_else(|| value.clone());
                let join = self.join(expr.ty);
                for arm in arms {
                    let hit = self.builder.create_block();
                    let next = self.builder.create_block();
                    let condition = self.pattern(&arm.pattern, &tested);
                    self.builder.ins().brif(condition, hit, &[], next, &[]);
                    self.builder.switch_to_block(hit);
                    match &borrowed {
                        Some((pointer, words)) => {
                            self.bind_borrowed_dyn(&arm.pattern, *pointer, words)
                        }
                        None => self.bind_pattern(&arm.pattern, &value),
                    }
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
                        if borrowed.is_none() {
                            self.dispose_pattern(&arm.pattern, input.ty, &value);
                        }
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
    /// Evaluate one allocator operand into `(alloc, release, realloc,
    /// context)`. The legacy value supplies three code pointers and no
    /// context; an instance context supplies one retained handle and selects
    /// its thunks inside the runtime helpers.
    fn allocator_words(&mut self, allocator: &Expr) -> Option<[Value; 4]> {
        let values = self.expr(allocator)?;
        let zero = self.constant(0);
        match allocator.ty {
            Type::Allocator => Some([values[0], values[1], values[2], zero]),
            Type::AllocatorContext => Some([zero, zero, zero, values[0]]),
            _ => unreachable!("checked allocator operand"),
        }
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
            STACK_SLOT_ALIGN_SHIFT,
        ));
        self.builder.ins().stack_addr(I64, slot, 0)
    }
    /// Read one local's words without moving it.
    fn local_words(&mut self, slot: usize) -> Words {
        if let Some(pointer) = self.locations[slot] {
            let width = self.variables[slot].len();
            return self.load_words(pointer, 0, width);
        }
        let mut words: Words = self.variables[slot]
            .iter()
            .map(|v| self.builder.use_var(*v))
            .collect();
        if let Some(width) = self.slice_layouts.get(&slot).copied() {
            words[2] = self.constant((width * 8) as i64);
            words[3] = self.constant(0);
        }
        words
    }
    /// Store a temporary-owner initializer in its already-declared hidden
    /// slot, releasing any previous value from an earlier loop evaluation.
    #[inline(never)]
    fn store_initialized_owner(&mut self, slot: usize, values: &[Value]) {
        let id = self.program.functions[self.function_index].local_resources[slot];
        self.cleanup(id);
        self.assign(slot, values);
        self.activate_local(slot);
    }
    /// Borrow one direct local binding, giving inline aggregates and owning
    /// handles their pinned address.
    fn borrow_local_value(&mut self, slot: usize) -> Words {
        let local = &self.program.functions[self.function_index].locals[slot];
        let record = local
            .ty
            .layout()
            .is_some_and(|id| self.program.enums[id].record);
        if record || local.pinned || matches!(local.ty, Type::Union(_) | Type::DynObj(_)) {
            let pointer = self.locations[slot]
                .expect("checked inline object borrow is pinned to stack storage");
            return vec![pointer];
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
            let pointer =
                self.locations[slot].expect("checked owner borrow is pinned to stack storage");
            return vec![pointer];
        }
        let variable = self.builder.use_var(self.variables[slot][0]);
        let stack = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
            ir::StackSlotKind::ExplicitSlot,
            8,
            STACK_SLOT_ALIGN_SHIFT,
        ));
        let pointer = self.builder.ins().stack_addr(I64, stack, 0);
        self.builder
            .ins()
            .store(ir::MemFlagsData::new(), variable, pointer, 0);
        vec![pointer]
    }
    /// Address of one local's pinned storage, materializing an explicit stack
    /// slot for a scalar or enum that was never pinned.
    fn local_address(&mut self, slot: usize) -> Value {
        if let Some(pointer) = self.locations[slot] {
            return pointer;
        }
        let variable = self.builder.use_var(self.variables[slot][0]);
        let stack = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
            ir::StackSlotKind::ExplicitSlot,
            (self.variables[slot].len().max(1) * 8) as u32,
            STACK_SLOT_ALIGN_SHIFT,
        ));
        let pointer = self.builder.ins().stack_addr(I64, stack, 0);
        self.builder
            .ins()
            .store(ir::MemFlagsData::new(), variable, pointer, 0);
        pointer
    }
    /// Address of a checked place expression: a pinned local or a chain of
    /// aggregate field projections over one. Only read-only projected dispatch
    /// uses this, so no relocation or ownership transfer happens here.
    /// `None` means evaluating a temporary initializer transferred control, so
    /// the surrounding expression lowering must stop emitting straight-line
    /// code.
    fn place_address(&mut self, expr: &Expr) -> Option<Value> {
        match &expr.kind {
            ExprKind::Local(slot) | ExprKind::Peek(slot) => Some(self.local_address(*slot)),
            ExprKind::InitOwner { slot, value: init } => {
                // Initialize temporary backing storage at the place's source
                // position, then address that stable slot.
                let values = lower!(self.expr(init));
                self.consume(init);
                self.store_initialized_owner(*slot, &values);
                Some(self.local_address(*slot))
            }
            ExprKind::Project(base, offset) => {
                let base_pointer = if base.ty.is_ref() {
                    lower!(self.expr(base))[0]
                } else {
                    lower!(self.place_address(base))
                };
                Some(
                    self.builder
                        .ins()
                        .iadd_imm_s(base_pointer, (*offset * 8) as i64),
                )
            }
            ExprKind::PlaceIndex { base, index, .. } if base.ty.is_slice() => {
                // A slice view is a `(data, length, stride, byte)` descriptor.
                // The element address is `data + index * stride` after the
                // bound check; a byte-backed view has no word-sized element
                // and traps instead.
                let descriptor = lower!(self.expr(base));
                let index = lower!(self.scalar(index));
                let negative = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::SignedLessThan, index, 0);
                let beyond =
                    self.builder
                        .ins()
                        .icmp(IntCC::SignedGreaterThanOrEqual, index, descriptor[1]);
                let bytes = self
                    .builder
                    .ins()
                    .icmp_imm_s(IntCC::NotEqual, descriptor[3], 0);
                let invalid = self.builder.ins().bor(negative, beyond);
                let invalid = self.builder.ins().bor(invalid, bytes);
                self.guard(invalid);
                let offset = self.builder.ins().imul(index, descriptor[2]);
                Some(self.builder.ins().iadd(descriptor[0], offset))
            }
            ExprKind::PlaceIndex { base, index, .. } => {
                let location = lower!(self.place_address(base));
                let index = lower!(self.scalar(index));
                if let Type::Vec(element) = base.ty {
                    let handle = self.load_words(location, 0, 1)[0];
                    let width =
                        self.constant(self.program.width(self.program.pointees[element]) as i64);
                    return Some(self.runtime_call(self.vec_element, &[handle, index, width]));
                }
                let (element, length) = base
                    .ty
                    .layout()
                    .and_then(|id| self.program.enums[id].array)
                    .expect("checked array index place");
                self.check_index(index, length as i64);
                let stride = (self.program.width(element) * 8) as i64;
                let offset = self.builder.ins().imul_imm_s(index, stride);
                let data = self.builder.ins().iadd_imm_s(location, 8);
                Some(self.builder.ins().iadd(data, offset))
            }
            _ => unreachable!("checked projected borrow has a place expression"),
        }
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
    fn encode_variant(&mut self, ty: Type, tag: usize, payload: &[Value]) -> Words {
        let layout = ty.layout().expect("enum constructor layout");
        let definition = &self.program.enums[layout];
        if let Some(niche) = definition.niche() {
            // Encoding is the inverse of the certificate's decoder: an empty
            // variant stores its constant, the payload keeps its own words.
            return match niche.decoder(tag) {
                crate::layout_cert::Decoder::Equal(constant) => vec![self.constant(constant)],
                crate::layout_cert::Decoder::NotEqual(_) => {
                    debug_assert_eq!(payload.len(), 1);
                    payload.to_vec()
                }
            };
        }
        let mut words = Vec::with_capacity(definition.words);
        if definition.tag_words() != 0 {
            words.push(self.constant(tag as i64));
        }
        words.extend_from_slice(payload);
        while words.len() < self.program.width(ty) {
            words.push(self.constant(0));
        }
        words
    }
    fn optional_words(
        &mut self,
        ty: Type,
        present: Value,
        payload: &[Value],
        some: usize,
        none: usize,
    ) -> Words {
        let some = self.encode_variant(ty, some, payload);
        let none = self.encode_variant(ty, none, &[]);
        some.into_iter()
            .zip(none)
            .map(|(some, none)| self.builder.ins().select(present, some, none))
            .collect()
    }
    fn str_call(&mut self, op: StrOp, values: Words, ty: Type) -> Words {
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
                self.optional_words(ty, present, &[codepoint], some_tag, none_tag)
            }
            StrOp::ToString => {
                vec![self.runtime_call(self.str_to_string, &[pointer, length])]
            }
            StrOp::AsciiUpper => {
                self.runtime_call(self.str_writes[0], &[pointer, length]);
                vec![]
            }
            StrOp::AsciiLower => {
                self.runtime_call(self.str_writes[1], &[pointer, length]);
                vec![]
            }
            StrOp::SetScalar => {
                self.runtime_call(self.str_writes[2], &[pointer, length, values[4], values[5]]);
                vec![]
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
        let mut offset = self.program.enums[layout].tag_words();
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
        let mut offset = self.program.enums[source_id].tag_words();
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
            Coercion::DynUpcast { from, to } => self.dyn_upcast(*from, *to, values),
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
    /// Lower small byte-buffer operations directly so hot loops can keep their
    /// length loads and bounds checks visible to Cranelift's optimizer. The
    /// unsigned comparison rejects negative indices as well as the upper bound.
    fn bytes_access(&mut self, op: BytesOp, values: &[Value]) -> Value {
        let handle = values[0];
        match op {
            BytesOp::Len => self
                .builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), handle, 0),
            BytesOp::Capacity => self
                .builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), handle, 8),
            BytesOp::Get => {
                let length = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0);
                let invalid =
                    self.builder
                        .ins()
                        .icmp(IntCC::UnsignedGreaterThanOrEqual, values[1], length);
                self.guard(invalid);
                let address = self.builder.ins().iadd(handle, values[1]);
                self.builder
                    .ins()
                    .uload8(I64, ir::MemFlagsData::new(), address, 16)
            }
            BytesOp::Clear => {
                let zero = self.constant(0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, handle, 0);
                handle
            }
            _ => unreachable!("checked byte-buffer access"),
        }
    }
    /// Decode ordinary buffer capacity. Headerless buffers have at most 1008
    /// data bytes, so their logical capacity fits in 16 bits. Header-bearing
    /// buffers retain the complete positive word, including large capacities.
    /// Build memory accesses of one class. The class travels as the
    /// instructions' source location, which Cranelift's code generator
    /// ignores and the LLVM backend turns into alias metadata.
    fn memory_class<T>(
        &mut self,
        class: llvm::MemoryClass,
        build: impl FnOnce(&mut Self) -> T,
    ) -> T {
        // Locations are stored relative to a base; fix it at zero so that no
        // class can coincide with "no location".
        self.builder
            .func
            .params
            .ensure_base_srcloc(ir::SourceLoc::new(0));
        let previous = self.builder.srcloc();
        self.builder.set_srcloc(ir::SourceLoc::new(class as u32));
        let built = build(self);
        self.builder.set_srcloc(previous);
        built
    }
    fn buffer_capacity(&mut self, handle: Value) -> Value {
        let word = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            g.builder
                .ins()
                .load(I64, ir::MemFlagsData::new(), handle, 8)
        });
        let raw = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, word, 0);
        let decoded = self.builder.ins().band_imm_s(word, 0xffff);
        self.builder.ins().select(raw, decoded, word)
    }
    /// Release-mode byte append avoids a C call when capacity is available.
    /// The unsigned range check also rejects negative values. The cold helper
    /// keeps all existing growth, overflow and reserved-capacity failures.
    fn push_bytes(&mut self, handle: Value, value: Value, op: BytesOp) -> Value {
        let invalid = self
            .builder
            .ins()
            .icmp_imm_u(IntCC::UnsignedGreaterThan, value, 255);
        self.guard(invalid);
        let (length, capacity) = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            (
                g.builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0),
                g.builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 8),
            )
        });
        let room = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, length, capacity);
        let fast = self.builder.create_block();
        let slow = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, I64);
        self.builder.ins().brif(room, fast, &[], slow, &[]);
        self.builder.switch_to_block(fast);
        let address = self.builder.ins().iadd(handle, length);
        self.memory_class(llvm::MemoryClass::BufferElements, |g| {
            g.builder
                .ins()
                .istore8(ir::MemFlagsData::new(), value, address, 16);
        });
        let next = self.builder.ins().iadd_imm_s(length, 1);
        self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            g.builder
                .ins()
                .store(ir::MemFlagsData::new(), next, handle, 0);
        });
        self.jump(join, &[handle]);
        self.builder.switch_to_block(slow);
        let grown = self.runtime_call(self.bytes_ops[&op], &[handle, value]);
        self.jump(join, &[grown]);
        self.builder.switch_to_block(join);
        self.builder.block_params(join)[0]
    }
    /// A checked vector has `length <= capacity` and an allocation large
    /// enough for every capacity slot. The fast arm neither grows nor changes
    /// ownership; the original helper handles all capacity/overflow cases.
    fn push_vector(&mut self, handle: Value, words: &[Value]) -> Value {
        let callee = self
            .module
            .declare_func_in_func(self.vec_ops[&VecOp::Push], self.builder.func);
        let width = self.constant(words.len() as i64);
        if self.codegen.optimization != Optimization::Speed {
            let item = self.stack_words(words.len());
            self.store_words(item, words);
            let call = self.builder.ins().call(callee, &[handle, item, width]);
            return self.builder.inst_results(call)[0];
        }
        let shadow = self.push_shadow.take();
        let (length, capacity) = match shadow {
            Some((length, capacity)) => {
                (self.builder.use_var(length), self.builder.use_var(capacity))
            }
            None => {
                let length = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
                    g.builder
                        .ins()
                        .load(I64, ir::MemFlagsData::new(), handle, 0)
                });
                (length, self.buffer_capacity(handle))
            }
        };
        let room = self
            .builder
            .ins()
            .icmp(IntCC::UnsignedLessThan, length, capacity);
        let next = self.builder.ins().iadd_imm_s(length, 1);
        let fast = self.builder.create_block();
        let slow = self.builder.create_block();
        let join = self.builder.create_block();
        self.builder.append_block_param(join, I64);
        self.builder.ins().brif(room, fast, &[], slow, &[]);
        self.builder.switch_to_block(fast);
        let offset = self
            .builder
            .ins()
            .imul_imm_s(length, (words.len() * 8) as i64);
        let address = self.builder.ins().iadd(handle, offset);
        self.memory_class(llvm::MemoryClass::BufferElements, |g| {
            for (word, value) in words.iter().enumerate() {
                g.builder.ins().store(
                    ir::MemFlagsData::new(),
                    *value,
                    address,
                    (16 + word * 8) as i32,
                );
            }
        });
        self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
            g.builder
                .ins()
                .store(ir::MemFlagsData::new(), next, handle, 0);
        });
        self.jump(join, &[handle]);
        self.builder.switch_to_block(slow);
        let item = self.stack_words(words.len());
        self.store_words(item, words);
        let call = self.builder.ins().call(callee, &[handle, item, width]);
        let grown = self.builder.inst_results(call)[0];
        if let Some((_, capacity)) = shadow {
            // The push succeeded or panicked, so the length is one more
            // either way; the capacity is whatever the new block has.
            let grown_capacity = self.buffer_capacity(grown);
            self.builder.def_var(capacity, grown_capacity);
        }
        self.jump(join, &[grown]);
        self.builder.switch_to_block(join);
        if let Some((length_var, _)) = shadow {
            self.builder.def_var(length_var, next);
        }
        self.builder.block_params(join)[0]
    }

    fn slice_out_of_bounds(&mut self, index: Value, length: Value) -> Value {
        if self.codegen.optimization == Optimization::Speed
            && self.upper_bounds.iter().any(|(known_index, known_length)| {
                self.builder.func.dfg.resolve_aliases(*known_index)
                    == self.builder.func.dfg.resolve_aliases(index)
                    && self.builder.func.dfg.resolve_aliases(*known_length)
                        == self.builder.func.dfg.resolve_aliases(length)
            })
        {
            // The exact SSA pair already passed `index < length`. A negative
            // index can still pass a signed loop condition, so retain its check
            // at the original access site, after all preceding effects.
            self.builder
                .ins()
                .icmp_imm_s(IntCC::SignedLessThan, index, 0)
        } else {
            // Length is always nonnegative; unsigned comparison rejects both
            // negative indices and indices at/above length in one test.
            self.builder
                .ins()
                .icmp(IntCC::UnsignedGreaterThanOrEqual, index, length)
        }
    }

    fn loop_slice(&self, condition: &Expr) -> Option<(usize, usize, usize)> {
        let ExprKind::Binary(Kind::Lt, index, length) = &condition.kind else {
            return None;
        };
        let (ExprKind::Local(index_slot) | ExprKind::Peek(index_slot)) = index.kind else {
            return None;
        };
        let ExprKind::Call(Target::Slice(SliceOp::Len, element), arguments) = &length.kind else {
            return None;
        };
        let [view] = arguments.as_slice() else {
            return None;
        };
        let (ExprKind::Local(view_slot) | ExprKind::Peek(view_slot)) = view.kind else {
            return None;
        };
        let locals = &self.program.functions[self.function_index].locals;
        if locals[index_slot].ty != Type::I64
            || locals[index_slot].pinned
            || locals[view_slot].mutable
            || locals[view_slot].pinned
        {
            return None;
        }
        Some((index_slot, view_slot, self.program.width(*element)))
    }

    fn lower_while(&mut self, condition: &Expr, body: &ex::Block) {
        // A loop that appends to a vector reloads its length and capacity
        // from the heap block on every `Vec.push`, and decodes the capacity,
        // because the growth call in the same loop may have changed both.
        // Where the loop touches the vector's header through nothing but
        // those pushes, keep the two in variables instead: load them once,
        // update them at each push (the length is still stored, so memory
        // is never stale), and reload the capacity only after a growth.
        // Only for LLVM: Cranelift's code for the same loop measured 15 to
        // 20% slower with the two extra loop-carried values than with the
        // reloads.
        let shadowed: Vec<usize> = if self.codegen.optimization == Optimization::Speed
            && self.codegen.backend == Backend::Llvm
        {
            push_only_vectors(condition, body)
                .into_iter()
                .filter(|slot| {
                    !self.vec_shadows.contains_key(slot)
                        && !self.erased_local(*slot)
                        && self.variables[*slot].len() == 1
                })
                .collect()
        } else {
            Vec::new()
        };
        if !shadowed.is_empty() && std::env::var_os("KUSH_TRACE_SHADOWS").is_some() {
            eprintln!(
                "vector shadows: a loop in {} keeps {} vector(s) in variables",
                self.program.functions[self.function_index].name,
                shadowed.len()
            );
        }
        for slot in &shadowed {
            let handle = self.local_words(*slot)[0];
            let length = self.memory_class(llvm::MemoryClass::BufferHeader, |g| {
                g.builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), handle, 0)
            });
            let capacity = self.buffer_capacity(handle);
            let length_var = self.builder.declare_var(I64);
            let capacity_var = self.builder.declare_var(I64);
            self.builder.def_var(length_var, length);
            self.builder.def_var(capacity_var, capacity);
            self.vec_shadows.insert(*slot, (length_var, capacity_var));
        }
        self.lower_while_checks(condition, body);
        for slot in &shadowed {
            self.vec_shadows.remove(slot);
        }
        if self.vec_shadows.is_empty() {
            self.pending_pushes.clear();
        }
    }
    fn lower_while_checks(&mut self, condition: &Expr, body: &ex::Block) {
        if self.codegen.defers_overflow()
            && self.deferred.is_none()
            && let Some(plan) = deferred::plan(
                &self.program.functions[self.function_index],
                condition,
                body,
                self.codegen.wide_multiply(),
            )
        {
            self.lower_deferred_while(plan, condition, body);
        } else {
            self.lower_checked_while(condition, body);
        }
    }
    fn lower_checked_while(&mut self, condition: &Expr, body: &ex::Block) {
        let candidate = self.loop_slice(condition);
        // Bound code growth and avoid recursively duplicating nested loops.
        fn eligible(expr: &Expr, budget: &mut usize) -> bool {
            if *budget == 0 || matches!(expr.kind, ExprKind::While(..) | ExprKind::Loop(..)) {
                return false;
            }
            *budget -= 1;
            let mut safe = true;
            expr.for_each_child(&mut |child| safe &= eligible(child, budget));
            safe
        }
        let mut budget = 96;
        let small = body.statements.iter().all(|statement| match statement {
            ex::Statement::Let(_, expr) | ex::Statement::Expr(expr) => eligible(expr, &mut budget),
            ex::Statement::Declare(_) => false,
        }) && body
            .tail
            .as_ref()
            .is_none_or(|expr| eligible(expr, &mut budget));
        if self.codegen.optimization == Optimization::Speed
            && self.slice_layouts.is_empty()
            && small
            && let Some((_, slot, width)) = candidate
        {
            let words = self.local_words(slot);
            let stride = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::Equal, words[2], (width * 8) as i64);
            let normal = self.builder.ins().icmp_imm_s(IntCC::Equal, words[3], 0);
            let matches = self.builder.ins().band(stride, normal);
            let fast = self.builder.create_block();
            let generic = self.builder.create_block();
            let join = self.builder.create_block();
            self.builder.ins().brif(matches, fast, &[], generic, &[]);
            self.builder.switch_to_block(fast);
            self.slice_layouts.insert(slot, width);
            self.while_body(condition, body, candidate);
            self.slice_layouts.remove(&slot);
            self.jump(join, &[]);
            self.builder.switch_to_block(generic);
            self.while_body(condition, body, candidate);
            self.jump(join, &[]);
            self.builder.switch_to_block(join);
        } else {
            self.while_body(condition, body, candidate);
        }
    }

    fn while_body(
        &mut self,
        condition: &Expr,
        body: &ex::Block,
        candidate: Option<(usize, usize, usize)>,
    ) {
        let head = self.builder.create_block();
        let enter = self.builder.create_block();
        let exit = self.builder.create_block();
        let depth = self.capture_handler_depth();
        self.jump(head, &[]);
        self.builder.switch_to_block(head);
        if let Some(test) = self.scalar(condition) {
            let fact = candidate
                .map(|(index, view, _)| (self.local_words(index)[0], self.local_words(view)[1]));
            // A deferred loop runs a bounded number of iterations at a time.
            let fuel = self
                .deferred
                .as_ref()
                .map(|state| state.fuel)
                .or(self.checked_fuel);
            let test = match fuel {
                Some(fuel) => {
                    let left = self.builder.use_var(fuel);
                    let some = self.builder.ins().icmp_imm_s(IntCC::NotEqual, left, 0);
                    let some = self.builder.ins().uextend(I64, some);
                    let holds = self.builder.ins().icmp_imm_s(IntCC::NotEqual, test, 0);
                    let holds = self.builder.ins().uextend(I64, holds);
                    self.builder.ins().band(holds, some)
                }
                None => test,
            };
            self.builder.ins().brif(test, enter, &[], exit, &[]);
            self.builder.seal_block(enter);
            self.builder.switch_to_block(enter);
            let saved = self.upper_bounds.len();
            if let Some(fact) = fact {
                self.upper_bounds.push(fact);
            }
            self.loops.push((head, exit, false, depth));
            let finished = self.block(body);
            self.loops.pop();
            self.upper_bounds.truncate(saved);
            if finished.is_some() {
                if let Some(fuel) = fuel {
                    let left = self.builder.use_var(fuel);
                    let left = self.builder.ins().iadd_imm_s(left, -1);
                    self.builder.def_var(fuel, left);
                }
                self.jump(head, &[]);
            }
        }
        self.builder.switch_to_block(exit);
    }

    fn slice_call(&mut self, op: SliceOp, element: Type, values: Words) -> Words {
        let element_width = self.program.width(element);
        let (pointer, length, stride, bytes) = (values[0], values[1], values[2], values[3]);
        if op == SliceOp::Len {
            return vec![length];
        }
        let index = values[4];
        if op == SliceOp::Set {
            let invalid = self.slice_out_of_bounds(index, length);
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
            let invalid = self.slice_out_of_bounds(index, length);
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
            let some_values = self.encode_variant(Type::Enum(option), some_tag, &payload);
            self.jump(join, &some_values);
            self.builder.switch_to_block(none);
            let none_values = self.encode_variant(Type::Enum(option), none_tag, &[]);
            self.jump(join, &none_values);
            self.builder.switch_to_block(join);
            return self.builder.block_params(join).to_vec();
        }
        if op == SliceOp::Get {
            let invalid = self.slice_out_of_bounds(index, length);
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
    fn alloc_vec_call(
        &mut self,
        op: AllocVecOp,
        element: Type,
        values: Words,
        result: Type,
    ) -> Words {
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
            AllocVecOp::TryPush => {
                let item = self.stack_words(width);
                self.store_words(item, &values[1..1 + width]);
                let success = self.runtime_call(self.alloc_ops.vec_try_push, &[values[0], item]);
                let shape = result
                    .layout()
                    .and_then(|id| self.program.enums[id].result)
                    .expect("checked AllocVec.try_push result");
                let failed = self.builder.ins().icmp_imm_s(IntCC::Equal, success, 0);
                let ok = self.builder.create_block();
                let error = self.builder.create_block();
                let done = self.builder.create_block();
                let result_width = self.program.width(result);
                let slot = self.builder.create_sized_stack_slot(ir::StackSlotData::new(
                    ir::StackSlotKind::ExplicitSlot,
                    (result_width * 8).max(1) as u32,
                    STACK_SLOT_ALIGN_SHIFT,
                ));
                let destination = self.builder.ins().stack_addr(I64, slot, 0);
                let zero = self.constant(0);
                self.builder.ins().brif(failed, error, &[], ok, &[]);
                self.builder.switch_to_block(ok);
                for index in 0..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                let tag = self.constant(shape.ok_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), values[0], destination, 8);
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(error);
                let tag = self.constant(shape.err_tag as i64);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), tag, destination, 0);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), zero, destination, 8);
                self.builder
                    .ins()
                    .store(ir::MemFlagsData::new(), values[0], destination, 16);
                for index in 0..width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        values[1 + index],
                        destination,
                        ((index + 3) * 8) as i32,
                    );
                }
                for index in (3 + width)..result_width {
                    self.builder.ins().store(
                        ir::MemFlagsData::new(),
                        zero,
                        destination,
                        (index * 8) as i32,
                    );
                }
                self.builder.ins().jump(done, &[]);
                self.builder.switch_to_block(done);
                (0..result_width)
                    .map(|index| {
                        self.builder.ins().load(
                            I64,
                            ir::MemFlagsData::new(),
                            destination,
                            (index * 8) as i32,
                        )
                    })
                    .collect()
            }
            AllocVecOp::Pop => {
                let item = self.stack_words(width);
                self.runtime_void(self.alloc_ops.vec_pop, &[values[0], item]);
                let zero = self.constant(0);
                let mut out = vec![zero, values[0]];
                out.extend(self.load_words(item, 0, width));
                out
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
            let mut args = args.to_vec();
            if !matches!(op, VecOp::WithCapacity | VecOp::Len) {
                args.push(g.constant(width as i64));
            }
            let call = g.builder.ins().call(callee, &args);
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
                    let fields = self.load_words(slot, 16, width);
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
                let grown = self.push_vector(handle, &values[1..1 + width]);
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
                    let fields = self.load_words(slot, 16, width);
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
            // Length, checked reads and copyable writes are inline: the header
            // is `{length, capacity}` followed by the elements (`KushVec`).
            // With speed optimization the length is an inline load (the header
            // is `{length, capacity}`, `KushVec`). Checked reads and writes stay
            // runtime calls: inlining them cost ~5-6% on the JSON benchmark
            // (2026-11-06). Proved reads (`Vec.at`) are inline loads.
            VecOp::Len => {
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                if self.codegen.optimization == Optimization::Speed {
                    vec![
                        self.builder
                            .ins()
                            .load(I64, ir::MemFlagsData::new(), handle, 0),
                    ]
                } else {
                    call(self, op, &[handle])
                }
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
                // Proved in bounds: direct load after the 16-byte header.
                let handle = self
                    .builder
                    .ins()
                    .load(I64, ir::MemFlagsData::new(), values[0], 0);
                let stride = self.builder.ins().imul_imm_s(values[1], (width * 8) as i64);
                let base = self.builder.ins().iadd(handle, stride);
                self.load_words(base, 16, width)
            }
            VecOp::Push => {
                vec![self.push_vector(values[0], &values[1..1 + width])]
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
    /// How this checked operation is lowered inside a deferred loop.
    fn deferral(&self, expr: &Expr) -> Option<deferred::Mode> {
        self.deferred
            .as_ref()?
            .plan
            .modes
            .get(&deferred::key(expr))
            .copied()
    }
    /// Record a deferred overflow whose indicator is the word's sign bit.
    fn defer_sign(&mut self, word: Value) {
        let sticky = self.deferred.as_ref().expect("deferred loop").sticky;
        let previous = self.builder.use_var(sticky);
        let merged = self.builder.ins().bor(previous, word);
        self.builder.def_var(sticky, merged);
    }
    /// Record a deferred overflow from a 0/1 flag.
    fn defer_flag(&mut self, flag: Value) {
        let wide = self.builder.ins().uextend(I64, flag);
        let word = self.builder.ins().ineg(wide);
        self.defer_sign(word);
    }
    fn defer_int_range(&mut self, kind: IntKind, value: Value) -> Value {
        let canonical = self.canonical(kind, value);
        let wrong = self.builder.ins().icmp(IntCC::NotEqual, canonical, value);
        self.defer_flag(wrong);
        // The wrapped result, not the raw word: the rest of the lowering
        // relies on narrow values being in canonical form (for instance, a
        // narrow signed division has no `MIN / -1` guard).
        canonical
    }
    /// OR an operand's magnitude word into its tracker, if it has one.
    fn track_leaf(&mut self, key: usize, value: Value) {
        let Some(tracker) = self
            .deferred
            .as_ref()
            .and_then(|state| state.leaves.get(&key).copied())
        else {
            return;
        };
        let folded = self.magnitude(value);
        let previous = self.builder.use_var(tracker);
        let merged = self.builder.ins().bor(previous, folded);
        self.builder.def_var(tracker, merged);
    }
    /// Wrapping signed 64-bit `+`, `-`, `*` with its check deferred. Exact
    /// add/sub tests are plain bit operations so the loop stays vectorizable;
    /// certified operations have no test at all.
    fn deferred_i64(
        &mut self,
        op: &Kind,
        left: Value,
        right: Value,
        mode: deferred::Mode,
    ) -> Value {
        if mode != deferred::Mode::Exact {
            return match op {
                Kind::Plus => self.builder.ins().iadd(left, right),
                Kind::Minus => self.builder.ins().isub(left, right),
                _ => self.builder.ins().imul(left, right),
            };
        }
        match op {
            Kind::Plus => {
                let sum = self.builder.ins().iadd(left, right);
                let a = self.builder.ins().bxor(left, sum);
                let b = self.builder.ins().bxor(right, sum);
                let overflow = self.builder.ins().band(a, b);
                self.defer_sign(overflow);
                sum
            }
            Kind::Minus => {
                let difference = self.builder.ins().isub(left, right);
                let a = self.builder.ins().bxor(left, right);
                let b = self.builder.ins().bxor(left, difference);
                let overflow = self.builder.ins().band(a, b);
                self.defer_sign(overflow);
                difference
            }
            _ => {
                let (product, overflow) = self.builder.ins().smul_overflow(left, right);
                self.defer_flag(overflow);
                product
            }
        }
    }
    /// `v ^ (v << 1)`: a word of bit length `b` (0 for zero) such that
    /// `|v| <= 2^(b - 1)`. Its highest set bit is one above the highest bit
    /// where `v` differs from its sign. Two cheap vector operations.
    fn magnitude(&mut self, value: Value) -> Value {
        let doubled = self.builder.ins().iadd(value, value);
        self.builder.ins().bxor(value, doubled)
    }
    /// Leading zeros of a word, counting zero itself as one (63).
    ///
    /// Where they are used the two give the same bound, and the operand is
    /// then visibly non-zero. Without that, a target that has no cheap
    /// count-leading-zeros gets a branch around each one late in LLVM's
    /// code generation, and each such split rescans the whole function:
    /// build time grew with the square of the number of deferred loops
    /// inlined into one function.
    fn leading_zeros(&mut self, word: Value) -> Value {
        let nonzero = self.builder.ins().bor_imm_s(word, 1);
        self.builder.ins().clz(nonzero)
    }
    /// The least tracked `u` with `|v| <= 2^u` for a magnitude word.
    fn magnitude_bound(&mut self, word: Value) -> Value {
        let zeros = self.leading_zeros(word);
        let sixty_four = self.constant(64);
        let bits = self.builder.ins().isub(sixty_four, zeros);
        let one = self.constant(1);
        let floor = self.builder.ins().umax(bits, one);
        self.builder.ins().iadd_imm_s(floor, -1)
    }
    /// Evaluate a certificate bound after the loop.
    fn bound_value(
        &mut self,
        bound: &deferred::Bound,
        leaves: &BTreeMap<usize, Variable>,
        entry: &BTreeMap<usize, Value>,
        count: Variable,
    ) -> Value {
        use deferred::Bound;
        match bound {
            Bound::Constant(bits) => self.constant(i64::from(*bits)),
            Bound::Leaf(key) => {
                let word = self.builder.use_var(leaves[key]);
                self.magnitude_bound(word)
            }
            Bound::Sum(left, right) => {
                let left = self.bound_value(left, leaves, entry, count);
                let right = self.bound_value(right, leaves, entry, count);
                let larger = self.builder.ins().umax(left, right);
                self.builder.ins().iadd_imm_s(larger, 1)
            }
            Bound::Product(left, right) => {
                let left = self.bound_value(left, leaves, entry, count);
                let right = self.bound_value(right, leaves, entry, count);
                self.builder.ins().iadd(left, right)
            }
            Bound::Accumulated { local, operands } => {
                let mut largest = self.magnitude_bound(entry[local]);
                for operand in operands {
                    let operand = self.bound_value(operand, leaves, entry, count);
                    largest = self.builder.ins().umax(largest, operand);
                }
                // At least one: the loop has an accumulating operation.
                let steps = self.builder.use_var(count);
                let zeros = self.leading_zeros(steps);
                let sixty_four = self.constant(64);
                let bits = self.builder.ins().isub(sixty_four, zeros);
                self.builder.ins().iadd(largest, bits)
            }
        }
    }
    /// Lower an innermost counted loop with its overflow panics deferred to
    /// the exit. `deferred` documents why the result is indistinguishable
    /// from checking every operation.
    /// The loop body is lowered three times: the deferred chunk, specialized
    /// to the walked slice being consecutive whole elements; one chunk with
    /// ordinary checks, shared by a chunk that failed its certificate
    /// (replayed from its entry state) and a chunk whose upward counter
    /// starts negative; and the whole loop with ordinary checks, for views
    /// that overlap or a walked slice with another layout. An ordinary loop
    /// over a slice is lowered twice.
    fn lower_deferred_while(&mut self, plan: deferred::Plan, condition: &Expr, body: &ex::Block) {
        let zero = self.constant(0);
        let sticky = self.builder.declare_var(I64);
        let count = self.builder.declare_var(I64);
        let fuel = self.builder.declare_var(I64);
        let mut leaves = BTreeMap::new();
        for key in &plan.leaves {
            leaves.insert(*key, self.builder.declare_var(I64));
        }
        let done = self.builder.create_block();
        // The loop runs in chunks of at most `CHUNK` iterations, each checked
        // on its own, so an overflow is reported after a bounded amount of
        // further work no matter how long the loop would have run, or what
        // the wrapped values do to it in the meantime.
        let chunk = self.builder.create_block();
        let checked = self.builder.create_block();
        // Where every chunk ends: out of fuel means the loop may have more
        // to do; anything else is the loop's own exit.
        let next = self.builder.create_block();
        let mut unsuitable = self.constant(0);
        // A replay re-reads what the first attempt read, so nothing the loop
        // reads may be something it wrote. The borrow rules already say so
        // of two distinct views; compare the address ranges anyway, once.
        for (stored, loaded) in &plan.disjoint {
            let (stored_start, stored_end) = self.view_range(*stored);
            let (loaded_start, loaded_end) = self.view_range(*loaded);
            let before = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, stored_start, loaded_end);
            let after = self
                .builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, loaded_start, stored_end);
            let both = self.builder.ins().band(before, after);
            let both = self.builder.ins().uextend(I64, both);
            unsuitable = self.builder.ins().bor(unsuitable, both);
        }
        // The deferred chunk is specialized to the slice the loop walks
        // being consecutive whole elements; nothing else would vectorize.
        let candidate = self.loop_slice(condition);
        let layout = candidate.filter(|_| {
            self.codegen.optimization == Optimization::Speed && self.slice_layouts.is_empty()
        });
        if let Some((_, slot, width)) = layout {
            let words = self.local_words(slot);
            let stride =
                self.builder
                    .ins()
                    .icmp_imm_s(IntCC::NotEqual, words[2], (width * 8) as i64);
            let stride = self.builder.ins().uextend(I64, stride);
            unsuitable = self.builder.ins().bor(unsuitable, stride);
            unsuitable = self.builder.ins().bor(unsuitable, words[3]);
        }
        // Such a loop is an ordinary loop: no chunks, no fuel. (Running it
        // through the checked chunk instead measured 2.4 times slower.)
        let plain = self.builder.create_block();
        self.builder.ins().brif(unsuitable, plain, &[], chunk, &[]);
        self.builder.switch_to_block(plain);
        self.while_body(condition, body, candidate);
        self.jump(done, &[]);
        // Every chunk starts here, so the chunks form one ordinary loop
        // with a single way in.
        self.builder.switch_to_block(chunk);
        self.builder.def_var(sticky, zero);
        self.builder.def_var(count, zero);
        let full = self.constant(deferred::CHUNK);
        self.builder.def_var(fuel, full);
        for tracker in leaves.values() {
            self.builder.def_var(*tracker, zero);
        }
        // An upward counter that starts a chunk non-negative stays so, which
        // is what removes the lower bounds check of every index it forms.
        // Inside one loop LLVM sees that for itself; across chunks it has to
        // be shown the starting sign. A chunk that starts negative (rare,
        // and legal) runs with ordinary checks.
        if let Some(counter) = plan.ascending {
            let start = self.local_words(counter)[0];
            let negative = self
                .builder
                .ins()
                .icmp_imm_s(IntCC::SignedLessThan, start, 0);
            let chunked = self.builder.create_block();
            self.builder
                .ins()
                .brif(negative, checked, &[], chunked, &[]);
            self.builder.switch_to_block(chunked);
        }
        let mut entry_magnitudes = BTreeMap::new();
        for slot in &plan.accumulators {
            let value = self.local_words(*slot)[0];
            let word = self.magnitude(value);
            entry_magnitudes.insert(*slot, word);
        }
        let entry: Vec<(usize, Words)> = plan
            .replay
            .iter()
            .map(|slot| (*slot, self.local_words(*slot)))
            .collect();
        self.deferred = Some(DeferredLoop {
            plan,
            sticky,
            leaves,
            fuel,
        });
        if let Some((_, slot, width)) = layout {
            self.slice_layouts.insert(slot, width);
        }
        self.while_body(condition, body, candidate);
        if let Some((_, slot, _)) = layout {
            self.slice_layouts.remove(&slot);
        }
        let state = self.deferred.take().expect("deferred loop");
        if !state.plan.obligations.is_empty() {
            // How many terms the reductions took in, at most: each
            // accumulating operation runs at most once per iteration, and
            // the fuel says how many iterations completed. One more covers
            // an iteration that left the loop part-way. Counting in the
            // loop would be exact but costs a vector reduction of its own.
            let accumulating = state
                .plan
                .modes
                .values()
                .filter(|mode| **mode == deferred::Mode::Accumulate)
                .count() as i64;
            let left = self.builder.use_var(fuel);
            let limit = self.constant(deferred::CHUNK + 1);
            let started = self.builder.ins().isub(limit, left);
            let terms = self.builder.ins().imul_imm_s(started, accumulating);
            self.builder.def_var(count, terms);
            // The certificate: every bound is within the limit.
            let mut worst = self.constant(0);
            for obligation in &state.plan.obligations {
                let value = self.bound_value(obligation, &state.leaves, &entry_magnitudes, count);
                worst = self.builder.ins().umax(worst, value);
            }
            let proved = self.builder.ins().icmp_imm_u(
                IntCC::UnsignedLessThanOrEqual,
                worst,
                deferred::LIMIT,
            );
            let certified = self.builder.create_block();
            let replay = self.builder.create_block();
            self.builder.ins().brif(proved, certified, &[], replay, &[]);
            // Without it nothing is known: run this chunk again from its
            // entry state with ordinary checks, then go on in chunks.
            self.builder.switch_to_block(replay);
            for (slot, words) in entry {
                self.assign(slot, &words);
            }
            self.jump(checked, &[]);
            // With it, every value was exact, so the sticky word of the
            // remaining exact tests is exact too.
            self.builder.switch_to_block(certified);
        }
        let overflowed = self.builder.use_var(sticky);
        let overflowed = self
            .builder
            .ins()
            .icmp_imm_s(IntCC::SignedLessThan, overflowed, 0);
        self.guard(overflowed);
        self.jump(next, &[]);
        // The one chunk with ordinary checks. Every way in arrives with the
        // locals of a checked execution: untouched, or a chunk's entry state
        // restored, or the result of an earlier chunk that passed.
        self.builder.switch_to_block(checked);
        let full = self.constant(deferred::CHUNK);
        self.builder.def_var(fuel, full);
        self.checked_fuel = Some(fuel);
        self.while_body(condition, body, candidate);
        self.checked_fuel = None;
        self.jump(next, &[]);
        self.builder.switch_to_block(next);
        let left = self.builder.use_var(fuel);
        let exhausted = self.builder.ins().icmp_imm_s(IntCC::Equal, left, 0);
        self.builder.ins().brif(exhausted, chunk, &[], done, &[]);
        self.builder.switch_to_block(done);
    }
    /// The address range `[start, end)` of a slice local's elements.
    fn view_range(&mut self, slot: usize) -> (Value, Value) {
        let words = self.local_words(slot);
        let bytes = self.builder.ins().imul(words[1], words[2]);
        let end = self.builder.ins().iadd(words[0], bytes);
        (words[0], end)
    }
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
        deferral: Option<deferred::Mode>,
    ) -> Value {
        let signed = kind.signed();
        let wide = kind.bits() == 64;
        match op {
            Kind::Plus | Kind::Minus | Kind::Star if deferral.is_some() => {
                if !wide {
                    // Canonical narrow operands combine exactly in 64 bits
                    // (a `u32` product modulo 2^64 is still the exact
                    // product), so the range test alone decides.
                    let value = match op {
                        Kind::Plus => self.builder.ins().iadd(left, right),
                        Kind::Minus => self.builder.ins().isub(left, right),
                        _ => self.builder.ins().imul(left, right),
                    };
                    return self.defer_int_range(kind, value);
                }
                if signed {
                    return self.deferred_i64(op, left, right, deferral.unwrap());
                }
                let (value, overflow) = match op {
                    Kind::Plus => {
                        let sum = self.builder.ins().iadd(left, right);
                        let carry = self.builder.ins().icmp(IntCC::UnsignedLessThan, sum, left);
                        (sum, carry)
                    }
                    Kind::Minus => {
                        let difference = self.builder.ins().isub(left, right);
                        let borrow = self
                            .builder
                            .ins()
                            .icmp(IntCC::UnsignedLessThan, left, right);
                        (difference, borrow)
                    }
                    _ => self.builder.ins().umul_overflow(left, right),
                };
                self.defer_flag(overflow);
                value
            }
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
                g.optional_words(ty, present, &[payload], some, none)
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
            // Proved in range: the exact result is the machine result and is
            // already in canonical (sign- or zero-extended) form.
            IntOp::Unchecked(arith) => {
                let b = values[1];
                let value = match arith {
                    ArithOp::Add => self.builder.ins().iadd(a, b),
                    ArithOp::Sub => self.builder.ins().isub(a, b),
                    ArithOp::Mul => self.builder.ins().imul(a, b),
                };
                // The proof may rest on an operation whose overflow panic a
                // deferred loop has not reported yet. Until it is, keep the
                // value in canonical form like every other narrow value.
                vec![if self.deferred.is_some() && source.bits() < 64 {
                    self.canonical(source, value)
                } else {
                    value
                }]
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
            Pattern::Variant {
                tag,
                fields,
                tagged,
                niche,
            } => {
                let mut result = if let Some(niche) = niche {
                    let (cc, constant) = decoder_test(niche.decoder(*tag));
                    self.builder.ins().icmp_imm_s(cc, values[0], constant)
                } else if *tagged {
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, values[0], *tag as i64)
                } else {
                    self.builder.ins().iconst(ir::types::I8, 1)
                };
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
            Pattern::DynArray {
                element,
                capacity,
                prefix,
                suffix,
                rest,
                ..
            } => {
                let width = self.program.width(*element);
                let length = values[0];
                let required = (prefix.len() + suffix.len()) as i64;
                let mut result = if *rest {
                    self.builder.ins().icmp_imm_s(
                        IntCC::UnsignedGreaterThanOrEqual,
                        length,
                        required,
                    )
                } else {
                    self.builder
                        .ins()
                        .icmp_imm_s(IntCC::Equal, length, required)
                };
                for (index, pattern) in prefix.iter().enumerate() {
                    let field = self.pattern(pattern, &values[1 + index * width..]);
                    result = self.builder.ins().band(result, field);
                }
                for (index, pattern) in suffix.iter().enumerate() {
                    let words = self.dyn_suffix_element(
                        values,
                        width,
                        *capacity,
                        prefix.len(),
                        suffix.len(),
                        index,
                    );
                    let field = self.pattern(pattern, &words);
                    result = self.builder.ins().band(result, field);
                }
                result
            }
        }
    }
    /// Bind a borrowed DynArray pattern over the array at `pointer`. Element
    /// names receive slot addresses, the rest a `&[T]` descriptor, and
    /// by-value element patterns bind copies from the loaded `words`.
    fn bind_borrowed_dyn(&mut self, pattern: &Pattern, pointer: Value, words: &[Value]) {
        let Pattern::DynArray {
            element,
            capacity,
            prefix,
            suffix,
            rest_binding,
            ..
        } = pattern
        else {
            return;
        };
        let width = self.program.width(*element);
        let stride = (width * 8) as i64;
        let length = words[0];
        let data = self.builder.ins().iadd_imm_s(pointer, 8);
        for (index, pattern) in prefix.iter().enumerate() {
            match pattern {
                Pattern::Bind(slot) => {
                    let address = self.builder.ins().iadd_imm_s(data, index as i64 * stride);
                    self.assign(*slot, &[address]);
                }
                pattern => self.bind_pattern(pattern, &words[1 + index * width..]),
            }
        }
        for (index, pattern) in suffix.iter().enumerate() {
            match pattern {
                Pattern::Bind(slot) => {
                    // Slot `length - suffix + index`, computed at run time.
                    let position = self
                        .builder
                        .ins()
                        .iadd_imm_s(length, index as i64 - suffix.len() as i64);
                    let offset = self.builder.ins().imul_imm_s(position, stride);
                    let address = self.builder.ins().iadd(data, offset);
                    self.assign(*slot, &[address]);
                }
                pattern => {
                    let element_words = self.dyn_suffix_element(
                        words,
                        width,
                        *capacity,
                        prefix.len(),
                        suffix.len(),
                        index,
                    );
                    self.bind_pattern(pattern, &element_words);
                }
            }
        }
        if let Some(slot) = rest_binding {
            let start = self
                .builder
                .ins()
                .iadd_imm_s(data, prefix.len() as i64 * stride);
            let middle = self
                .builder
                .ins()
                .iadd_imm_s(length, -((prefix.len() + suffix.len()) as i64));
            let stride = self.constant(stride);
            let bytes = self.constant(0);
            self.assign(*slot, &[start, middle, stride, bytes]);
        }
    }
    /// The words of suffix element `index` of a DynArray pattern: the slot at
    /// `length - suffix + index`, selected over the SSA slots it may occupy
    /// (from `prefix + index` up to `capacity - suffix + index`). When the
    /// length guard fails the selected words are unused.
    fn dyn_suffix_element(
        &mut self,
        values: &[Value],
        width: usize,
        capacity: usize,
        prefix: usize,
        suffix: usize,
        index: usize,
    ) -> Vec<Value> {
        let length = values[0];
        let mut words = vec![self.constant(0); width];
        for slot in prefix + index..=capacity - suffix + index {
            let here =
                self.builder
                    .ins()
                    .icmp_imm_s(IntCC::Equal, length, (slot + suffix - index) as i64);
            for (word, out) in words.iter_mut().enumerate() {
                *out = self
                    .builder
                    .ins()
                    .select(here, values[1 + slot * width + word], *out);
            }
        }
        words
    }
    fn dispose_pattern(&mut self, pattern: &Pattern, ty: Type, values: &[Value]) {
        match pattern {
            Pattern::Any => self.drop_value(ty, values),
            Pattern::Bind(slot) => self.activate_local(*slot),
            Pattern::Variant { tag, fields, .. } => {
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
            Pattern::DynArray { .. } => {}
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
            Pattern::DynArray {
                element,
                capacity,
                prefix,
                suffix,
                rest_binding,
                ..
            } => {
                let width = self.program.width(*element);
                for (index, pattern) in prefix.iter().enumerate() {
                    self.bind_pattern(pattern, &values[1 + index * width..]);
                }
                for (index, pattern) in suffix.iter().enumerate() {
                    let words = self.dyn_suffix_element(
                        values,
                        width,
                        *capacity,
                        prefix.len(),
                        suffix.len(),
                        index,
                    );
                    self.bind_pattern(pattern, &words);
                }
                if let Some(slot) = rest_binding {
                    let zero = self.constant(0);
                    let length = values[0];
                    let mut tail = vec![zero; 1 + width * *capacity];
                    let rest_length = self
                        .builder
                        .ins()
                        .iadd_imm_s(length, -((prefix.len() + suffix.len()) as i64));
                    tail[0] = rest_length;
                    for position in 0..capacity.saturating_sub(prefix.len() + suffix.len()) {
                        let source = prefix.len() + position;
                        // The middle slot `source` is live when it is before
                        // the suffix: `length > source + suffix`.
                        let active = self.builder.ins().icmp_imm_s(
                            IntCC::UnsignedGreaterThan,
                            length,
                            (source + suffix.len()) as i64,
                        );
                        for word in 0..width {
                            let value = values[1 + source * width + word];
                            tail[1 + position * width + word] =
                                self.builder.ins().select(active, value, zero);
                        }
                    }
                    self.assign(*slot, &tail);
                }
            }
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
/// Root local and total word offset of a record-field projection chain.
fn projection_offset(expr: &Expr) -> Option<(usize, usize)> {
    let mut offset = 0usize;
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::Project(base, field) => {
                offset += field;
                current = base;
            }
            ExprKind::Peek(slot)
            | ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::InitOwner { slot, .. } => {
                return Some((*slot, offset));
            }
            _ => return None,
        }
    }
}
/// The temporary-owner initializer at the root of a field projection chain.
fn projection_root_init(expr: &Expr) -> Option<(usize, &Expr)> {
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::Project(base, _) => current = base,
            ExprKind::InitOwner { slot, value } => return Some((*slot, value)),
            _ => return None,
        }
    }
}
fn has_bindings(p: &Pattern) -> bool {
    match p {
        Pattern::Bind(_) => true,
        Pattern::Variant { fields, .. } => fields.iter().any(|(_, p)| has_bindings(p)),
        Pattern::Type { inner, .. } => has_bindings(inner),
        Pattern::Or(ps) => ps.iter().any(has_bindings),
        Pattern::DynArray {
            prefix,
            suffix,
            rest_binding,
            ..
        } => {
            rest_binding.is_some()
                || prefix.iter().any(has_bindings)
                || suffix.iter().any(has_bindings)
        }
        _ => false,
    }
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64"))]
mod scalar_inline_codegen_tests {
    use super::*;

    #[test]
    fn depth_guards_exist_only_in_functions_that_install_handlers() {
        if Command::new("objdump").arg("--version").output().is_err() {
            return;
        }
        let program=ex::check(r#"
            effect Op:i64->i64;
            fn leaf(n:i64)->i64 ! {panic} {let mut i=0;while i<n {i=i+1;if i==2 {continue;}if i==4 {break;}}loop {break i;}}
            fn install()->i64 ! {panic} {
                handle Op:i64->i64 with fn(x:i64,r:linear once fn(i64)->i64 ! {})->i64 ! {} {r(x)} {leaf(8)}
            }
            fn main()->i64 ! {panic} {install()}
        "#).unwrap();
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        for options in [CodegenOptions::default(), CodegenOptions::release()] {
            let path = scratch.path().join("guards.o");
            fs::write(&path, object(&program, options).unwrap()).unwrap();
            for name in ["leaf", "install", "main"] {
                let index = program
                    .functions
                    .iter()
                    .position(|f| f.name.rsplit('.').next() == Some(name))
                    .unwrap();
                let output = Command::new("objdump")
                    .args([
                        "-dr",
                        "--no-show-raw-insn",
                        &format!("--disassemble=kush_fn_{index}"),
                    ])
                    .arg(&path)
                    .output()
                    .unwrap();
                assert!(output.status.success());
                let assembly = String::from_utf8(output.stdout).unwrap();
                assert_eq!(
                    assembly.contains("kush_handler_depth"),
                    name == "install",
                    "{name}: {assembly}"
                );
                assert_eq!(
                    assembly.contains("kush_handler_restore"),
                    name == "install",
                    "{name}: {assembly}"
                );
            }
        }
    }

    #[test]
    fn map_callback_inlining_removes_machine_calls_without_backend_optimization() {
        if Command::new("objdump").arg("--version").output().is_err() {
            eprintln!("objdump unavailable; machine-code inspection skipped");
            return;
        }
        let program = ex::check("fn first(x:i64)->i64 ! {} {x & 255} fn second(x:i64)->i64 ! {} {x ^ 7} fn mapped(v:Vec<i64>)->Vec<i64> ! {} {Vec.map_in_place(Vec.map_in_place(v,first),second)} fn main()->i64 ! {alloc,panic} {let v:Vec<i64> = [1];Vec.get(&mapped(v),0)}").unwrap();
        let index = program
            .functions
            .iter()
            .position(|function| function.name.rsplit('.').next() == Some("mapped"))
            .unwrap();
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let mut calls = Vec::new();
        for enabled in [false, true] {
            let path = scratch.path().join(format!("inline-{enabled}.o"));
            fs::write(
                &path,
                object(
                    &program,
                    CodegenOptions::cranelift(Optimization::None, enabled),
                )
                .unwrap(),
            )
            .unwrap();
            let output = Command::new("objdump")
                .args([
                    "-dr",
                    "--no-show-raw-insn",
                    &format!("--disassemble=kush_fn_{index}"),
                ])
                .arg(&path)
                .output()
                .unwrap();
            assert!(output.status.success());
            let assembly = String::from_utf8(output.stdout).unwrap();
            assert!(
                assembly.contains(&format!("<kush_fn_{index}>:")),
                "{assembly}"
            );
            calls.push(
                assembly
                    .lines()
                    .filter(|line| {
                        line.split_whitespace()
                            .nth(1)
                            .is_some_and(|word| word.starts_with("call"))
                    })
                    .count(),
            );
        }
        assert!(
            calls[0] >= calls[1] + 2,
            "callback calls were not removed: {calls:?}"
        );
    }
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64"))]
mod allocator_runtime_tests {
    use super::*;

    /// References to locals point into native stack slots; every slot must be
    /// created with the contract alignment, never a literal.
    #[test]
    fn every_stack_slot_uses_the_pointer_alignment_contract() {
        let source = include_str!("native.rs");
        let marker = ["StackSlotData", "::new("].concat();
        let mut slots = 0;
        for (start, _) in source.match_indices(&marker) {
            let call = &source[start..start + source[start..].find("));").unwrap()];
            assert!(
                call.contains("STACK_SLOT_ALIGN_SHIFT"),
                "stack slot without the alignment contract: {call}"
            );
            slots += 1;
        }
        assert!(slots >= 17, "{slots}");
        assert_eq!(1u64 << STACK_SLOT_ALIGN_SHIFT, POINTER_ALIGN);
    }

    /// UNBOX-ALIGN-CONTRACT: every allocation path returns a nonzero pointer
    /// that is a multiple of `POINTER_ALIGN`, including pool reuse, growth,
    /// fallible paths, arenas (with and without fresh chunks), allocator
    /// blocks and vector/byte element storage.
    #[test]
    fn every_allocation_path_returns_nonzero_pointer_aligned_storage() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let source = scratch.path().join("alignment-test.c");
        let binary = scratch.path().join("alignment-test");
        let test = r#"
#undef main
#include <assert.h>
int64_t kush_entry(void) { return 0; }
static uint64_t checked = 0;
static void aligned(uint64_t pointer, uint64_t align) {
    assert(pointer != 0);
    assert(pointer % KUSH_POINTER_ALIGN == 0);
    assert(pointer % align == 0);
    ++checked;
}
int main(int argc, char **argv) {
    (void)argc; (void)argv;
    uint64_t live[64];
    for (int round = 0; round < 3; ++round) {
        /* Ordinary boxes: every pool class, the system path, and reuse. */
        for (uint64_t bytes = 0; bytes <= 2 * KUSH_POOL_MAX; bytes += 8) {
            uint64_t p = kush_alloc(bytes);
            aligned(p, KUSH_ALLOC_ALIGN);
            kush_free(p);
        }
        for (int i = 0; i < 64; ++i) { live[i] = kush_alloc((uint64_t)(i * 24)); aligned(live[i], KUSH_ALLOC_ALIGN); }
        for (int i = 0; i < 64; ++i) kush_free(live[i]);
        /* Fallible allocation and growth. */
        uint64_t t = kush_try_alloc(40);
        aligned(t, KUSH_ALLOC_ALIGN);
        void *g = kush_grow((void *)(uintptr_t)t, 5000);
        aligned((uint64_t)(uintptr_t)g, KUSH_ALLOC_ALIGN);
        g = kush_try_grow(g, 9000);
        aligned((uint64_t)(uintptr_t)g, KUSH_ALLOC_ALIGN);
        kush_free((uint64_t)(uintptr_t)g);
        /* Headerless buffers, bytes and vectors (element data included). */
        for (uint64_t bytes = 16; bytes <= 2 * KUSH_POOL_MAX; bytes += 16) {
            uint64_t b = kush_buffer_alloc(bytes, bytes - 16, 0);
            aligned(b, KUSH_ALLOC_ALIGN);
            kush_buffer_free(b);
        }
        for (int64_t capacity = 0; capacity < 3000; capacity += 97) {
            uint64_t b = kush_bytes_with_capacity(capacity);
            aligned(b, KUSH_ALLOC_ALIGN);
            aligned((uint64_t)(uintptr_t)kush_alloc_block_data(b), KUSH_POINTER_ALIGN);
            kush_bytes_free(b);
            uint64_t tb = kush_try_bytes_with_capacity(capacity);
            aligned(tb, KUSH_ALLOC_ALIGN);
            kush_bytes_free(tb);
        }
        uint64_t v = kush_vec_with_capacity(1, 3);
        for (int64_t i = 0; i < 200; ++i) {
            uint64_t words[3] = {(uint64_t)i, 0, 0};
            v = kush_vec_push(v, words, 3);
            KushVec *vec = (KushVec *)(uintptr_t)v;
            aligned(v, KUSH_ALLOC_ALIGN);
            aligned((uint64_t)(uintptr_t)&vec->data[i * 3], KUSH_POINTER_ALIGN);
        }
        kush_buffer_free(v);
        /* Arenas: odd sizes, fresh chunks and the fallible path. */
        uint64_t arena = kush_arena_new();
        aligned(arena, KUSH_ALLOC_ALIGN);
        for (uint64_t bytes = 1; bytes < 3000; bytes += 37) {
            uint64_t a = kush_arena_alloc(arena, bytes);
            aligned(a, KUSH_POINTER_ALIGN);
            uint64_t b = kush_arena_try_alloc(arena, bytes + 3);
            aligned(b, KUSH_POINTER_ALIGN);
            kush_arena_box_release(a);
            kush_arena_box_release(b);
        }
        kush_arena_release(arena);
    }
    kush_pool_drain();
    assert(kush_live_allocations == 0);
    assert(checked > 3000);
    return 0;
}
"#;
        fs::write(
            &source,
            format!("#define main kush_runtime_process_main\n{RUNTIME}\n{test}"),
        )
        .unwrap();
        let output = Command::new("cc")
            .args([
                "-std=c11",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-DKUSH_HAS_TASKS=1",
                "-DKUSH_STATS=1",
                "-DKUSH_FUSION_COUNT=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .arg("-lm")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary)
            .env_remove("KUSH_ALLOC_FAIL_AFTER")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(POINTER_ALIGN, 8);
        assert!(
            RUNTIME.contains("#define KUSH_POINTER_ALIGN ((uint64_t)8)"),
            "the C runtime and POINTER_ALIGN must agree"
        );
    }

    #[test]
    fn headerless_buffers_preserve_growth_capacity_and_typed_release() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let source = scratch.path().join("headerless-test.c");
        let binary = scratch.path().join("headerless-test");
        let test = r#"
#undef main
#include <assert.h>
int64_t kush_entry(void) { return 0; }
int main(int argc, char **argv) {
    if (argc > 1) {
        uint64_t handle=kush_bytes_with_capacity(0), guard=kush_alloc(8);
        (void)argv; (void)guard;
        kush_bytes_free(handle);
        kush_bytes_free(handle);
        return 90;
    }
    assert(sizeof(KushBytes)==16 && sizeof(KushVec)==16);
    uint64_t ordinary[2]={0,UINT64_C(0x7fffffffffffffef)};
    assert(kush_buffer_capacity(ordinary)==UINT64_C(0x7fffffffffffffef));
    kush_buffer_set_capacity(ordinary,UINT64_C(0x7fffffffffffffff));
    assert(kush_buffer_capacity(ordinary)==UINT64_C(0x7fffffffffffffff));
    for (int64_t capacity=0;capacity<=1100;capacity++) {
        uint64_t handle=kush_bytes_with_capacity(capacity);
        KushBytes *b=(KushBytes *)(uintptr_t)handle;
        assert(((uintptr_t)b & 15)==0);
        assert(kush_bytes_capacity(handle)==capacity);
        assert(b->capacity==(uint64_t)capacity);
        for (int64_t i=0;i<capacity;i++) handle=kush_bytes_push(handle,i%256);
        assert(kush_bytes_len(handle)==capacity);
        for (int64_t i=0;i<capacity;i++) assert(kush_bytes_get(handle,i)==i%256);
        handle=kush_bytes_push(handle,42);
        assert(kush_bytes_get(handle,capacity)==42);
        kush_bytes_free(handle);
    }
    kush_pool_drain();
    for(size_t i=0;i<KUSH_POOL_CLASSES;i++) assert(kush_pool_counts[i]==0);
    assert(kush_pool_retained==0 && kush_live_allocations==0);
    uint64_t v=kush_vec_with_capacity(4,4);
    for(int64_t i=0;i<4;i++) {uint64_t words[4]={(uint64_t)i,2,3,4};v=kush_vec_push(v,words,4);}
    /* Emulate a checked narrowing map's compacted slots without changing its
       physical class; logical capacity remains four elements. */
    KushVec *vec=(KushVec *)(uintptr_t)v;
    for(int64_t i=0;i<4;i++) vec->data[i]=(uint64_t)i;
    kush_try_fail_after=0;kush_try_attempts=0;kush_try_probe_initialized=1;
    assert(kush_vec_try_reserve(v,8,1)==v);
    assert(kush_buffer_capacity(vec)==12 && kush_try_attempts==0);
    assert(kush_vec_try_reserve(v,1000,1)==0);
    assert(kush_buffer_capacity(vec)==12);
    kush_try_fail_after=UINT64_MAX;
    uint64_t grown=kush_vec_try_reserve(v,1000,1);
    assert(grown!=0);
    vec=(KushVec *)(uintptr_t)grown;
    assert(!(vec->capacity & KUSH_BUFFER_RAW));
    for(int64_t i=0;i<4;i++) assert(vec->data[i]==(uint64_t)i);
    kush_buffer_free(grown);
    kush_pool_drain();
    assert(kush_pool_retained==0 && kush_live_allocations==0);
    return 0;
}
"#;
        fs::write(
            &source,
            format!("#define main kush_runtime_process_main\n{RUNTIME}\n{test}"),
        )
        .unwrap();
        let output = Command::new("cc")
            .args([
                "-std=c11",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-DKUSH_HAS_TASKS=1",
                "-DKUSH_STATS=1",
                "-DKUSH_FUSION_COUNT=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .arg("-lm")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary)
            .env_remove("KUSH_ALLOC_FAIL_AFTER")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary).arg("double").output().unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
    }

    #[test]
    fn compact_headers_preserve_alignment_markers_growth_and_class_counts() {
        let scratch = Scratch::new(&std::env::temp_dir()).unwrap();
        let source = scratch.path().join("runtime-test.c");
        let binary = scratch.path().join("runtime-test");
        let test = r#"
#undef main
#include <assert.h>
int64_t kush_entry(void) { return 0; }
int main(int argc, char **argv) {
    if (argc > 1) {
        uint64_t first=kush_alloc(8), guard=kush_alloc(8);
        (void)guard;
        if (strcmp(argv[1], "double") == 0) kush_free(first);
        else ((KushAllocHeader *)(uintptr_t)first-1)->magic=0;
        kush_free(first);
        return 90;
    }
    assert(sizeof(KushAllocHeader)==16);
    const uint64_t sizes[]={0,1,16,17,1024,1025};
    for (size_t i=0;i<sizeof(sizes)/sizeof(sizes[0]);i++) {
        uint64_t handle=kush_alloc(sizes[i]);
        assert((handle & 15)==0);
        KushAllocHeader *header=(KushAllocHeader *)(uintptr_t)handle-1;
        assert(kush_block_live(header));
        assert(header->magic==(sizes[i]<=1024 ? KUSH_ALLOC_MAGIC : KUSH_ALLOC_UNPOOLED));
        memset((void *)(uintptr_t)handle,0x5a,(size_t)sizes[i]);
        void *grown=kush_grow((void *)(uintptr_t)handle,sizes[i]+2048);
        assert(((uintptr_t)grown & 15)==0);
        for (uint64_t j=0;j<sizes[i];j++) assert(((unsigned char *)grown)[j]==0x5a);
        kush_free((uint64_t)(uintptr_t)grown);
    }
    kush_pool_drain();
    uint64_t owner=kush_alloc(17);
    KushAllocHeader *header=(KushAllocHeader *)(uintptr_t)owner-1;
    header->magic=0;
    assert(kush_try_grow((void *)(uintptr_t)owner,64)==NULL);
    header->magic=KUSH_ALLOC_MAGIC;
    kush_free(owner);
    owner=kush_try_alloc(17);
    assert(owner!=0 && ((KushAllocHeader *)(uintptr_t)owner-1)->magic==KUSH_ALLOC_MAGIC);
    kush_free(owner);
    kush_pool_drain();
    uint64_t blocks[128];
    for (size_t i=0;i<128;i++) blocks[i]=kush_alloc(1);
    for (size_t i=0;i<128;i++) kush_free(blocks[i]);
    assert(kush_pool_counts[0]==KUSH_POOL_CLASS_CAP);
    assert(kush_pool_retained==KUSH_POOL_CLASS_CAP*32);
    for (size_t i=0;i<64;i++) blocks[i]=kush_try_alloc(1);
    assert(kush_pool_counts[0]==0 && kush_pool_retained==0);
    for (size_t i=0;i<64;i++) kush_free(blocks[i]);
    kush_pool_drain();
    for (size_t i=0;i<KUSH_POOL_CLASSES;i++) assert(kush_pool_counts[i]==0);
    assert(kush_pool_retained==0 && kush_live_allocations==0);
    return 0;
}
"#;
        fs::write(
            &source,
            format!("#define main kush_runtime_process_main\n{RUNTIME}\n{test}"),
        )
        .unwrap();
        let output = Command::new("cc")
            .args([
                "-std=c11",
                "-O2",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-DKUSH_HAS_TASKS=1",
                "-DKUSH_STATS=1",
                "-DKUSH_FUSION_COUNT=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .arg("-lm")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let output = Command::new(&binary)
            .env_remove("KUSH_ALLOC_FAIL_AFTER")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        for argument in ["double", "corrupt"] {
            let output = Command::new(&binary).arg(argument).output().unwrap();
            assert!(!output.status.success());
            assert!(String::from_utf8_lossy(&output.stderr).contains("panic:"));
        }
    }
}
