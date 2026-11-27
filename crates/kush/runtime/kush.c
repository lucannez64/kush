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
#include <arpa/inet.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
extern char **environ;
extern int64_t kush_entry(void);
/* THREAD-SCOPE: a program that runs OS threads is built with
   KUSH_HAS_THREADS: shared counters become atomic, and allocator pools,
   handler stacks, the current task and the abort word become per thread.
   Single-threaded programs keep the plain paths. */
#if defined(KUSH_HAS_THREADS) || defined(KUSH_MAIN_STACK)
#include <pthread.h>
#endif
#ifdef KUSH_HAS_THREADS
#define KUSH_TLS _Thread_local
#define KUSH_ADD(x, n) __atomic_add_fetch(&(x), (n), __ATOMIC_RELAXED)
#define KUSH_SUB(x, n) __atomic_sub_fetch(&(x), (n), __ATOMIC_RELAXED)
#else
#define KUSH_TLS
#define KUSH_ADD(x, n) ((x) += (n))
#define KUSH_SUB(x, n) ((x) -= (n))
#endif
/* Diagnostic/error-path writes intentionally do not retry or alter control
   flow on failure. Assign the result so fortified libc headers also accept
   the explicit best-effort policy under -Werror. */
static void kush_best_effort_write(int fd, const void *data, size_t length) {
    ssize_t result = write(fd, data, length);
    (void)result;
}
/* PROOF-FUZZ (docs/proof-fuzz.md): a fuzz build (-DKUSH_FUZZ=1) counts how
   often each run-time check the prover left in place (an obligation site)
   runs, keeps the smallest distance from failing it saw, and remembers the
   site being checked. Generated code calls kush_fuzz_enter or
   kush_fuzz_arith just before the checked operation and kush_fuzz_leave
   after it, so a panic inside it names its site. The table is written to
   $KUSH_FUZZ_OUT at exit and on every panic. Ordinary builds contain none of
   this. Attribution assumes one thread runs Kush code at a time. */
#ifdef KUSH_FUZZ
typedef struct { uint64_t hits; int64_t margin; } KushFuzzSite;
static KushFuzzSite kush_fuzz_sites[KUSH_FUZZ_SITES > 0 ? KUSH_FUZZ_SITES : 1];
static int64_t kush_fuzz_current = -1;
static int kush_fuzz_written = 0;
static const char *kush_fuzz_path = NULL;
#include <sys/resource.h>
static void kush_fuzz_init(void) {
    /* A fuzz run that panics aborts; a core dump of every such run (with a
       large main stack, hundreds of milliseconds each) is never wanted. */
    struct rlimit no_core = { 0, 0 };
    (void)setrlimit(RLIMIT_CORE, &no_core);
    for (int64_t i = 0; i < KUSH_FUZZ_SITES; ++i) kush_fuzz_sites[i].margin = INT64_MAX;
    kush_fuzz_path = getenv("KUSH_FUZZ_OUT");
}
/* failed: a site id, -1 for a normal exit, -2 for a panic outside every
   site, -3 for stack exhaustion. Only async-signal-safe calls. */
static void kush_fuzz_write(int64_t failed) {
    if (kush_fuzz_written || kush_fuzz_path == NULL) return;
    kush_fuzz_written = 1;
    int fd = open(kush_fuzz_path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) return;
    int64_t header[3];
    memcpy(&header[0], "KUSHFUZ1", 8);
    header[1] = failed;
    header[2] = (int64_t)KUSH_FUZZ_SITES;
    kush_best_effort_write(fd, header, sizeof(header));
    kush_best_effort_write(fd, kush_fuzz_sites, sizeof(KushFuzzSite) * (size_t)KUSH_FUZZ_SITES);
    close(fd);
}
static void kush_fuzz_margin(int64_t margin) {
    if (kush_fuzz_current >= 0 && margin < kush_fuzz_sites[kush_fuzz_current].margin)
        kush_fuzz_sites[kush_fuzz_current].margin = margin;
}
void kush_fuzz_enter(int64_t site) {
    if (site < 0 || site >= KUSH_FUZZ_SITES) return;
    kush_fuzz_current = site;
    kush_fuzz_sites[site].hits += 1;
}
void kush_fuzz_leave(void) { kush_fuzz_current = -1; }
static int64_t kush_fuzz_clamp(__int128 value) {
    return value > INT64_MAX ? INT64_MAX : value < INT64_MIN ? INT64_MIN : (int64_t)value;
}
/* code: operation in bits 0..7 (0 +, 1 -, 2 *, 3 /, 4 %, 5 <<, 6 >>,
   7 unary -), the left type's width in bits 8..15, its signedness in bit
   16, the right operand's signedness in bit 17. The margin is how far the
   exact result is from the type's range (or the divisor from zero, or the
   shift amount from 0..width); negative means this operation fails. */
void kush_fuzz_arith(int64_t site, int64_t code, int64_t a, int64_t b) {
    kush_fuzz_enter(site);
    int op = (int)(code & 255), bits = (int)((code >> 8) & 255);
    int is_signed = (int)((code >> 16) & 1), right_signed = (int)((code >> 17) & 1);
    __int128 lo = is_signed ? -((__int128)1 << (bits - 1)) : 0;
    __int128 hi = is_signed ? ((__int128)1 << (bits - 1)) - 1 : ((__int128)1 << bits) - 1;
    __int128 x = is_signed ? (__int128)a : (__int128)(uint64_t)a;
    __int128 y = is_signed ? (__int128)b : (__int128)(uint64_t)b;
    __int128 r = 0;
    int64_t margin;
    switch (op) {
    case 0: r = x + y; break;
    case 1: r = x - y; break;
    case 7: r = -x; break;
    case 2:
        if (!is_signed && bits == 64) {
            unsigned __int128 p = (unsigned __int128)(uint64_t)a * (uint64_t)b;
            kush_fuzz_margin(p > (unsigned __int128)hi ? -1 : kush_fuzz_clamp((__int128)((unsigned __int128)hi - p)));
            return;
        }
        r = x * y;
        break;
    case 3: case 4:
        if (y == 0 || (is_signed && x == lo && y == -1)) margin = -1;
        else margin = kush_fuzz_clamp((y < 0 ? -y : y) - 1);
        kush_fuzz_margin(margin);
        return;
    default: {
        __int128 amount = right_signed ? (__int128)b : (__int128)(uint64_t)b;
        if (amount < 0 || amount >= bits) margin = -1;
        else margin = kush_fuzz_clamp(amount < bits - 1 - amount ? amount : bits - 1 - amount);
        kush_fuzz_margin(margin);
        return;
    }
    }
    margin = (r < lo || r > hi) ? -1 : kush_fuzz_clamp(r - lo < hi - r ? r - lo : hi - r);
    kush_fuzz_margin(margin);
}
/* An element access: record how far `index` is from leaving 0..length. */
#define KUSH_FUZZ_INDEX(index, length) \
    kush_fuzz_margin((index) < 0 || (uint64_t)(index) >= (uint64_t)(length) ? -1 \
        : kush_fuzz_clamp((__int128)(index) < (__int128)(length) - 1 - (index) \
            ? (__int128)(index) : (__int128)(length) - 1 - (index)))
#else
#define KUSH_FUZZ_INDEX(index, length) ((void)0)
#endif
/* PANIC-UNWIND-NATIVE (docs/panic-unwinding.md): when a catch boundary is
   active, a failed precondition sets the panic word and returns `value`
   (which the generated caller never uses: it tests the word and unwinds);
   otherwise it panics as before. Only for preconditions on the program's
   values, checked before anything is changed or consumed. */
static int kush_panic_unwinds(void);
static void kush_raise_panic(void);
static int64_t *kush_panic_word(void);
void kush_unwind_rethrow(void);
/* PANIC-UNWIND-USE: set on an OS thread started by Thread.spawn, whose body
   is a boundary of its own; the Task.catch depth of such a thread. */
static KUSH_TLS int kush_in_thread = 0;
static KUSH_TLS int kush_thread_catch_depth = 0;
/* FND-ROWS-PANIC: allocator release callbacks and arena strategies run
   inside runtime bookkeeping that never tests the panic word, so a panic in
   them aborts instead of unwinding. The depth is per task (and per thread
   for a thread body), next to the catch depth. */
#ifdef KUSH_UNWIND
static KUSH_TLS int kush_thread_nounwind_depth = 0;
#endif
static void kush_nounwind_enter(void);
static void kush_nounwind_leave(void);
#define KUSH_FAIL(value) do { if (kush_panic_unwinds()) { kush_raise_panic(); return value; } kush_panic(); } while (0)
#define KUSH_FAIL_VOID() do { if (kush_panic_unwinds()) { kush_raise_panic(); return; } kush_panic(); } while (0)
_Noreturn void kush_panic(void) {
#ifdef KUSH_FUZZ
    kush_fuzz_write(kush_fuzz_current >= 0 ? kush_fuzz_current : -2);
#endif
    static const char message[] = "panic: checked arithmetic, memory, or I/O failure\n";
    kush_best_effort_write(2, message, sizeof(message) - 1);
    /* A panic a catch boundary could stop unwinds instead (KUSH_FAIL,
       kush_unwind_panic); one that reaches here checks the runtime's own
       invariants, or has no boundary, and ends the process. */
#ifdef KUSH_FUZZ
    /* No abort(): a system core handler would run for every panicking
       input. The status is the one abort() gives a shell. */
    _exit(134);
#endif
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
#ifdef KUSH_FUZZ
        kush_fuzz_write(-3);
#endif
        static const char message[] = "panic: stack exhausted\n";
        kush_best_effort_write(2, message, sizeof(message) - 1);
#ifdef KUSH_FUZZ
        _exit(134);
#endif
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
/* A program's main may run on a thread with a larger stack
   (`#[stack_size(N)]`). That thread gets its own signal stack, and the
   ceiling moves to its first frame. */
#ifdef KUSH_MAIN_STACK
static void kush_stack_guard_thread(void *signal_stack, size_t size) {
    stack_t stack;
    memset(&stack, 0, sizeof(stack));
    stack.ss_sp = signal_stack;
    stack.ss_size = size;
    if (sigaltstack(&stack, NULL) != 0) kush_panic();
    kush_stack_ceiling = (uintptr_t)__builtin_frame_address(0);
}
#endif
#else
static void kush_stack_guard_init(void) {}
#ifdef KUSH_MAIN_STACK
static void kush_stack_guard_thread(void *signal_stack, size_t size) {
    (void)signal_stack;
    (void)size;
}
#endif
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
        if (count <= 0) KUSH_FAIL(0);
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
        if (count <= 0) KUSH_FAIL(0);
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
        if (count <= 0) KUSH_FAIL_VOID();
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
    uint64_t live = KUSH_ADD(kush_live_allocations, 1);
    KUSH_ADD(kush_allocations, 1);
#ifdef KUSH_HAS_THREADS
    uint64_t peak = __atomic_load_n(&kush_peak_live, __ATOMIC_RELAXED);
    while (live > peak
           && !__atomic_compare_exchange_n(&kush_peak_live, &peak, live, 1,
                                           __ATOMIC_RELAXED, __ATOMIC_RELAXED)) {
    }
#else
    if (live > kush_peak_live) kush_peak_live = live;
#endif
}
static void kush_note_deallocation(void) {
#ifdef KUSH_HAS_THREADS
    if (__atomic_fetch_sub(&kush_live_allocations, 1, __ATOMIC_RELAXED) == 0) kush_panic();
#else
    if (kush_live_allocations == 0) kush_panic();
    --kush_live_allocations;
#endif
    KUSH_ADD(kush_deallocations, 1);
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
static KUSH_TLS KushAllocHeader *kush_pool_lists[KUSH_POOL_CLASSES];
/* Headerless ordinary buffers have their own intrusive lists. Both families
   share the existing per-class count and global physical-byte budget. */
static KUSH_TLS uint64_t *kush_buffer_lists[KUSH_POOL_CLASSES];
static KUSH_TLS size_t kush_pool_counts[KUSH_POOL_CLASSES];
static KUSH_TLS uint64_t kush_pool_retained = 0;
static KUSH_TLS uint64_t kush_pool_peak_retained = 0;
static KUSH_TLS uint64_t kush_pool_hits = 0;
static KUSH_TLS uint64_t kush_pool_misses = 0;
static KUSH_TLS uint64_t kush_pool_retains = 0;
static KUSH_TLS uint64_t kush_pool_releases = 0;
static KUSH_TLS uint64_t kush_pool_drains = 0;
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
        KUSH_ADD(kush_try_attempts, 1);
        return 1;
    }
    KUSH_ADD(kush_try_attempts, 1);
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
int64_t kush_note_reuse(void) { KUSH_ADD(kush_reuses, 1); return 0; }
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
        kush_nounwind_enter();
        uint64_t chosen = arena->strategy(need, current);
        kush_nounwind_leave();
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
    if (capacity < 0 || (uint64_t)capacity > KUSH_MAX_CAPACITY) KUSH_FAIL(0);
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
    kush_nounwind_enter();
    ((KushContextFreeFn)(uintptr_t)state->release)(state->state, block);
    kush_nounwind_leave();
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
    kush_nounwind_enter();
    ((KushFreeBlockFn)(uintptr_t)release)(block);
    kush_nounwind_leave();
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
    v->block = block; v->capacity = next; KUSH_ADD(kush_buffer_growths, 1);
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
    v->block = block; v->capacity = next; KUSH_ADD(kush_buffer_growths, 1);
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
    if (v->length == 0) {
        if (kush_panic_unwinds()) memset(out, 0, (size_t)(v->width * 8));
        KUSH_FAIL_VOID();
    }
    uint64_t index = --v->length;
    memcpy(out, kush_alloc_block_data(v->block) + index * v->width * 8,
           (size_t)(v->width * 8));
}
int64_t kush_alloc_vec_len(uint64_t handle) {
    return (int64_t)((KushAllocVec *)(uintptr_t)handle)->length;
}
void kush_alloc_vec_get(uint64_t handle, int64_t index, uint64_t *out) {
    KushAllocVec *v = (KushAllocVec *)(uintptr_t)handle;
    KUSH_FUZZ_INDEX(index, v->length);
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
    KUSH_FUZZ_INDEX(index, v->length);
    if (index < 0 || (uint64_t)index >= v->length) {
        if (kush_panic_unwinds()) memset(old, 0, (size_t)(v->width * 8));
        KUSH_FAIL(handle);
    }
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
    KUSH_FUZZ_INDEX(index, b->length);
    if (index < 0 || (uint64_t)index >= b->length) KUSH_FAIL(0);
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
    /* The buffer was moved into the push: free it before failing. */
    if (value < 0 || value > 255) { if (kush_panic_unwinds()) kush_bytes_free(handle); KUSH_FAIL(0); }
    if (b->length == b->capacity) {
        if (!grow) { if (kush_panic_unwinds()) kush_bytes_free(handle); KUSH_FAIL(0); }
        uint64_t next = b->capacity == 0 ? 8 : (b->capacity <= KUSH_MAX_CAPACITY / 2 ? b->capacity * 2 : KUSH_MAX_CAPACITY);
        if (next <= b->capacity || next > KUSH_MAX_CAPACITY) kush_panic();
        kush_bytes_encode(b);
        b = (KushBytes *)kush_buffer_grow(b, sizeof(KushBytes) + next);
        b->capacity = next; KUSH_ADD(kush_buffer_growths, 1);
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
    if (!kush_utf8_valid_data(b->data, b->length)) KUSH_FAIL(0);
    int64_t count = 0;
    for (uint64_t i = 0; i < b->length; ++i) {
        if ((b->data[i] & 0xC0) != 0x80) ++count;
    }
    return count;
}
/* Scalar-indexed code point, or -1 when the scalar index is out of range. */
int64_t kush_utf8_scalar_at(uint64_t handle, int64_t index) {
    KushBytes *b = (KushBytes *)(uintptr_t)handle;
    if (!kush_utf8_valid_data(b->data, b->length)) KUSH_FAIL(-1);
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
    if (index < 0 || index >= length) KUSH_FAIL(0);
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
    if (index < 0 || index >= length || (data[index] & 0xC0) == 0x80) KUSH_FAIL(0);
    unsigned char lead = data[index];
    int64_t width = lead < 0x80 ? 1 : (lead & 0xE0) == 0xC0 ? 2 : (lead & 0xF0) == 0xE0 ? 3 : 4;
    int64_t wanted = code < 0x80 ? 1 : code < 0x800 ? 2 : code < 0x10000 ? 3 : 4;
    if (width != wanted || index + width > length) KUSH_FAIL(0);
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
/* ---- std.sys stubs (STD-SYS-FOREIGN) --------------------------------------
   One system call each, imported by `std.sys` through the foreign bridge ABI
   and callable only from std (the checker reserves `kush_sys_*`). A stub
   returns 0 or the positive errno (EINTR included: retry policy is Kush code)
   and writes a payload through `out`.
   Paths arrive as (pointer, length) and are copied into a C string here, the
   only marshalling the bridge cannot express. */
static char *kush_sys_path(const uint8_t *data, int64_t length, int *code) {
    if (length < 0 || memchr(data, 0, (size_t)length) != NULL) { *code = EINVAL; return NULL; }
    char *text = (char *)malloc((size_t)length + 1);
    if (text == NULL) { *code = ENOMEM; return NULL; }
    memcpy(text, data, (size_t)length);
    text[length] = 0;
    return text;
}
int64_t kush_sys_openat(const uint8_t *path, int64_t path_len, int64_t flags, int64_t mode, int64_t *out) {
    int code = 0;
    char *text = kush_sys_path(path, path_len, &code);
    if (text == NULL) return code;
    int fd = openat(AT_FDCWD, text, (int)flags | O_CLOEXEC, (mode_t)mode);
    code = fd < 0 ? errno : 0;
    free(text);
    if (code == 0) *out = fd;
    return code;
}
int64_t kush_sys_close(int64_t fd) {
    /* Linux releases the descriptor even when close reports EINTR. */
    return close((int)fd) != 0 && errno != EINTR ? errno : 0;
}
int64_t kush_sys_fsync(int64_t fd) { return fsync((int)fd) != 0 ? errno : 0; }
int64_t kush_sys_ftruncate(int64_t fd, int64_t length) {
    if (length < 0) return EINVAL;
    return ftruncate((int)fd, (off_t)length) != 0 ? errno : 0;
}
int64_t kush_sys_fstat_size(int64_t fd, int64_t *out) {
    struct stat info;
    if (fstat((int)fd, &info) != 0) return errno;
    *out = (int64_t)info.st_size;
    return 0;
}
/* Write data[start..] once; `offset` < 0 means the current file position. */
int64_t kush_sys_write(int64_t fd, const uint8_t *data, int64_t length, int64_t start, int64_t offset, int64_t *out) {
    if (start < 0 || start > length) return EINVAL;
    ssize_t written = offset < 0
        ? write((int)fd, data + start, (size_t)(length - start))
        : pwrite((int)fd, data + start, (size_t)(length - start), (off_t)offset);
    if (written < 0) return errno;
    *out = (int64_t)written;
    return 0;
}
/* One read of up to `length` bytes into the spare capacity of the owned
   buffer (FOREIGN-BYTES-FILL), at `offset` (pread) or at the file position
   when `offset` < 0 (read). The buffer comes back through `out` with its
   length advanced, or is freed on failure, so EINTR is retried here: the
   caller cannot retry with a buffer it no longer has. Room for `length` more
   bytes is required up front (EFBIG otherwise). */
int64_t kush_sys_read(int64_t fd, uint64_t buffer_handle, int64_t length, int64_t offset, uint64_t *out) {
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    int64_t code = 0;
    if (length < 0) code = EINVAL;
    else if ((uint64_t)length > b->capacity - b->length) code = EFBIG;
    ssize_t received = 0;
    while (code == 0) {
        received = offset < 0
            ? read((int)fd, b->data + b->length, (size_t)length)
            : pread((int)fd, b->data + b->length, (size_t)length, (off_t)offset);
        if (received >= 0) break;
        if (errno != EINTR) code = errno;
    }
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    b->length += (uint64_t)received;
    *out = buffer_handle;
    return 0;
}
/* Fill `length` more bytes of the owned buffer's spare capacity from the
   kernel's random generator (getrandom(2), which blocks only until the pool
   is first seeded). Short reads and EINTR are retried here, since a failed
   call frees the buffer; EFBIG when the buffer lacks room (WEB-CRYPTO). */
#include <sys/random.h>
int64_t kush_sys_getrandom(uint64_t buffer_handle, int64_t length, uint64_t *out) {
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    int64_t code = 0;
    if (length < 0) code = EINVAL;
    else if ((uint64_t)length > b->capacity - b->length) code = EFBIG;
    int64_t filled = 0;
    while (code == 0 && filled < length) {
        ssize_t received = getrandom(b->data + b->length + filled, (size_t)(length - filled), 0);
        if (received >= 0) filled += received;
        else if (errno != EINTR) code = errno;
    }
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    b->length += (uint64_t)length;
    *out = buffer_handle;
    return 0;
}
/* SIMD-X86-SHA: the x86 SHA instructions, one routine each, for std.x86.
   Only reached with a cpu.Sha token, which std.cpu hands out only when
   CPUID reports SHA, SSSE3 and SSE4.1. */
#include <immintrin.h>
#define KUSH_SHA __attribute__((target("sha,sse4.1,ssse3")))
KUSH_SHA __m128i kush_x86_sha256rnds2(__m128i cdgh, __m128i abef, __m128i wk) {
    return _mm_sha256rnds2_epu32(cdgh, abef, wk);
}
KUSH_SHA __m128i kush_x86_sha256msg1(__m128i a, __m128i b) { return _mm_sha256msg1_epu32(a, b); }
KUSH_SHA __m128i kush_x86_sha256msg2(__m128i a, __m128i b) { return _mm_sha256msg2_epu32(a, b); }
KUSH_SHA __m128i kush_x86_sha1rnds4_0(__m128i a, __m128i b) { return _mm_sha1rnds4_epu32(a, b, 0); }
KUSH_SHA __m128i kush_x86_sha1rnds4_1(__m128i a, __m128i b) { return _mm_sha1rnds4_epu32(a, b, 1); }
KUSH_SHA __m128i kush_x86_sha1rnds4_2(__m128i a, __m128i b) { return _mm_sha1rnds4_epu32(a, b, 2); }
KUSH_SHA __m128i kush_x86_sha1rnds4_3(__m128i a, __m128i b) { return _mm_sha1rnds4_epu32(a, b, 3); }
KUSH_SHA __m128i kush_x86_sha1nexte(__m128i a, __m128i b) { return _mm_sha1nexte_epu32(a, b); }
KUSH_SHA __m128i kush_x86_sha1msg1(__m128i a, __m128i b) { return _mm_sha1msg1_epu32(a, b); }
KUSH_SHA __m128i kush_x86_sha1msg2(__m128i a, __m128i b) { return _mm_sha1msg2_epu32(a, b); }
/* Cranelift lowers a byte shuffle to this libcall when the target lacks
   SSSE3, as the portable x86-64 baseline does (SIMD-NATIVE): pshufb in
   software. A clear top bit selects the byte at the low four bits. */
#include <emmintrin.h>
__m128i __cranelift_x86_pshufb(__m128i table, __m128i index) {
    unsigned char t[16], m[16], r[16];
    _mm_storeu_si128((__m128i *)t, table);
    _mm_storeu_si128((__m128i *)m, index);
    for (int i = 0; i < 16; ++i) r[i] = (m[i] & 0x80) ? 0 : t[m[i] & 15];
    return _mm_loadu_si128((const __m128i *)r);
}
/* CPU features for std.cpu (SIMD-CPU), as bits: 1 SSSE3, 2 SSE4.1, 4 AVX2,
   8 SHA. Detected once with CPUID; AVX2 also needs the OS to save YMM state
   (OSXSAVE and XGETBV). KUSH_CPU_DISABLE=sha,avx2,... clears features so
   tests can run the portable paths natively. */
#include <cpuid.h>
static int64_t kush_cpu_feature_bits = -1;
static int kush_cpu_disabled(const char *name) {
    const char *list = getenv("KUSH_CPU_DISABLE");
    if (list == NULL) return 0;
    size_t length = strlen(name);
    for (const char *p = list; *p != 0;) {
        const char *end = strchr(p, ',');
        size_t n = end == NULL ? strlen(p) : (size_t)(end - p);
        if (n == length && strncmp(p, name, n) == 0) return 1;
        if (end == NULL) break;
        p = end + 1;
    }
    return 0;
}
/* Threads may race to fill the cache; every one computes the same bits, and
   atomic accesses make the race defined (SIMD-REVIEW). */
int64_t kush_sys_cpu_features(int64_t *out) {
    int64_t cached = __atomic_load_n(&kush_cpu_feature_bits, __ATOMIC_ACQUIRE);
    if (cached < 0) {
        unsigned int a = 0, b = 0, c = 0, d = 0;
        int64_t bits = 0;
        if (__get_cpuid(1, &a, &b, &c, &d)) {
            unsigned int leaf1_ecx = c;
            if (leaf1_ecx & (1u << 9)) bits |= 1;   /* SSSE3 */
            if (leaf1_ecx & (1u << 19)) bits |= 2;  /* SSE4.1 */
            int ymm = 0;
            if ((leaf1_ecx & (1u << 27)) && (leaf1_ecx & (1u << 28))) {
                unsigned int lo, hi;
                __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
                ymm = (lo & 6u) == 6u;
            }
            if (__get_cpuid_count(7, 0, &a, &b, &c, &d)) {
                if (ymm && (b & (1u << 5))) bits |= 4;  /* AVX2 */
                if (b & (1u << 29)) bits |= 8;          /* SHA */
            }
        }
        if (kush_cpu_disabled("ssse3")) bits &= ~1;
        if (kush_cpu_disabled("sse41")) bits &= ~2;
        if (kush_cpu_disabled("avx2")) bits &= ~4;
        if (kush_cpu_disabled("sha")) bits &= ~8;
        __atomic_store_n(&kush_cpu_feature_bits, bits, __ATOMIC_RELEASE);
        cached = bits;
    }
    *out = cached;
    return 0;
}
/* The standard input descriptor. A separate call (not the constant 0) so the
   reference evaluator can tell which programs read standard input. */
int64_t kush_sys_stdin(int64_t *out) { *out = 0; return 0; }
/* Read and discard up to one byte at the file position: the count tells a
   caller whose buffer is full whether more data follows (EINTR retried). */
int64_t kush_sys_probe(int64_t fd, int64_t *out) {
    unsigned char probe;
    for (;;) {
        ssize_t received = read((int)fd, &probe, 1);
        if (received >= 0) { *out = (int64_t)received; return 0; }
        if (errno != EINTR) return errno;
    }
}
/* opendir(3); the DIR pointer is the handle. */
int64_t kush_sys_opendir(const uint8_t *path, int64_t path_len, int64_t *out) {
    int code = 0;
    char *text = kush_sys_path(path, path_len, &code);
    if (text == NULL) return code;
    DIR *directory = opendir(text);
    code = directory == NULL ? errno : 0;
    free(text);
    if (code == 0) *out = (int64_t)(uintptr_t)directory;
    return code;
}
/* readdir(3) once, skipping "." and "..": append the next entry name and a
   newline to the owned buffer (EFBIG and freed when it does not fit). At the
   end of the directory the buffer comes back unchanged. */
int64_t kush_sys_readdir(int64_t handle, uint64_t buffer_handle, uint64_t *out) {
    DIR *directory = (DIR *)(uintptr_t)handle;
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    int64_t code = 0;
    for (;;) {
        errno = 0;
        struct dirent *entry = readdir(directory);
        if (entry == NULL) { code = errno; break; }
        const char *name = entry->d_name;
        if (strcmp(name, ".") == 0 || strcmp(name, "..") == 0) continue;
        uint64_t length = (uint64_t)strlen(name);
        if (b->length > b->capacity || length + 1 > b->capacity - b->length) { code = EFBIG; break; }
        memcpy(b->data + b->length, name, (size_t)length);
        b->data[b->length + length] = '\n';
        b->length += length + 1;
        break;
    }
    if (code != 0) { kush_bytes_free(buffer_handle); return code; }
    *out = buffer_handle;
    return 0;
}
int64_t kush_sys_closedir(int64_t handle) {
    return closedir((DIR *)(uintptr_t)handle) != 0 ? errno : 0;
}
int64_t kush_sys_unlink(const uint8_t *path, int64_t path_len) {
    int code = 0;
    char *text = kush_sys_path(path, path_len, &code);
    if (text == NULL) return code;
    code = unlink(text) != 0 ? errno : 0;
    free(text);
    return code;
}
int64_t kush_sys_mkdir(const uint8_t *path, int64_t path_len, int64_t mode) {
    int code = 0;
    char *text = kush_sys_path(path, path_len, &code);
    if (text == NULL) return code;
    code = mkdir(text, (mode_t)mode) != 0 ? errno : 0;
    free(text);
    return code;
}
int64_t kush_sys_rmdir(const uint8_t *path, int64_t path_len) {
    int code = 0;
    char *text = kush_sys_path(path, path_len, &code);
    if (text == NULL) return code;
    code = rmdir(text) != 0 ? errno : 0;
    free(text);
    return code;
}
int64_t kush_sys_rename(const uint8_t *from, int64_t from_len, const uint8_t *to, int64_t to_len) {
    int code = 0;
    char *a = kush_sys_path(from, from_len, &code);
    if (a == NULL) return code;
    char *b = kush_sys_path(to, to_len, &code);
    if (b == NULL) { free(a); return code; }
    code = rename(a, b) != 0 ? errno : 0;
    free(a); free(b);
    return code;
}
/* stat(2) one field: 0 = st_mode, 1 = st_size. */
int64_t kush_sys_stat(const uint8_t *path, int64_t path_len, int64_t field, int64_t *out) {
    int code = 0;
    char *text = kush_sys_path(path, path_len, &code);
    if (text == NULL) return code;
    struct stat info;
    code = stat(text, &info) != 0 ? errno : 0;
    free(text);
    if (code != 0) return code;
    if (field == 0) *out = (int64_t)info.st_mode;
    else if (field == 1) *out = (int64_t)info.st_size;
    else return EINVAL;
    return 0;
}
/* Append `length` bytes to an owned buffer, or free it: EFBIG when full. */
static int64_t kush_sys_append_owned(uint64_t buffer_handle, const char *text, uint64_t *out) {
    KushBytes *b = (KushBytes *)(uintptr_t)buffer_handle;
    uint64_t length = (uint64_t)strlen(text);
    if (b->length > b->capacity || length > b->capacity - b->length) {
        kush_bytes_free(buffer_handle);
        return EFBIG;
    }
    memcpy(b->data + b->length, text, (size_t)length);
    b->length += length;
    *out = buffer_handle;
    return 0;
}
int64_t kush_sys_argc(int64_t *out) {
    *out = kush_host_argc < 0 ? 0 : kush_host_argc;
    return 0;
}
/* Append argv[index]; ENOENT when out of range. */
int64_t kush_sys_argv(int64_t index, uint64_t buffer_handle, uint64_t *out) {
    if (index < 0 || index >= (int64_t)kush_host_argc || kush_host_argv == NULL) {
        kush_bytes_free(buffer_handle);
        return ENOENT;
    }
    return kush_sys_append_owned(buffer_handle, kush_host_argv[index], out);
}
/* Number of environ entries of the form NAME=VALUE. */
int64_t kush_sys_environ_count(int64_t *out) {
    int64_t count = 0;
    if (environ != NULL) {
        for (char **entry = environ; *entry != NULL; ++entry) {
            if (strchr(*entry, '=') != NULL) ++count;
        }
    }
    *out = count;
    return 0;
}
/* getenv(3), appending the value; ENOENT when unset. */
int64_t kush_sys_getenv(const uint8_t *name, int64_t name_len, uint64_t buffer_handle, uint64_t *out) {
    int code = 0;
    char *text = kush_sys_path(name, name_len, &code);
    if (text == NULL) { kush_bytes_free(buffer_handle); return code; }
    const char *value = getenv(text);
    free(text);
    if (value == NULL) { kush_bytes_free(buffer_handle); return ENOENT; }
    return kush_sys_append_owned(buffer_handle, value, out);
}
/* clock_gettime(2): clock 0 = realtime, 1 = monotonic; field 0 = whole
   seconds, 1 = nanoseconds since the clock's origin (EOVERFLOW if huge). */
int64_t kush_sys_clock_gettime(int64_t clock, int64_t field, int64_t *out) {
    struct timespec now;
    if (clock != 0 && clock != 1) return EINVAL;
    if (clock_gettime(clock == 0 ? CLOCK_REALTIME : CLOCK_MONOTONIC, &now) != 0) return errno;
    if (field == 0) { *out = (int64_t)now.tv_sec; return 0; }
    if (field == 2) {
        if (now.tv_sec < 0 || (uint64_t)now.tv_sec > (uint64_t)INT64_MAX / 1000 - 1) return EOVERFLOW;
        *out = (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
        return 0;
    }
    if (field != 1) return EINVAL;
    if (now.tv_sec < 0 || (uint64_t)now.tv_sec > (uint64_t)INT64_MAX / UINT64_C(1000000000)) return EOVERFLOW;
    uint64_t seconds = (uint64_t)now.tv_sec * UINT64_C(1000000000);
    if (seconds > (uint64_t)INT64_MAX - (uint64_t)now.tv_nsec) return EOVERFLOW;
    *out = (int64_t)(seconds + (uint64_t)now.tv_nsec);
    return 0;
}
/* nanosleep(2) for `milliseconds` >= 0, resuming with the remaining time
   after EINTR (the kernel reports it; a caller-side retry would restart). */
int64_t kush_sys_nanosleep(int64_t milliseconds) {
    if (milliseconds < 0) return EINVAL;
    struct timespec request;
    request.tv_sec = (time_t)(milliseconds / 1000);
    request.tv_nsec = (long)((milliseconds % 1000) * 1000000);
    while (nanosleep(&request, &request) != 0) {
        if (errno != EINTR) return errno;
    }
    return 0;
}
/* strerror(3) text for 0 <= code <= 4095, appended. */
int64_t kush_sys_strerror(int64_t code, uint64_t buffer_handle, uint64_t *out) {
    if (code < 0 || code > 4095) { kush_bytes_free(buffer_handle); return EINVAL; }
    const char *text = strerror((int)code);
    return kush_sys_append_owned(buffer_handle, text == NULL ? "Unknown error" : text, out);
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
    return fd >= 0 && fd < KUSH_MAX_FILES
        && (__atomic_load_n(&kush_open_files[fd / 8], __ATOMIC_SEQ_CST) >> (fd % 8)) & 1;
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
    __atomic_fetch_or(&kush_open_files[fd / 8], (unsigned char)(1u << (fd % 8)), __ATOMIC_SEQ_CST);
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
    __atomic_fetch_and(&kush_open_files[fd / 8], (unsigned char)~(1u << (fd % 8)), __ATOMIC_SEQ_CST);
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
/* STD-PROC-NET-IN-KUSH: one-call stubs for std.proc and std.net. Timeouts,
   partial reads and retries are Kush code over these. */
/* pipe2(O_CLOEXEC); the read end plus the write end times 2^32. */
int64_t kush_sys_pipe(int64_t *out) {
    int ends[2];
    if (pipe2(ends, O_CLOEXEC) != 0) return errno;
    *out = (int64_t)ends[0] + ((int64_t)ends[1] << 32);
    return 0;
}
/* fork and execvp `program` with the NUL-separated `arguments` (empty
   segments skipped), stdin and stderr on /dev/null and stdout on `stdout_fd`.
   Waits only until the exec has happened: an exec failure is reaped and
   returned as its errno. The child's pid otherwise. */
int64_t kush_sys_spawn(const uint8_t *program, int64_t program_len,
                       const uint8_t *arguments, int64_t arguments_len,
                       int64_t stdout_fd, int64_t *out) {
    if (program_len <= 0 || arguments_len < 0) return EINVAL;
    int code = 0;
    char *path = kush_sys_path(program, program_len, &code);
    if (path == NULL) return code;
    uint64_t total = 1;
    for (int64_t i = 0, start = 0; i <= arguments_len; ++i) {
        if (i == arguments_len || arguments[i] == 0) {
            if (i > start) ++total;
            start = i + 1;
        }
    }
    char **argv = (char **)calloc((size_t)total + 1, sizeof(char *));
    if (argv == NULL) { free(path); return ENOMEM; }
    argv[0] = path;
    uint64_t count = 1;
    for (int64_t i = 0, start = 0; i <= arguments_len; ++i) {
        if (i == arguments_len || arguments[i] == 0) {
            if (i > start) {
                char *text = (char *)malloc((size_t)(i - start) + 1);
                if (text == NULL) { code = ENOMEM; break; }
                memcpy(text, arguments + start, (size_t)(i - start));
                text[i - start] = 0;
                argv[count++] = text;
            }
            start = i + 1;
        }
    }
    int report[2] = {-1, -1};
    pid_t child = -1;
    if (code == 0 && pipe2(report, O_CLOEXEC) != 0) code = errno;
    if (code == 0) {
        child = fork();
        if (child < 0) code = errno;
    }
    if (child == 0) {
        int devnull = open("/dev/null", O_RDWR);
        if (devnull >= 0) {
            (void)dup2(devnull, 0);
            (void)dup2(devnull, 2);
            if (devnull > 2) (void)close(devnull);
        }
        if ((int)stdout_fd != 1) (void)dup2((int)stdout_fd, 1);
        else (void)fcntl(1, F_SETFD, 0);
        (void)close(report[0]);
        execvp(argv[0], argv);
        int failure = errno;
        kush_best_effort_write(report[1], &failure, sizeof(failure));
        _exit(127);
    }
    if (report[1] >= 0) (void)close(report[1]);
    if (child > 0) {
        /* The report pipe closes on exec (EOF) or carries the exec errno. */
        int failure = 0;
        ssize_t received;
        do { received = read(report[0], &failure, sizeof(failure)); }
        while (received < 0 && errno == EINTR);
        if (received == (ssize_t)sizeof(failure)) {
            int status = 0;
            kush_host_reap(child, &status);
            code = failure;
        }
    }
    if (report[0] >= 0) (void)close(report[0]);
    for (uint64_t i = 0; i < count; ++i) free(argv[i]);
    free(argv);
    if (code != 0) return code;
    *out = (int64_t)child;
    return 0;
}
/* waitpid(2), blocking or not: -1 while the child runs, else its exit
   status, or 128 + signal. */
int64_t kush_sys_wait(int64_t pid, int64_t block, int64_t *out) {
    int status = 0;
    pid_t result = waitpid((pid_t)pid, &status, block ? 0 : WNOHANG);
    if (result < 0) return errno;
    if (result == 0) { *out = -1; return 0; }
    if (WIFEXITED(status)) *out = WEXITSTATUS(status);
    else if (WIFSIGNALED(status)) *out = 128 + WTERMSIG(status);
    else return EIO;
    return 0;
}
int64_t kush_sys_kill(int64_t pid, int64_t signal) {
    if (pid <= 0) return EINVAL;
    return kill((pid_t)pid, (int)signal) != 0 ? errno : 0;
}
/* poll(2) on one descriptor for up to `timeout_ms` (-1 forever): the
   returned events, 0 on timeout. Events: 1 POLLIN, 4 POLLOUT, 8 POLLERR,
   16 POLLHUP. */
int64_t kush_sys_poll(int64_t fd, int64_t events, int64_t timeout_ms, int64_t *out) {
    if (timeout_ms < -1 || timeout_ms > INT32_MAX) return EINVAL;
    struct pollfd waiting = { (int)fd, (short)events, 0 };
    int ready = poll(&waiting, 1, (int)timeout_ms);
    if (ready < 0) return errno;
    *out = ready == 0 ? 0 : (int64_t)(unsigned short)waiting.revents;
    return 0;
}
static int64_t kush_sys_resolve_type(const uint8_t *host, int64_t host_len, int64_t port, int family,
                                     int socktype, int64_t *out) {
    if (port < 0 || port > 65535) return EINVAL;
    int code = 0;
    char *text = kush_sys_path(host, host_len, &code);
    if (text == NULL) return code;
    if (!kush_utf8_valid_data((const unsigned char *)text, (uint64_t)host_len)) {
        free(text);
        return EINVAL;
    }
    char service[8];
    (void)snprintf(service, sizeof(service), "%lld", (long long)port);
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = family;
    hints.ai_socktype = socktype;
    struct addrinfo *addresses = NULL;
    int resolved = getaddrinfo(text, service, &hints, &addresses);
    free(text);
    if (resolved != 0) {
        int failure = resolved == EAI_MEMORY ? ENOMEM : resolved == EAI_SYSTEM ? errno : EINVAL;
        return failure == 0 ? EINVAL : failure;
    }
    *out = (int64_t)(uintptr_t)addresses;
    return 0;
}
/* getaddrinfo(3) for a TCP connection to host:port; the list is the handle
   for kush_sys_connect and must be freed with kush_sys_resolve_free. */
int64_t kush_sys_resolve(const uint8_t *host, int64_t host_len, int64_t port, int64_t *out) {
    return kush_sys_resolve_type(host, host_len, port, AF_UNSPEC, SOCK_STREAM, out);
}
/* getaddrinfo(3) for UDP: kush_sys_socket makes datagram sockets from this
   list, and kush_sys_sendto sends to its addresses. */
int64_t kush_sys_resolve_udp(const uint8_t *host, int64_t host_len, int64_t port, int64_t *out) {
    return kush_sys_resolve_type(host, host_len, port, AF_UNSPEC, SOCK_DGRAM, out);
}
/* kush_sys_resolve_udp for IPv6 only: no IPv4-mapped addresses, so a name
   with no AAAA record is an error. */
int64_t kush_sys_resolve_udp6(const uint8_t *host, int64_t host_len, int64_t port, int64_t *out) {
    return kush_sys_resolve_type(host, host_len, port, AF_INET6, SOCK_DGRAM, out);
}
int64_t kush_sys_resolve_free(int64_t list) {
    freeaddrinfo((struct addrinfo *)(uintptr_t)list);
    return 0;
}
/* Connect to address `index` of a resolved list, waiting up to `timeout_ms`
   (-1 forever). ENOENT past the end of the list. The socket comes back in
   blocking mode: reads follow a poll, and kush_sys_send never blocks. */
int64_t kush_sys_connect(int64_t list, int64_t index, int64_t timeout_ms, int64_t *out) {
    if (index < 0 || timeout_ms < -1) return EINVAL;
    struct addrinfo *address = (struct addrinfo *)(uintptr_t)list;
    for (int64_t i = 0; address != NULL && i < index; ++i) address = address->ai_next;
    if (address == NULL) return ENOENT;
    int64_t deadline = timeout_ms < 0 ? -1 : timeout_ms == 0 ? 0 : kush_host_deadline(timeout_ms);
    int64_t fd = kush_host_connect(address, deadline);
    if (fd < 0) return -fd;
    int flags = fcntl((int)fd, F_GETFL, 0);
    if (flags < 0 || fcntl((int)fd, F_SETFL, flags & ~O_NONBLOCK) < 0) {
        int failure = errno; (void)close((int)fd); return failure;
    }
    *out = fd;
    return 0;
}
/* One nonblocking send(2) of data[start..] (EAGAIN when the socket is full,
   no SIGPIPE): the count sent. */
int64_t kush_sys_send(int64_t fd, const uint8_t *data, int64_t length, int64_t start, int64_t *out) {
    if (start < 0 || start > length) return EINVAL;
    ssize_t sent = send((int)fd, data + start, (size_t)(length - start), MSG_NOSIGNAL | MSG_DONTWAIT);
    if (sent < 0) return errno;
    *out = (int64_t)sent;
    return 0;
}
/* shutdown(2): 0 read side, 1 write side, 2 both. */
int64_t kush_sys_shutdown(int64_t fd, int64_t how) {
    if (how < 0 || how > 2) return EINVAL;
    return shutdown((int)fd, (int)how) != 0 ? errno : 0;
}
/* WEB-NET: server sockets, one call each; std.net builds Listener and Conn
   on them. Address `index` of a resolved list as in kush_sys_connect. */
static struct addrinfo *kush_sys_address(int64_t list, int64_t index) {
    struct addrinfo *address = (struct addrinfo *)(uintptr_t)list;
    for (int64_t i = 0; address != NULL && i < index; ++i) address = address->ai_next;
    return index < 0 ? NULL : address;
}
/* A blocking socket of the family and type of address `index`: TCP for a
   kush_sys_resolve list, UDP for a kush_sys_resolve_udp one. */
int64_t kush_sys_socket(int64_t list, int64_t index, int64_t *out) {
    struct addrinfo *address = kush_sys_address(list, index);
    if (address == NULL) return ENOENT;
    int fd = socket(address->ai_family, address->ai_socktype | SOCK_CLOEXEC, address->ai_protocol);
    if (fd < 0) return errno;
    *out = fd;
    return 0;
}
/* One nonblocking sendto(2) of all of `data` to address `index` of a
   resolved list (ENOENT past its end; EAGAIN when the socket is full, no
   SIGPIPE): the count sent. A datagram is never sent in part. */
int64_t kush_sys_sendto(int64_t fd, const uint8_t *data, int64_t length, int64_t list, int64_t index,
                        int64_t *out) {
    struct addrinfo *address = kush_sys_address(list, index);
    if (address == NULL) return ENOENT;
    ssize_t sent = sendto((int)fd, data, (size_t)length, MSG_NOSIGNAL | MSG_DONTWAIT, address->ai_addr,
                          address->ai_addrlen);
    if (sent < 0) return errno;
    *out = (int64_t)sent;
    return 0;
}
/* Append address `index` of a resolved list as text (inet_ntop, without
   the port) to the owned buffer, which is freed on failure: ENOENT past the
   end of the list, EFBIG when the text does not fit. */
int64_t kush_sys_address_text(int64_t list, int64_t index, uint64_t buffer_handle, uint64_t *out) {
    struct addrinfo *address = kush_sys_address(list, index);
    if (address == NULL) { kush_bytes_free(buffer_handle); return ENOENT; }
    char text[INET6_ADDRSTRLEN];
    const void *ip = NULL;
    if (address->ai_family == AF_INET) ip = &((struct sockaddr_in *)address->ai_addr)->sin_addr;
    else if (address->ai_family == AF_INET6) ip = &((struct sockaddr_in6 *)address->ai_addr)->sin6_addr;
    else { kush_bytes_free(buffer_handle); return EAFNOSUPPORT; }
    if (inet_ntop(address->ai_family, ip, text, sizeof(text)) == NULL) {
        int failure = errno;
        kush_bytes_free(buffer_handle);
        return failure;
    }
    return kush_sys_append_owned(buffer_handle, text, out);
}
/* One connect(2) of an existing socket to address `index` of a resolved
   list (ENOENT past its end). For a UDP socket it only picks the peer and
   the route; nothing is sent. */
int64_t kush_sys_connect_to(int64_t fd, int64_t list, int64_t index) {
    struct addrinfo *address = kush_sys_address(list, index);
    if (address == NULL) return ENOENT;
    return connect((int)fd, address->ai_addr, address->ai_addrlen) != 0 ? errno : 0;
}
/* Append the socket's local address as text (getsockname, inet_ntop, no
   port) to the owned buffer, which is freed on failure. */
int64_t kush_sys_local_address(int64_t fd, uint64_t buffer_handle, uint64_t *out) {
    struct sockaddr_storage address;
    socklen_t length = sizeof(address);
    char text[INET6_ADDRSTRLEN];
    const void *ip = NULL;
    if (getsockname((int)fd, (struct sockaddr *)&address, &length) != 0) {
        int failure = errno;
        kush_bytes_free(buffer_handle);
        return failure;
    }
    if (address.ss_family == AF_INET) ip = &((struct sockaddr_in *)&address)->sin_addr;
    else if (address.ss_family == AF_INET6) ip = &((struct sockaddr_in6 *)&address)->sin6_addr;
    else { kush_bytes_free(buffer_handle); return EAFNOSUPPORT; }
    if (inet_ntop(address.ss_family, ip, text, sizeof(text)) == NULL) {
        int failure = errno;
        kush_bytes_free(buffer_handle);
        return failure;
    }
    return kush_sys_append_owned(buffer_handle, text, out);
}
/* setsockopt(2) with an int value. */
int64_t kush_sys_setsockopt(int64_t fd, int64_t level, int64_t name, int64_t value) {
    if (value < INT32_MIN || value > INT32_MAX) return EINVAL;
    int option = (int)value;
    return setsockopt((int)fd, (int)level, (int)name, &option, sizeof(option)) != 0 ? errno : 0;
}
int64_t kush_sys_bind(int64_t fd, int64_t list, int64_t index) {
    struct addrinfo *address = kush_sys_address(list, index);
    if (address == NULL) return ENOENT;
    return bind((int)fd, address->ai_addr, address->ai_addrlen) != 0 ? errno : 0;
}
/* listen(2), and make the listener nonblocking: `accept` is EAGAIN when
   another waiter took the connection or it was reset in the queue. */
int64_t kush_sys_listen(int64_t fd, int64_t backlog) {
    if (backlog < 0 || backlog > INT32_MAX) return EINVAL;
    if (listen((int)fd, (int)backlog) != 0) return errno;
    int flags = fcntl((int)fd, F_GETFL, 0);
    if (flags < 0 || fcntl((int)fd, F_SETFL, flags | O_NONBLOCK) != 0) return errno;
    return 0;
}
/* Start connecting a new nonblocking socket to address `index` of a
   resolved list (ENOENT past its end). Wait until it is writable, then call
   kush_sys_connect_finish. */
int64_t kush_sys_connect_start(int64_t list, int64_t index, int64_t *out) {
    struct addrinfo *address = kush_sys_address(list, index);
    if (address == NULL) return ENOENT;
    int fd = socket(address->ai_family, address->ai_socktype | SOCK_CLOEXEC | SOCK_NONBLOCK,
                    address->ai_protocol);
    if (fd < 0) return errno;
    if (connect(fd, address->ai_addr, address->ai_addrlen) != 0 && errno != EINPROGRESS) {
        int code = errno;
        (void)close(fd);
        return code;
    }
    *out = fd;
    return 0;
}
/* The connection's outcome (SO_ERROR); on success the socket goes back to
   blocking mode, like kush_sys_connect's. */
int64_t kush_sys_connect_finish(int64_t fd) {
    int error = 0;
    socklen_t length = sizeof(error);
    if (getsockopt((int)fd, SOL_SOCKET, SO_ERROR, &error, &length) != 0) return errno;
    if (error != 0) return error;
    int flags = fcntl((int)fd, F_GETFL, 0);
    if (flags < 0 || fcntl((int)fd, F_SETFL, flags & ~O_NONBLOCK) != 0) return errno;
    return 0;
}
/* accept4(2) with SOCK_CLOEXEC: a blocking connected socket. */
int64_t kush_sys_accept(int64_t fd, int64_t *out) {
    int accepted = accept4((int)fd, NULL, NULL, SOCK_CLOEXEC);
    if (accepted < 0) return errno;
    *out = accepted;
    return 0;
}
/* The local port of a bound socket (getsockname). */
int64_t kush_sys_local_port(int64_t fd, int64_t *out) {
    struct sockaddr_storage address;
    socklen_t length = sizeof(address);
    if (getsockname((int)fd, (struct sockaddr *)&address, &length) != 0) return errno;
    if (address.ss_family == AF_INET) *out = ntohs(((struct sockaddr_in *)&address)->sin_port);
    else if (address.ss_family == AF_INET6) *out = ntohs(((struct sockaddr_in6 *)&address)->sin6_port);
    else return EAFNOSUPPORT;
    return 0;
}
/* Vectors store fixed-width elements of `width` 64-bit words each. */
typedef struct { uint64_t length; uint64_t capacity; uint64_t data[]; } KushVec;
static uint64_t kush_vec_bytes(uint64_t capacity, uint64_t width) {
    if (width == 0 || capacity > ((uint64_t)INT64_MAX - sizeof(KushVec)) / 8 / width) kush_panic();
    return sizeof(KushVec) + capacity * width * 8;
}
uint64_t kush_vec_with_capacity(int64_t capacity, int64_t width) {
    if (capacity < 0 || width <= 0) KUSH_FAIL(0);
    KushVec *v = (KushVec *)(uintptr_t)kush_buffer_alloc(kush_vec_bytes((uint64_t)capacity, (uint64_t)width), (uint64_t)capacity, 0);
    v->length = 0;
    return (uint64_t)(uintptr_t)v;
}
int64_t kush_vec_len(uint64_t handle) { return (int64_t)((KushVec *)(uintptr_t)handle)->length; }
void kush_vec_get(uint64_t handle, int64_t index, uint64_t *out, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    KUSH_FUZZ_INDEX(index, v->length);
    if (index < 0 || (uint64_t)index >= v->length) {
        if (kush_panic_unwinds()) memset(out, 0, (size_t)(width * 8));
        KUSH_FAIL_VOID();
    }
    memcpy(out, v->data + (uint64_t)index * width, (size_t)(width * 8));
}
uint64_t kush_vec_push(uint64_t handle, const uint64_t *item, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    if (v->length == kush_buffer_capacity(v)) {
        uint64_t next = kush_buffer_capacity(v) == 0 ? 4 : kush_buffer_capacity(v) * 2;
        if (next <= kush_buffer_capacity(v)) kush_panic();
        uint64_t bytes = kush_vec_bytes(next, width);
        v = (KushVec *)kush_buffer_grow(v, bytes);
        kush_buffer_set_capacity(v, next); KUSH_ADD(kush_buffer_growths, 1);
    }
    memcpy(v->data + v->length * width, item, (size_t)(width * 8));
    v->length++;
    return (uint64_t)(uintptr_t)v;
}
uint64_t kush_vec_set(uint64_t handle, int64_t index, const uint64_t *item, uint64_t *old, uint64_t width) {
    KushVec *v = (KushVec *)(uintptr_t)handle;
    KUSH_FUZZ_INDEX(index, v->length);
    if (index < 0 || (uint64_t)index >= v->length) {
        /* The item stays with the caller's cleanup; the vector is unchanged. */
        if (kush_panic_unwinds()) memset(old, 0, (size_t)(width * 8));
        KUSH_FAIL(handle);
    }
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
    KUSH_FUZZ_INDEX(index, v->length);
    if (index < 0 || (uint64_t)index >= v->length) KUSH_FAIL((uint64_t)(uintptr_t)v->data);
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
    KUSH_ADD(kush_buffer_growths, 1);
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
    KUSH_ADD(kush_buffer_growths, 1);
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
    if (replacement != v) KUSH_ADD(kush_buffer_growths, 1);
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
/* These tables are emitted by native/staging.rs. Graph bytes never supply
   machine code, relocation offsets, or native symbol addresses. */
typedef struct {
    uint64_t offset, kind, target_kind, target;
    int64_t addend;
    uintptr_t address;
} KushStageReloc;
typedef struct {
    uint64_t id, size;
    const unsigned char *code;
    uint64_t reloc_count;
    const KushStageReloc *relocs;
    uintptr_t original;
} KushStageBody;
typedef struct { uint64_t schema, body, captures; } KushStageSchema;
typedef struct {
    uint64_t body_count, schema_count;
    const KushStageBody *bodies;
    const KushStageSchema *schemas;
    uint64_t function_count;
    const uint64_t *functions;
} KushStageImage;
extern const KushStageImage kush_stage_image __attribute__((weak));
#define KUSH_STAGE_LIMIT (64u * 1024u * 1024u)
typedef struct { unsigned char *base; size_t used; int error; } KushStageLink;
typedef struct { const unsigned char *next; size_t left; } KushStageReader;
typedef struct { uint64_t value, stub; uintptr_t entry; } KushStageCapture;

static const unsigned char *kush_stage_take(KushStageReader *r, uint64_t size) {
    if (size > r->left) return NULL;
    const unsigned char *bytes = r->next;
    r->next += size;
    r->left -= size;
    return bytes;
}
static int kush_stage_word(KushStageReader *r, uint64_t *value) {
    const unsigned char *bytes = kush_stage_take(r, 8);
    if (bytes == NULL) return 0;
    memcpy(value, bytes, 8);
    return 1;
}
static unsigned char *kush_stage_space(KushStageLink *link, uint64_t size) {
    size_t at = (link->used + 15) & ~(size_t)15;
    if (at > KUSH_STAGE_LIMIT || size > KUSH_STAGE_LIMIT - at) {
        link->error = E2BIG;
        return NULL;
    }
    link->used = at + size;
    return link->base + at;
}
static int kush_stage_patch(KushStageLink *link, const KushStageBody *body,
                            unsigned char *code, const KushStageCapture *captures,
                            size_t count, uint64_t *constants) {
    for (size_t i = 0; i < body->reloc_count; ++i) {
        const KushStageReloc *rel = &body->relocs[i];
        uintptr_t target = rel->address;
        switch (rel->target_kind) {
        case 0:
            if (rel->target == body->id) target = (uintptr_t)code;
            for (size_t j = 0; j < count; ++j)
                if (captures[j].entry && captures[j].stub == rel->target)
                    target = captures[j].entry;
            break;
        case 1:
            break;
        case 2:
            if (rel->target != body->id || rel->address >= body->size) return 0;
            target = (uintptr_t)code + rel->address;
            break;
        case 3:
            if ((rel->target >> 32) != body->id || (uint32_t)rel->target >= count) return 0;
            target = (uintptr_t)&constants[(uint32_t)rel->target];
            break;
        default:
            return 0;
        }
        size_t width = rel->kind == 0 ? 8 : 4;
        if (rel->offset > body->size || width > body->size - rel->offset) return 0;
        unsigned char *site = code + rel->offset;
        if (rel->kind == 0) {
            target += rel->addend;
            memcpy(site, &target, 8);
            continue;
        }
        if (rel->kind == 3) {
            unsigned char *slot = kush_stage_space(link, 8);
            if (slot == NULL) return 0;
            memcpy(slot, &target, 8);
            target = (uintptr_t)slot;
        }
        int64_t distance = (int64_t)(target + rel->addend - (uintptr_t)site);
        if (rel->kind == 2 && (distance < INT32_MIN || distance > INT32_MAX)) {
            unsigned char *thunk = kush_stage_space(link, 13);
            if (thunk == NULL) return 0;
            /* movabs r11, target; jmp r11. r11 is caller-saved. */
            thunk[0] = 0x49; thunk[1] = 0xbb;
            memcpy(thunk + 2, &target, 8);
            thunk[10] = 0x41; thunk[11] = 0xff; thunk[12] = 0xe3;
            distance = (int64_t)((uintptr_t)thunk + rel->addend - (uintptr_t)site);
        }
        if (rel->kind > 3 || distance < INT32_MIN || distance > INT32_MAX) return 0;
        int32_t displacement = (int32_t)distance;
        memcpy(site, &displacement, 4);
    }
    return 1;
}

static uintptr_t kush_stage_node(KushStageLink *link, KushStageReader reader, unsigned depth) {
    const KushStageImage *image = &kush_stage_image;
    if (depth >= 128) { link->error = E2BIG; return 0; }
    const unsigned char *magic = kush_stage_take(&reader, 8);
    uint64_t id, count = 0;
    if (magic == NULL || memcmp(magic, "KUSHCD0", 7) != 0 ||
        magic[7] < '1' || magic[7] > '3' || !kush_stage_word(&reader, &id) ||
        (magic[7] != '1' && !kush_stage_word(&reader, &count))) return 0;
    const KushStageSchema *schema = NULL;
    for (size_t i = 0; i < image->schema_count; ++i)
        if (image->schemas[i].schema == id) { schema = &image->schemas[i]; break; }
    if (schema == NULL || count != schema->captures || count > reader.left) return 0;
    const KushStageBody *body = NULL;
    for (size_t i = 0; i < image->body_count; ++i)
        if (image->bodies[i].id == schema->body) { body = &image->bodies[i]; break; }
    if (body == NULL) return 0;
    KushStageCapture *captures = count ? calloc((size_t)count, sizeof(*captures)) : NULL;
    if (count && captures == NULL) { link->error = ENOMEM; return 0; }
    uintptr_t result = 0;
    for (size_t i = 0; i < count; ++i) {
        const unsigned char *tag = magic[7] == '3' ? kush_stage_take(&reader, 1) : NULL;
        if (magic[7] == '3' && tag == NULL) goto done;
        if (tag == NULL || *tag == 0) {
            if (!kush_stage_word(&reader, &captures[i].value)) goto done;
        } else if (*tag == 1 || *tag == 2) {
            uint64_t stub = 0, size;
            if ((*tag == 1 && (!kush_stage_word(&reader, &stub) || stub >= image->function_count)) ||
                !kush_stage_word(&reader, &size)) goto done;
            const unsigned char *bytes = kush_stage_take(&reader, size);
            if (bytes == NULL) goto done;
            if (*tag == 1) {
                captures[i].stub = image->functions[stub];
                captures[i].entry = kush_stage_node(link, (KushStageReader){bytes, size}, depth + 1);
                if (captures[i].entry == 0) goto done;
            } else {
                KushBytes *literal = (KushBytes *)kush_stage_space(link, sizeof(*literal) + size);
                if (literal == NULL) goto done;
                literal->length = literal->capacity = size;
                memcpy(literal->data, bytes, size);
                captures[i].value = (uintptr_t)literal;
            }
        } else goto done;
    }
    if (reader.left != 0) goto done;
    uint64_t *constants = (uint64_t *)kush_stage_space(link, count * 8);
    unsigned char *code = kush_stage_space(link, body->size);
    if (constants == NULL || code == NULL) goto done;
    for (size_t i = 0; i < count; ++i) constants[i] = captures[i].value;
    memcpy(code, body->code, body->size);
    if (kush_stage_patch(link, body, code, captures, count, constants)) result = (uintptr_t)code;
done:
    free(captures);
    return result;
}

typedef struct {
    void *mapping;
    uint64_t mapping_size;
    void *entry;
} KushStageCompiled;
uint64_t kush_stage_release(uint64_t handle) {
    KushStageCompiled *owner = (KushStageCompiled *)(uintptr_t)handle;
    if (owner->mapping != NULL) munmap(owner->mapping, (size_t)owner->mapping_size);
    kush_free(handle);
    return 0;
}
uint64_t kush_stage_compile(uint64_t graph, uint64_t *owner) {
    *owner = 0;
    const KushBytes *buffer = (const KushBytes *)(uintptr_t)graph;
    int status = ENOTSUP;
    if (&kush_stage_image == NULL) goto done;
    status = E2BIG;
    if (buffer->length > 16u * 1024u * 1024u) goto done;
    uint64_t handle = kush_try_alloc(sizeof(KushStageCompiled));
    status = ENOMEM;
    if (handle == 0) goto done;
    KushStageCompiled *compiled = (KushStageCompiled *)(uintptr_t)handle;
    compiled->mapping = mmap(NULL, KUSH_STAGE_LIMIT, PROT_READ | PROT_WRITE,
                             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    compiled->mapping_size = KUSH_STAGE_LIMIT;
    if (compiled->mapping == MAP_FAILED) {
        status = errno;
        kush_free(handle);
        goto done;
    }
    KushStageLink link = {compiled->mapping, 0, ENOTSUP};
    uintptr_t entry = kush_stage_node(&link, (KushStageReader){buffer->data, buffer->length}, 0);
    status = link.error;
    if (entry) {
        __builtin___clear_cache((char *)link.base, (char *)link.base + link.used);
        if (mprotect(link.base, link.used, PROT_READ | PROT_EXEC) == 0) {
            compiled->entry = (void *)entry;
            *owner = handle;
            status = 0;
        } else status = errno;
    }
    if (status != 0) kush_stage_release(handle);
done:
    kush_bytes_free(graph);
    return (uint64_t)status;
}
/* Task slots are reused: a handle is the slot plus one in its low 32 bits and
   the slot's generation in its high 32 bits, so a handle to a joined task
   never names the task that later takes its slot. A scope lists only its
   live children (join removes the child), so a scope cannot reach a task
   that reuses a joined child's slot. The bound is live tasks, set by memory. */
#define KUSH_MAX_SCOPES 16
#define KUSH_MAX_SLOTS (1 << 30)
#define KUSH_TASK_STACK (256u * 1024u)
enum { KUSH_READY = 0, KUSH_RUNNING = 1, KUSH_BLOCKED = 2, KUSH_FINISHED = 3 };
typedef struct KushTask KushTask;
struct KushHandlerContext;
struct KushTask {
    ucontext_t context;
    uint64_t id, handle, wrapper, code, env;
    void *result;
    size_t result_size;
    void (*drop)(void *);
    int state, cancelled, joined, completed, preserve;
    KushTask *waiter;
    /* The parent scope frame that lists this task, and its neighbours in
       that frame's list of unjoined children (in spawn order). */
    KushTask *parent, *previous_sibling, *next_sibling;
    int parent_depth;
    KushTask *scope_first[KUSH_MAX_SCOPES];
    KushTask *scope_last[KUSH_MAX_SCOPES];
    int scope_depth;
    /* Allocated on first use; the root task uses the static root context. */
    struct KushHandlerContext *handlers;
    void *stack_base;
    size_t stack_total;
    /* WEB-REACTOR: a task parked in kush_sys_wait_ready. wait_fd is its own
       duplicate of the descriptor, registered one-shot with epoll (-1 for a
       pure timer); wait_deadline is in monotonic ms (-1 for none);
       wait_result is the events, 0 on timeout, -1 when cancelled. */
    int waiting_io, wait_fd, wait_shielded;
    /* PANIC-UNWIND-USE: active Task.catch bodies in this task, and whether a
       panic unwound the whole task (its join raises it again). */
    int catch_depth, panicked;
    /* FND-ROWS-PANIC: runtime callbacks in progress where a panic aborts. */
    int nounwind_depth;
    int64_t wait_deadline, wait_result;
    KushTask *wait_previous, *wait_next;
};
/* Slot table: kush_task_count slots have ever been used, freed ones are on
   kush_free_slots. Runtime bookkeeping uses malloc, not kush_alloc, so the
   allocation statistics count only task stacks, control blocks and results.
   THREAD-TASKS: every OS thread runs its own scheduler, so all of its state
   is per thread; a thread's tasks never leave it (task handles cannot cross
   a thread boundary), and the thread tears its scheduler down at its end. */
static KUSH_TLS KushTask **kush_tasks = NULL;
static KUSH_TLS uint32_t *kush_task_generations = NULL;
static KUSH_TLS int *kush_free_slots = NULL;
static KUSH_TLS int kush_free_count = 0;
static KUSH_TLS int kush_task_capacity = 0;
static KUSH_TLS int kush_task_count = 0;
static KUSH_TLS KushTask *kush_current = NULL;
static KUSH_TLS ucontext_t kush_scheduler_context;
static KUSH_TLS void *kush_scheduler_stack = NULL;
static KUSH_TLS size_t kush_scheduler_stack_total = 0;
static KUSH_TLS int kush_initialized = 0;
/* Ready queue of task handles, a ring that doubles when full. */
static KUSH_TLS uint64_t *kush_ready = NULL;
static KUSH_TLS int kush_ready_capacity = 0;
static KUSH_TLS int kush_ready_head = 0, kush_ready_tail = 0, kush_ready_count = 0;
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
/* Continuation stack of multishot tokens (docs/multishot-capabilities.md):
   environments of `multi fn` tokens are bump-allocated in chunks, and every
   token call and multishot `handle` restores the top it saw on entry. */
typedef struct KushKChunk KushKChunk;
struct KushKChunk {
    KushKChunk *previous;
    uint64_t base;      /* bytes in use below this chunk */
    uint64_t capacity;
    uint64_t padding;
    unsigned char data[];
};
#define KUSH_KCHUNK ((uint64_t)64 * 1024)
typedef struct {
    KushKChunk *chunk;
    unsigned char *top;
    KushKChunk *spare;
} kush_kstack;
typedef struct KushHandlerContext {
    kush_handler_frame frames[KUSH_HANDLER_MAX];
    int64_t depth;
    kush_kstack kstack;
} kush_handler_context;
/* The root task's context, also used before the task runtime starts. */
static kush_handler_context kush_root_handlers;
#ifdef KUSH_HAS_THREADS
/* A child OS thread has its own handler stack (it inherits no frames). */
static KUSH_TLS kush_handler_context *kush_thread_handlers = NULL;
#endif
static kush_handler_context *kush_handlers(void) {
    KushTask *task = kush_current;
    if (task == NULL || task->id == 0) {
#ifdef KUSH_HAS_THREADS
        /* A thread's root (its body) uses the thread's stack; the tasks it
           spawns have their own, as on the main thread (THREAD-TASKS). */
        if (kush_thread_handlers != NULL) return kush_thread_handlers;
#endif
        return &kush_root_handlers;
    }
    if (task->handlers == NULL) {
        task->handlers = (kush_handler_context *)calloc(1, sizeof(kush_handler_context));
        if (task->handlers == NULL) kush_panic();
    }
    return task->handlers;
}
static int kush_kstack_poison_flag = -1;
static uint64_t kush_kstack_peak = 0;
static int kush_kstack_poisoning(void) {
    if (kush_kstack_poison_flag < 0)
        kush_kstack_poison_flag = getenv("KUSH_KSTACK_POISON") != NULL;
    return kush_kstack_poison_flag;
}
static void kush_kstack_release_chunk(kush_kstack *stack, KushKChunk *chunk) {
    if (kush_kstack_poisoning()) memset(chunk->data, 0xA5, chunk->capacity);
    if (stack->spare == NULL && chunk->capacity == KUSH_KCHUNK) {
        stack->spare = chunk;
    } else {
        kush_free((uint64_t)(uintptr_t)chunk);
    }
}
/* A word-aligned environment of `bytes` bytes on the current task's stack. */
uint64_t kush_kstack_push(uint64_t bytes) {
    kush_kstack *stack = &kush_handlers()->kstack;
    uint64_t need;
    if (__builtin_add_overflow(bytes, (uint64_t)15, &need)) kush_panic();
    need &= ~(uint64_t)15;
    KushKChunk *chunk = stack->chunk;
    if (chunk == NULL || (uint64_t)(chunk->data + chunk->capacity - stack->top) < need) {
        uint64_t base = chunk == NULL ? 0 : chunk->base + (uint64_t)(stack->top - chunk->data);
        KushKChunk *fresh;
        if (need <= KUSH_KCHUNK && stack->spare != NULL) {
            fresh = stack->spare;
            stack->spare = NULL;
        } else {
            uint64_t capacity = need > KUSH_KCHUNK ? need : KUSH_KCHUNK;
            uint64_t total;
            if (__builtin_add_overflow(capacity, (uint64_t)sizeof(KushKChunk), &total)) kush_panic();
            fresh = (KushKChunk *)(uintptr_t)kush_alloc(total);
            fresh->capacity = capacity;
        }
        fresh->previous = chunk;
        fresh->base = base;
        stack->chunk = fresh;
        stack->top = fresh->data;
        chunk = fresh;
    }
    unsigned char *environment = stack->top;
    stack->top += need;
    uint64_t used = chunk->base + (uint64_t)(stack->top - chunk->data);
    if (used > kush_kstack_peak) kush_kstack_peak = used;
    return (uint64_t)(uintptr_t)environment;
}
uint64_t kush_kstack_mark(void) {
    return (uint64_t)(uintptr_t)kush_handlers()->kstack.top;
}
/* Release everything pushed since `mark`. Marks are restored in LIFO
   order; a mark above the top is an internal error. */
void kush_kstack_restore(uint64_t mark) {
    kush_kstack *stack = &kush_handlers()->kstack;
    unsigned char *target = (unsigned char *)(uintptr_t)mark;
    while (stack->chunk != NULL
           && !(target >= stack->chunk->data
                && target <= stack->chunk->data + stack->chunk->capacity)) {
        KushKChunk *chunk = stack->chunk;
        KushKChunk *previous = chunk->previous;
        stack->chunk = previous;
        stack->top = previous == NULL ? NULL : previous->data + (chunk->base - previous->base);
        kush_kstack_release_chunk(stack, chunk);
    }
    if (stack->chunk == NULL) {
        if (target != NULL) kush_panic();
        return;
    }
    if (target > stack->top) kush_panic();
    if (kush_kstack_poisoning()) memset(target, 0xA5, (size_t)(stack->top - target));
    stack->top = target;
    if (target == stack->chunk->data && stack->chunk->previous == NULL) {
        /* Empty: give the chunk back so a finished program owns nothing. */
        KushKChunk *chunk = stack->chunk;
        stack->chunk = NULL;
        stack->top = NULL;
        kush_kstack_release_chunk(stack, chunk);
    }
}
/* Free the spare chunk. A chunk still in use is left alone, so the live
   allocation check at exit reports a missing restore. */
static void kush_kstack_drain(kush_handler_context *context) {
    if (context->kstack.spare != NULL) {
        kush_free((uint64_t)(uintptr_t)context->kstack.spare);
        context->kstack.spare = NULL;
    }
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
/* With threads, generated code reaches the calling thread's abort word
   through this function instead of the shared symbol. */
static KUSH_TLS int64_t kush_abort_word_local = 0;
int64_t kush_abort_word_address(void) {
    return (int64_t)(uintptr_t)&kush_abort_word_local;
}
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
/* Returns the pushed frame: the activation's cell, which a capability names
   (FND-HANDLERS-ONE-CELLS). A task's frames never move. */
int64_t kush_handler_push(int64_t operation, int64_t code, int64_t environment,
                          int64_t once) {
    kush_handler_context *handlers = kush_handlers();
    if (handlers->depth >= KUSH_HANDLER_MAX) kush_panic();
    kush_handler_frame *frame = &handlers->frames[handlers->depth];
    frame->operation = operation;
    frame->code = code;
    frame->environment = environment;
    frame->once = once;
    frame->consumed = 0;
    handlers->depth += 1;
    return (int64_t)(uintptr_t)frame;
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
/* What a perform takes from `frame`: its code, environment and whether the
   call owns the environment. */
static int64_t kush_handler_take(kush_handler_frame *frame, int64_t *out) {
    /* A consumed once frame still discharges its operation: a later
       perform must not fall through to an outer handler. */
    if (frame->consumed) return 0;
    out[0] = frame->code;
    out[1] = frame->environment;
    out[2] = frame->once;
    if (frame->once == 2) {
        /* A reusable handler (all captures copyable) keeps its
           environment; each call owns and frees a fresh copy. */
        KushAllocHeader *header =
            (KushAllocHeader *)(uintptr_t)frame->environment - 1;
        uint64_t copy = kush_alloc(header->usable);
        memcpy((void *)(uintptr_t)copy,
               (const void *)(uintptr_t)frame->environment,
               (size_t)header->usable);
        out[1] = (int64_t)copy;
        out[2] = 1;
    } else if (frame->once) {
        /* A once handler transfers its environment to this call. The
           callee frees it, so the frame must never drop it again. */
        frame->consumed = 1;
        frame->environment = 0;
    }
    return 1;
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
        return kush_handler_take(frame, out);
    }
    return 0;
}
/* A perform through a capability: the activation `cell` when nonzero. A
   task does not get another task's capturing handler (decision D3): its
   cell answers as missing there. */
int64_t kush_handler_perform(int64_t operation, int64_t cell, int64_t *out) {
    if (cell == 0) return kush_handler_lookup(operation, out);
    kush_handler_frame *frame = (kush_handler_frame *)(uintptr_t)cell;
    kush_handler_context *handlers = kush_handlers();
    int own = frame >= handlers->frames && frame < handlers->frames + KUSH_HANDLER_MAX;
    if (!own && frame->once != 0) return 0;
    return kush_handler_take(frame, out);
}
/* Freed task stacks are kept for reuse (a server spawns a task per
   request): mmap, mprotect and munmap cost more than the request. */
#define KUSH_STACK_CACHE 64
static KUSH_TLS void *kush_stack_cache[KUSH_STACK_CACHE];
static KUSH_TLS size_t kush_stack_cache_total[KUSH_STACK_CACHE];
static KUSH_TLS int kush_stack_cached = 0;
static void *kush_stack_alloc(size_t bytes, void **base_out, size_t *total_out) {
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    size_t total = ((bytes + page - 1) / page) * page + page;
    for (int i = kush_stack_cached - 1; i >= 0; --i) {
        if (kush_stack_cache_total[i] != total) continue;
        void *base = kush_stack_cache[i];
        kush_stack_cached -= 1;
        kush_stack_cache[i] = kush_stack_cache[kush_stack_cached];
        kush_stack_cache_total[i] = kush_stack_cache_total[kush_stack_cached];
        kush_note_allocation();
        *base_out = base; *total_out = total;
        return (void *)((char *)base + page);
    }
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
    kush_note_deallocation();
    if (kush_stack_cached < KUSH_STACK_CACHE) {
        kush_stack_cache[kush_stack_cached] = base;
        kush_stack_cache_total[kush_stack_cached] = total;
        kush_stack_cached += 1;
        return;
    }
    if (munmap(base, total) != 0) kush_panic();
}
static void kush_stack_cache_drain(void) {
    while (kush_stack_cached > 0) {
        kush_stack_cached -= 1;
        (void)munmap(kush_stack_cache[kush_stack_cached], kush_stack_cache_total[kush_stack_cached]);
    }
}
static void kush_ready_push(KushTask *task) {
    if (kush_ready_count == kush_ready_capacity) {
        int capacity = kush_ready_capacity == 0 ? 64 : kush_ready_capacity * 2;
        if (capacity <= kush_ready_capacity) kush_panic();
        uint64_t *ready = (uint64_t *)malloc((size_t)capacity * sizeof(uint64_t));
        if (ready == NULL) kush_panic();
        for (int i = 0; i < kush_ready_count; ++i)
            ready[i] = kush_ready[(kush_ready_head + i) % kush_ready_capacity];
        free(kush_ready);
        kush_ready = ready;
        kush_ready_capacity = capacity;
        kush_ready_head = 0;
        kush_ready_tail = kush_ready_count;
    }
    kush_ready[kush_ready_tail] = task->handle;
    kush_ready_tail = (kush_ready_tail + 1) % kush_ready_capacity;
    ++kush_ready_count;
}
static uint64_t kush_ready_pop(void) {
    uint64_t handle = kush_ready[kush_ready_head];
    kush_ready_head = (kush_ready_head + 1) % kush_ready_capacity;
    --kush_ready_count;
    return handle;
}
static uint64_t kush_task_handle(int slot) {
    return ((uint64_t)kush_task_generations[slot] << 32) | (uint64_t)(slot + 1);
}
/* The live task a handle names, the root included, or NULL for a stale or
   malformed handle. */
static KushTask *kush_task_lookup(uint64_t handle) {
    uint64_t low = handle & UINT64_C(0xffffffff);
    if (low == 0 || low > (uint64_t)kush_task_count) return NULL;
    KushTask *t = kush_tasks[low - 1];
    if (t == NULL || t->handle != handle) return NULL;
    return t;
}
static void kush_task_grow(void) {
    int capacity = kush_task_capacity == 0 ? 64 : kush_task_capacity * 2;
    if (capacity <= kush_task_capacity || capacity > KUSH_MAX_SLOTS) kush_panic();
    KushTask **tasks = (KushTask **)realloc(kush_tasks, (size_t)capacity * sizeof(KushTask *));
    if (tasks == NULL) kush_panic();
    kush_tasks = tasks;
    uint32_t *generations = (uint32_t *)realloc(kush_task_generations, (size_t)capacity * sizeof(uint32_t));
    if (generations == NULL) kush_panic();
    kush_task_generations = generations;
    int *free_slots = (int *)realloc(kush_free_slots, (size_t)capacity * sizeof(int));
    if (free_slots == NULL) kush_panic();
    kush_free_slots = free_slots;
    for (int i = kush_task_capacity; i < capacity; ++i) {
        kush_tasks[i] = NULL;
        kush_task_generations[i] = 0;
    }
    kush_task_capacity = capacity;
}
static void kush_scope_unlink(KushTask *t) {
    KushTask *parent = t->parent;
    if (parent == NULL) return;
    int depth = t->parent_depth;
    if (t->previous_sibling != NULL) t->previous_sibling->next_sibling = t->next_sibling;
    else parent->scope_first[depth] = t->next_sibling;
    if (t->next_sibling != NULL) t->next_sibling->previous_sibling = t->previous_sibling;
    else parent->scope_last[depth] = t->previous_sibling;
    t->parent = t->previous_sibling = t->next_sibling = NULL;
}
/* Drop the frames a finished task left and free its handler context. A
   continuation chunk still in use is left alone, so the live allocation
   check at exit reports the missing restore. */
static void kush_kstack_drain(kush_handler_context *context);
static void kush_handler_drop_frame(kush_handler_frame *frame);
static void kush_task_release_handlers(KushTask *t) {
    kush_handler_context *handlers = t->handlers;
    if (handlers == NULL) return;
    while (handlers->depth > 0) {
        handlers->depth -= 1;
        kush_handler_drop_frame(&handlers->frames[handlers->depth]);
    }
    kush_kstack_drain(handlers);
    free(handlers);
    t->handlers = NULL;
}
/* ---- WEB-REACTOR: descriptor and timer waits ---------------------------
   A task waiting for a descriptor or a deadline is BLOCKED on the waiting
   list. When no task is ready the scheduler sleeps in epoll_wait until a
   registered descriptor is ready or the nearest deadline; while tasks are
   ready it still checks every 64 switches so none waits forever. */
#include <sys/epoll.h>
/* Per thread, like the scheduler: each thread has its own reactor. */
static KUSH_TLS int kush_epoll = -1;
static KUSH_TLS KushTask *kush_waiting = NULL;
static KUSH_TLS unsigned kush_reactor_turns = 0;
static void kush_reactor_wake(KushTask *t, int64_t result) {
    if (t->wait_previous != NULL) t->wait_previous->wait_next = t->wait_next;
    else kush_waiting = t->wait_next;
    if (t->wait_next != NULL) t->wait_next->wait_previous = t->wait_previous;
    t->wait_previous = t->wait_next = NULL;
    if (t->wait_fd >= 0) {
        (void)epoll_ctl(kush_epoll, EPOLL_CTL_DEL, t->wait_fd, NULL);
        (void)close(t->wait_fd);
        t->wait_fd = -1;
    }
    t->waiting_io = 0;
    t->wait_result = result;
    t->state = KUSH_READY;
    kush_ready_push(t);
}
static void kush_reactor_poll(int block) {
    int timeout = 0;
    int64_t now = kush_host_now_ms();
    if (block) {
        int64_t nearest = -1;
        for (KushTask *t = kush_waiting; t != NULL; t = t->wait_next)
            if (t->wait_deadline >= 0 && (nearest < 0 || t->wait_deadline < nearest))
                nearest = t->wait_deadline;
        if (nearest < 0) timeout = -1;
        else if (nearest > now) timeout = nearest - now > 60000 ? 60000 : (int)(nearest - now);
    }
    struct epoll_event events[64];
    int count = 0;
    if (kush_epoll >= 0) count = epoll_wait(kush_epoll, events, 64, timeout);
    else if (timeout != 0) (void)poll(NULL, 0, timeout);
    for (int i = 0; i < count; ++i) {
        KushTask *t = kush_task_lookup(events[i].data.u64);
        /* EPOLLIN, EPOLLOUT, EPOLLERR and EPOLLHUP have poll(2)'s values. */
        if (t != NULL && t->waiting_io) kush_reactor_wake(t, (int64_t)(events[i].events & 0x1f));
    }
    now = kush_host_now_ms();
    for (KushTask *t = kush_waiting, *next; t != NULL; t = next) {
        next = t->wait_next;
        if (t->wait_deadline >= 0 && now >= t->wait_deadline) kush_reactor_wake(t, 0);
    }
}
/* Cancellation is structured (TASK-CANCEL-PROPAGATE): cancelling a task
   also cancels every unjoined task in its scopes, recursively. */
static void kush_task_request_cancel(KushTask *t) {
    if (t->joined || t->state == KUSH_FINISHED) return;
    t->cancelled = 1;
    if (t->waiting_io && !t->wait_shielded) kush_reactor_wake(t, -1);
    for (int depth = 0; depth < t->scope_depth; ++depth)
        for (KushTask *child = t->scope_first[depth]; child != NULL; child = child->next_sibling)
            kush_task_request_cancel(child);
}
static void kush_scheduler(void) {
    for (;;) {
        if (kush_waiting != NULL && (kush_ready_count == 0 || ++kush_reactor_turns % 64 == 0))
            kush_reactor_poll(kush_ready_count == 0);
        if (kush_ready_count == 0) {
            if (kush_waiting != NULL) continue;
            kush_panic();
        }
        KushTask *t = kush_task_lookup(kush_ready_pop());
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
    if (kush_task_capacity == 0) kush_task_grow();
    root->id = 0; root->handle = kush_task_handle(0);
    root->state = KUSH_RUNNING; root->completed = 1;
    kush_tasks[0] = root; kush_task_count = 1; kush_free_count = 0;
    kush_current = root;
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
    int id;
    if (kush_free_count > 0) {
        id = kush_free_slots[--kush_free_count];
    } else {
        if (kush_task_count == kush_task_capacity) kush_task_grow();
        id = kush_task_count++;
    }
    KushTask *t = (KushTask *)(uintptr_t)kush_alloc(sizeof(KushTask));
    memset(t, 0, sizeof(*t));
    t->id = (uint64_t)id; t->handle = kush_task_handle(id); t->wrapper = wrapper; t->code = code; t->env = env;
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
    /* Inherit the parent's copyable noncapturing dynamic handler frames.
       A capturing or one-shot frame is a task boundary: its environment is
       owned by the parent's dynamic extent, so only the longest inheritable
       innermost contiguous suffix crosses. Frames below a barrier must not
       become visible to a child merely because their shadowing frame cannot
       be inherited. */
    {
        kush_handler_context *parent = kush_handlers();
        /* Walk the frames visible to the parent: a redirect frame (pushed by
           a resumed continuation) skips the frames its handler pushed. */
        static KUSH_TLS int64_t picked[KUSH_HANDLER_MAX];
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
        if (count > 0) {
            kush_handler_context *child =
                (kush_handler_context *)calloc(1, sizeof(kush_handler_context));
            if (child == NULL) kush_panic();
            for (int64_t i = count - 1; i >= 0; --i) {
                child->frames[child->depth] = parent->frames[picked[i]];
                child->depth += 1;
            }
            t->handlers = child;
        }
    }
    kush_ready_push(t);
    int depth = kush_current->scope_depth - 1;
    t->parent = kush_current; t->parent_depth = depth;
    t->previous_sibling = kush_current->scope_last[depth];
    if (t->previous_sibling != NULL) t->previous_sibling->next_sibling = t;
    else kush_current->scope_first[depth] = t;
    kush_current->scope_last[depth] = t;
    kush_tasks[id] = t;
    return t->handle;
}
static void kush_task_entry(unsigned int low, unsigned int high) {
    uintptr_t pointer = ((uintptr_t)high << 32) | (uintptr_t)low;
    KushTask *t = (KushTask *)pointer;
    kush_current = t;
    ((void (*)(uint64_t, uint64_t, uint64_t))(uintptr_t)t->wrapper)(
        t->code, t->env, (uint64_t)(uintptr_t)t->result);
    t->completed = (t->cancelled && !t->preserve) ? 0 : 1;
#ifdef KUSH_UNWIND
    /* A panic unwound the whole task body: the task ends here and its join
       raises the panic in the parent (PANIC-UNWIND-USE). Its result buffer
       holds nothing. */
    if (*kush_panic_word() == 1) {
        *kush_panic_word() = 0;
        t->panicked = 1;
        t->completed = 0;
    }
#endif
    t->state = KUSH_FINISHED;
    if (t->waiter != NULL) {
        t->waiter->state = KUSH_READY;
        kush_ready_push(t->waiter);
        t->waiter = NULL;
    }
    swapcontext(&t->context, &kush_scheduler_context);
    abort();
}
uint64_t kush_task_join(uint64_t handle, void *out) {
    if (!kush_initialized || handle == 0) kush_panic();
    KushTask *t = kush_task_lookup(handle);
    if (t == NULL || t->id == 0 || t->joined || t == kush_current) kush_panic();
    int id = (int)t->id;
    while (t->state != KUSH_FINISHED) {
        kush_current->state = KUSH_BLOCKED;
        t->waiter = kush_current;
        swapcontext(&kush_current->context, &kush_scheduler_context);
    }
    int completed = t->completed;
    int panicked = t->panicked;
    if (out == NULL && t->preserve && !panicked) kush_panic();
    if (panicked) {
        /* No result to copy or drop. */
    } else if (out != NULL) {
        memcpy(out, t->result, t->result_size);
    } else if (t->drop != NULL) {
        t->drop(t->result);
    }
    t->joined = 1;
    kush_scope_unlink(t);
    kush_task_release_handlers(t);
    kush_tasks[id] = NULL;
    kush_task_generations[id] += 1;
    kush_free_slots[kush_free_count++] = id;
    kush_free((uint64_t)(uintptr_t)t->result);
    kush_stack_free(t->stack_base, t->stack_total);
    kush_free((uint64_t)(uintptr_t)t);
    return panicked ? 2 : completed ? 0 : 1;
}
uint64_t kush_task_yield(void) {
    kush_task_init();
    KushTask *t = kush_current;
    t->state = KUSH_READY;
    kush_ready_push(t);
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
    KushTask *t = kush_task_lookup(value);
    if (t == NULL || t->id == 0) return 0;
    if (!t->joined && t->state != KUSH_FINISHED) kush_task_request_cancel(t);
    return 0;
}
uint64_t kush_task_scope_begin(void) {
    kush_task_init();
    if (kush_current->scope_depth >= KUSH_MAX_SCOPES) KUSH_FAIL(0);
    kush_current->scope_first[kush_current->scope_depth] = NULL;
    kush_current->scope_last[kush_current->scope_depth] = NULL;
    ++kush_current->scope_depth;
    return 0;
}
uint64_t kush_task_cancel_scope(void) {
    if (!kush_initialized || kush_current == NULL || kush_current->scope_depth == 0) return 0;
    int depth = kush_current->scope_depth - 1;
    for (KushTask *child = kush_current->scope_first[depth]; child != NULL;
         child = child->next_sibling) {
        if (!child->joined && child->state != KUSH_FINISHED) kush_task_request_cancel(child);
    }
    return 0;
}
uint64_t kush_task_scope_end(void) {
    if (!kush_initialized || kush_current->scope_depth == 0) kush_panic();
    --kush_current->scope_depth;
    int depth = kush_current->scope_depth;
    /* Every listed child is unjoined and joining unlinks it, so join the
       first child until none is left: spawn order, as before. */
    int panicked = 0;
    while (kush_current->scope_first[depth] != NULL) {
        if (kush_task_join(kush_current->scope_first[depth]->handle, NULL) == 2) panicked = 1;
    }
#ifdef KUSH_UNWIND
    /* A child the epilogue joined panicked: raise it here (PANIC-UNWIND-USE). */
    if (panicked) kush_unwind_rethrow();
#endif
    (void)panicked;
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
    free(kush_tasks); kush_tasks = NULL;
    free(kush_task_generations); kush_task_generations = NULL;
    free(kush_free_slots); kush_free_slots = NULL;
    kush_free_count = 0; kush_task_capacity = 0;
    free(kush_ready); kush_ready = NULL;
    kush_ready_capacity = 0; kush_ready_head = kush_ready_tail = kush_ready_count = 0;
    kush_stack_free(kush_scheduler_stack, kush_scheduler_stack_total);
    kush_scheduler_stack = NULL;
    kush_stack_cache_drain();
    if (kush_epoll >= 0) { (void)close(kush_epoll); kush_epoll = -1; }
    kush_waiting = NULL;
    kush_initialized = 0;
    kush_current = NULL;
    kush_task_count = 0;
}
/* Wait until `fd` has one of `events` (poll(2) bits) or `timeout_ms` passes
   (-1 forever; fd -1 waits for the timeout alone), letting the other tasks
   run meanwhile: the events, 0 on timeout. ECANCELED (125) when the task is
   or becomes cancelled, unless `events` has KUSH_WAIT_SHIELD (256): a
   shielded wait (finishing a response during a graceful stop) runs to its
   event or timeout. It waits on the calling thread's own scheduler and
   reactor (THREAD-TASKS); a thread's body and `main` may wait too. */
int64_t kush_sys_wait_ready(int64_t fd, int64_t events, int64_t timeout_ms, int64_t *out) {
    if (timeout_ms < -1 || timeout_ms > INT32_MAX) return EINVAL;
    kush_task_init();
    KushTask *t = kush_current;
    int shielded = (events & 256) != 0;
    if (t->cancelled && !shielded) return ECANCELED;
    t->wait_shielded = shielded;
    t->wait_fd = -1;
    if (fd >= 0) {
        if (kush_epoll < 0) {
            kush_epoll = epoll_create1(EPOLL_CLOEXEC);
            if (kush_epoll < 0) return errno;
        }
        /* A private duplicate, so several tasks can wait on one socket. */
        int copy = fcntl((int)fd, F_DUPFD_CLOEXEC, 0);
        if (copy < 0) return errno;
        struct epoll_event wanted;
        memset(&wanted, 0, sizeof(wanted));
        wanted.events = ((uint32_t)events & (EPOLLIN | EPOLLOUT)) | EPOLLONESHOT;
        wanted.data.u64 = t->handle;
        if (epoll_ctl(kush_epoll, EPOLL_CTL_ADD, copy, &wanted) != 0) {
            int code = errno;
            (void)close(copy);
            return code;
        }
        t->wait_fd = copy;
    }
    int64_t now = kush_host_now_ms();
    t->wait_deadline = timeout_ms < 0 ? -1 : (now < 0 ? 0 : now + timeout_ms);
    t->waiting_io = 1;
    t->wait_previous = NULL;
    t->wait_next = kush_waiting;
    if (kush_waiting != NULL) kush_waiting->wait_previous = t;
    kush_waiting = t;
    t->state = KUSH_BLOCKED;
    swapcontext(&t->context, &kush_scheduler_context);
    if (t->wait_result < 0) return ECANCELED;
    *out = t->wait_result;
    return 0;
}
/* PANIC-UNWIND-USE: whether a panic now unwinds instead of aborting. A
   thread body and a spawned task unwind to their entry, and their join
   raises the panic in the joiner; `main` unwinds only inside a Task.catch.
   A panic nothing catches still aborts the process, at the root. */
static int kush_panic_unwinds(void) {
#ifdef KUSH_UNWIND
    if (kush_in_thread) return kush_thread_nounwind_depth == 0;
    if (!kush_initialized || kush_current == NULL || kush_current->state != KUSH_RUNNING) return 0;
    if (kush_current->nounwind_depth > 0) return 0;
    return kush_current->id != 0 || kush_current->catch_depth > 0;
#else
    return 0;
#endif
}
static void kush_nounwind_enter(void) {
#ifdef KUSH_UNWIND
    if (kush_in_thread) { kush_thread_nounwind_depth += 1; return; }
    if (kush_initialized && kush_current != NULL) kush_current->nounwind_depth += 1;
#endif
}
static void kush_nounwind_leave(void) {
#ifdef KUSH_UNWIND
    if (kush_in_thread) {
        if (kush_thread_nounwind_depth > 0) kush_thread_nounwind_depth -= 1;
        return;
    }
    if (kush_initialized && kush_current != NULL && kush_current->nounwind_depth > 0)
        kush_current->nounwind_depth -= 1;
#endif
}
/* Task.catch: count the bodies running in this task, or in this thread. */
void kush_catch_enter(void) {
    if (kush_in_thread) { kush_thread_catch_depth += 1; return; }
    kush_task_init();
    kush_current->catch_depth += 1;
}
void kush_catch_leave(void) {
    if (kush_in_thread) { kush_thread_catch_depth -= 1; return; }
    kush_current->catch_depth -= 1;
}
static int64_t *kush_panic_word(void) {
#ifdef KUSH_HAS_THREADS
    return &kush_abort_word_local;
#else
    return &kush_abort_word;
#endif
}
static void kush_raise_panic(void) {
    static const char message[] = "panic: checked arithmetic, memory, or I/O failure\n";
    kush_best_effort_write(2, message, sizeof(message) - 1);
    *kush_panic_word() = 1;
}
/* PANIC-LINEAR-CLEANUP: the drop glue of a linear type with an unwind
   cleanup holds the panic word clear while the cleanup runs, so the
   cleanup's own calls run normally. */
int64_t kush_unwind_hold(void) {
    int64_t *word = kush_panic_word();
    int64_t held = *word;
    *word = 0;
    return held;
}
void kush_unwind_restore(int64_t held) {
    *kush_panic_word() = held;
}
/* Generated code's panic sites: unwind when a boundary is active (set the
   word and return, the caller then leaves through its cleanup), otherwise
   abort. */
void kush_unwind_panic(void) {
    if (!kush_panic_unwinds()) kush_panic();
    kush_raise_panic();
}
/* A joined task or thread panicked: raise the panic again in the joiner
   (its message was already printed), or abort when nothing can stop it. */
void kush_unwind_rethrow(void) {
    if (!kush_panic_unwinds()) {
        static const char message[] = "panic: a joined task or thread panicked\n";
        kush_best_effort_write(2, message, sizeof(message) - 1);
        abort();
    }
    *kush_panic_word() = 1;
}
#ifdef KUSH_HAS_THREADS
/* ---- THREAD-SCOPE: structured OS threads ---------------------------------
   A Thread.scope frame lists the threads spawned in it; Thread.join waits for
   one, and the scope epilogue joins every one not joined yet and drops its
   result. Threads run the same task wrapper (code, environment, result
   buffer) as cooperative tasks. A thread has its own handler stack,
   allocator pool and task scheduler; they are freed when it finishes. */
typedef struct KushThread {
    pthread_t thread;
    uint64_t wrapper, code, env;
    void *result;
    size_t result_size;
    void (*drop)(void *);
    int preserve, joined;
    /* PANIC-UNWIND-USE: a panic unwound the whole body; the join raises it. */
    int panicked;
    struct KushThread *next;
} KushThread;
#define KUSH_THREAD_SCOPES 64
static KUSH_TLS KushThread *kush_thread_scopes[KUSH_THREAD_SCOPES];
static KUSH_TLS int kush_thread_scope_depth = 0;
static void *kush_thread_main(void *argument) {
    KushThread *t = (KushThread *)argument;
    kush_handler_context *handlers = (kush_handler_context *)calloc(1, sizeof(kush_handler_context));
    if (handlers == NULL) kush_panic();
    kush_thread_handlers = handlers;
    kush_in_thread = 1;
    ((void (*)(uint64_t, uint64_t, uint64_t))(uintptr_t)t->wrapper)(
        t->code, t->env, (uint64_t)(uintptr_t)t->result);
#ifdef KUSH_UNWIND
    if (*kush_panic_word() == 1) {
        *kush_panic_word() = 0;
        t->panicked = 1;
    }
#endif
    /* THREAD-TASKS: free this thread's scheduler (every task it ran was
       joined by its scope), before the pool its blocks return to drains. */
    kush_task_finish();
    kush_handler_restore(0);
    kush_kstack_drain(handlers);
    kush_thread_handlers = NULL;
    free(handlers);
    kush_pool_drain();
    return NULL;
}
void kush_thread_scope_begin(void) {
    if (kush_thread_scope_depth >= KUSH_THREAD_SCOPES) kush_panic();
    kush_thread_scopes[kush_thread_scope_depth++] = NULL;
}
static void kush_thread_wait(KushThread *t) {
    if (pthread_join(t->thread, NULL) != 0) kush_panic();
    t->joined = 1;
}
void kush_thread_scope_end(void) {
    if (kush_thread_scope_depth == 0) kush_panic();
    KushThread *t = kush_thread_scopes[--kush_thread_scope_depth];
    int panicked = 0;
    while (t != NULL) {
        KushThread *next = t->next;
        if (!t->joined) {
            kush_thread_wait(t);
            if (t->panicked) {
                panicked = 1;
            } else {
                if (t->preserve) kush_panic();
                if (t->drop != NULL) t->drop(t->result);
            }
            kush_free((uint64_t)(uintptr_t)t->result);
        }
        kush_free((uint64_t)(uintptr_t)t);
        t = next;
    }
#ifdef KUSH_UNWIND
    /* A thread the epilogue joined panicked: raise it here. */
    if (panicked) kush_unwind_rethrow();
#endif
    (void)panicked;
}
uint64_t kush_thread_spawn(uint64_t wrapper, uint64_t code, uint64_t env,
                           uint64_t result_size, uint64_t drop, uint64_t preserve) {
    if (kush_thread_scope_depth == 0) kush_panic();
    KushThread *t = (KushThread *)(uintptr_t)kush_alloc(sizeof(KushThread));
    memset(t, 0, sizeof(*t));
    t->wrapper = wrapper; t->code = code; t->env = env;
    t->result_size = result_size == 0 ? 8 : (size_t)result_size;
    t->drop = (void (*)(void *))(uintptr_t)drop;
    t->preserve = preserve != 0;
    t->result = (void *)(uintptr_t)kush_alloc(t->result_size);
    pthread_attr_t attributes;
    if (pthread_attr_init(&attributes) != 0) kush_panic();
    if (pthread_attr_setstacksize(&attributes, (size_t)64 << 20) != 0) kush_panic();
    if (pthread_create(&t->thread, &attributes, kush_thread_main, t) != 0) kush_panic();
    pthread_attr_destroy(&attributes);
    t->next = kush_thread_scopes[kush_thread_scope_depth - 1];
    kush_thread_scopes[kush_thread_scope_depth - 1] = t;
    return (uint64_t)(uintptr_t)t;
}
/* ---- THREAD-CHANNELS: bounded channels of plain-data messages ----------
   One counted allocation holds the header and a ring of `capacity` messages
   of `width` words. Send waits while full and panics once closed; receive
   waits while empty and open and reports a closed, drained channel. */
typedef struct {
    pthread_mutex_t lock;
    pthread_cond_t readable, writable;
    int64_t capacity, width, head, count;
    int closed;
    uint64_t words[];
} KushChannel;
uint64_t kush_channel_new(int64_t capacity, int64_t width) {
    if (capacity < 1 || capacity > ((int64_t)1 << 24) || width < 0 || width > 64) kush_panic();
    int64_t stride = width == 0 ? 1 : width;
    KushChannel *c = (KushChannel *)(uintptr_t)kush_alloc(
        sizeof(KushChannel) + (size_t)capacity * (size_t)stride * sizeof(uint64_t));
    memset(c, 0, sizeof(KushChannel));
    if (pthread_mutex_init(&c->lock, NULL) != 0) kush_panic();
    if (pthread_cond_init(&c->readable, NULL) != 0) kush_panic();
    if (pthread_cond_init(&c->writable, NULL) != 0) kush_panic();
    c->capacity = capacity; c->width = stride;
    return (uint64_t)(uintptr_t)c;
}
void kush_channel_free(uint64_t handle) {
    KushChannel *c = (KushChannel *)(uintptr_t)handle;
    if (c == NULL) return;
    pthread_cond_destroy(&c->readable);
    pthread_cond_destroy(&c->writable);
    pthread_mutex_destroy(&c->lock);
    kush_free(handle);
}
void kush_channel_send(uint64_t handle, const uint64_t *message) {
    KushChannel *c = (KushChannel *)(uintptr_t)handle;
    if (c == NULL || pthread_mutex_lock(&c->lock) != 0) kush_panic();
    while (c->count == c->capacity && !c->closed) pthread_cond_wait(&c->writable, &c->lock);
    if (c->closed) { pthread_mutex_unlock(&c->lock); kush_panic(); }
    int64_t slot = (c->head + c->count) % c->capacity;
    memcpy(&c->words[slot * c->width], message, (size_t)c->width * sizeof(uint64_t));
    c->count += 1;
    pthread_cond_signal(&c->readable);
    pthread_mutex_unlock(&c->lock);
}
int64_t kush_channel_recv(uint64_t handle, uint64_t *out) {
    KushChannel *c = (KushChannel *)(uintptr_t)handle;
    if (c == NULL || pthread_mutex_lock(&c->lock) != 0) kush_panic();
    while (c->count == 0 && !c->closed) pthread_cond_wait(&c->readable, &c->lock);
    if (c->count == 0) { pthread_mutex_unlock(&c->lock); return 0; }
    memcpy(out, &c->words[c->head * c->width], (size_t)c->width * sizeof(uint64_t));
    c->head = (c->head + 1) % c->capacity;
    c->count -= 1;
    pthread_cond_signal(&c->writable);
    pthread_mutex_unlock(&c->lock);
    return 1;
}
void kush_channel_close(uint64_t handle) {
    KushChannel *c = (KushChannel *)(uintptr_t)handle;
    if (c == NULL || pthread_mutex_lock(&c->lock) != 0) kush_panic();
    c->closed = 1;
    pthread_cond_broadcast(&c->readable);
    pthread_cond_broadcast(&c->writable);
    pthread_mutex_unlock(&c->lock);
}
uint64_t kush_thread_join(uint64_t handle, void *out) {
    KushThread *t = (KushThread *)(uintptr_t)handle;
    if (t == NULL || t->joined) kush_panic();
    kush_thread_wait(t);
    /* 2: the body panicked; the joiner raises it (PANIC-UNWIND-USE). */
    if (!t->panicked) memcpy(out, t->result, t->result_size);
    kush_free((uint64_t)(uintptr_t)t->result);
    return t->panicked ? 2 : 0;
}
#endif
#ifndef KUSH_NO_MAIN
#ifdef KUSH_MAIN_STACK
/* `#[stack_size(N)]` on main: the program runs on a thread with a stack of
   KUSH_MAIN_STACK bytes (reserved, committed as it is used), with the same
   stack-exhaustion panic as the process stack. */
static int64_t kush_main_result;
static char kush_main_signal_stack[1 << 16];
static void *kush_main_thread(void *unused) {
    (void)unused;
    kush_stack_guard_thread(kush_main_signal_stack, sizeof(kush_main_signal_stack));
#ifdef KUSH_HAS_TASKS
    kush_task_init();
#endif
    kush_main_result = kush_entry();
    kush_task_finish();
    return NULL;
}
#endif
int main(int argc, char **argv) {
#ifdef KUSH_FUZZ
    kush_fuzz_init();
#endif
    kush_host_init(argc, argv);
    /* Broken pipes become recoverable EPIPE results instead of process signals. */
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) kush_panic();
    kush_stack_guard_init();
    /* Formatting and parse-back must never depend on the host locale. */
    if (setlocale(LC_NUMERIC, "C") == NULL) kush_panic();
#ifdef KUSH_MAIN_STACK
    {
        pthread_t thread;
        pthread_attr_t attributes;
        if (pthread_attr_init(&attributes) != 0) kush_panic();
        if (pthread_attr_setstacksize(&attributes, (size_t)KUSH_MAIN_STACK) != 0) kush_panic();
        if (pthread_create(&thread, &attributes, kush_main_thread, NULL) != 0) kush_panic();
        pthread_attr_destroy(&attributes);
        if (pthread_join(thread, NULL) != 0) kush_panic();
    }
    int64_t result = kush_main_result;
#else
#ifdef KUSH_HAS_TASKS
    kush_task_init();
#endif
    int64_t result = kush_entry();
    kush_task_finish();
#endif
    /* Retained pool storage is physical only; release it before the live
       allocation check so a normal exit owns nothing either way. */
    kush_pool_drain();
    kush_kstack_drain(&kush_root_handlers);
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
    if (getenv("KUSH_KSTACK_STATS") != NULL) {
        char line[128];
        int length = snprintf(line, sizeof(line), "kstack-stats: peak-bytes=%llu\n",
            (unsigned long long)kush_kstack_peak);
        if (length > 0) kush_best_effort_write(2, line, (size_t)(length < (int)sizeof(line) ? length : (int)sizeof(line) - 1));
    }
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
#ifdef KUSH_FUZZ
    kush_fuzz_write(-1);
#endif
    return (int)((uint64_t)result & UINT64_C(255));
}
#endif
