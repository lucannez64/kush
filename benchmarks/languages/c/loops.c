// The three kernels of ../../checked-loops, in C. Build with -DCHECKED to
// check every +, - and * for overflow (Kush semantics, minus bounds checks,
// which C has none of); without it, C's ordinary unchecked arithmetic.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef CHECKED
static inline int64_t add(int64_t a, int64_t b) {
    int64_t r;
    if (__builtin_add_overflow(a, b, &r)) abort();
    return r;
}
static inline int64_t sub(int64_t a, int64_t b) {
    int64_t r;
    if (__builtin_sub_overflow(a, b, &r)) abort();
    return r;
}
static inline int64_t mul(int64_t a, int64_t b) {
    int64_t r;
    if (__builtin_mul_overflow(a, b, &r)) abort();
    return r;
}
#else
#define add(a, b) ((a) + (b))
#define sub(a, b) ((a) - (b))
#define mul(a, b) ((a) * (b))
#endif

__attribute__((noinline)) static int64_t sum(const int64_t *values, int64_t n) {
    int64_t acc = 0;
    for (int64_t i = 0; i < n; i++) acc = add(acc, values[i]);
    return acc;
}

__attribute__((noinline)) static int64_t dot(const int64_t *left, const int64_t *right, int64_t n) {
    int64_t acc = 0;
    for (int64_t i = 0; i < n; i++) acc = add(acc, mul(left[i], right[i]));
    return acc;
}

__attribute__((noinline)) static void scale(const int64_t *source, int64_t *target, int64_t n,
                                            int64_t factor) {
    for (int64_t i = 0; i < n; i++) target[i] = sub(mul(source[i], factor), 7);
}

static int64_t *fill(int64_t n, int64_t salt) {
    int64_t *values = malloc((size_t)n * sizeof *values);
    if (!values) abort();
    for (int64_t i = 0; i < n; i++) values[i] = sub(add(mul(i, 7919), salt) & 4095, 2048);
    return values;
}

static int argument(const char *text, int64_t *out) {
    char *end;
    long long value = strtoll(text, &end, 10);
    if (*text == 0 || *end != 0) return 0;
    *out = value;
    return 1;
}

int main(int argc, char **argv) {
    int64_t n, repetitions, kernel;
    if (argc != 4 || !argument(argv[1], &n) || !argument(argv[2], &repetitions) ||
        !argument(argv[3], &kernel))
        return 2;
    if (n < 1 || n > 8000000 || repetitions < 0 || repetitions > 100000000 || kernel < 0 ||
        kernel > 2)
        return 2;
    int64_t *left = fill(n, 17);
    int64_t *right = fill(n, 4001);
    int64_t *scratch = fill(n, 0);
    int64_t result = 0;
    for (int64_t round = 0; round < repetitions; round++) {
        int64_t step;
        if (kernel == 0) {
            step = sum(left, n);
        } else if (kernel == 1) {
            step = dot(left, right, n);
        } else {
            scale(left, scratch, n, add(round & 3, 2));
            step = sum(scratch, n);
        }
        result = add(result ^ step, round & 1);
    }
    printf("%lld\n", (long long)result);
    free(left);
    free(right);
    free(scratch);
    return 0;
}
