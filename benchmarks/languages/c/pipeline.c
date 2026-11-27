// The fused batch of ../../feature-pipeline (Rust mode 1), in C: a boxed
// ticket key, one vector at its final capacity, the fused transform and a
// checksum. -DCHECKED checks the checksum's additions for overflow, as Kush
// and Rust with overflow checks do.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef CHECKED
static inline int64_t add(int64_t a, int64_t b) {
    int64_t r;
    if (__builtin_add_overflow(a, b, &r)) abort();
    return r;
}
#else
#define add(a, b) ((a) + (b))
#endif

static int64_t scrub(int64_t x) { return (x & 65535) ^ (x & 255); }
static int64_t tag(int64_t x) { return x ^ 23130; }

static int64_t checksum(const int64_t *values, size_t n) {
    int64_t sum = 0;
    for (size_t i = 0; i < n; i++) sum = add(sum, values[i]);
    return sum;
}

static int64_t batch(size_t n) {
    int64_t *ticket = malloc(sizeof *ticket);
    if (!ticket) abort();
    *ticket = 23130;
    int64_t *values = malloc(n * sizeof *values);
    if (!values) abort();
    for (size_t i = 0; i < n; i++) values[i] = (int64_t)i & 65535;
    for (size_t i = 0; i < n; i++) values[i] = tag(scrub(values[i]));
    int64_t result = add(checksum(values, n), *ticket);
    free(values);
    free(ticket);
    return result;
}

static int argument(const char *text, int64_t *out) {
    char *end;
    long long value = strtoll(text, &end, 10);
    if (*text == 0 || *end != 0) return 0;
    *out = value;
    return 1;
}

int main(int argc, char **argv) {
    int64_t n, rounds, mode;
    if (argc != 4 || !argument(argv[1], &n) || !argument(argv[2], &rounds) ||
        !argument(argv[3], &mode))
        return 2;
    if (n < 1 || n > 8000000 || rounds < 0 || rounds > 32 || mode != 1) return 2;
    int64_t result = 0;
    for (int64_t round = 0; round < rounds; round++) result = add(result, batch((size_t)n));
    printf("%lld\n", (long long)result);
    return 0;
}
