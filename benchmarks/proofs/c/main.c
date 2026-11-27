// The kernels of ../kush/main.kush in C. C never checks indexing, so this is
// the form Kush's proofs reach: unchecked reads and window arithmetic, with
// the accumulators checked for overflow as in Kush. The fourth argument is
// accepted for symmetry and ignored.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static inline int64_t add(int64_t a, int64_t b) {
    int64_t r;
    if (__builtin_add_overflow(a, b, &r)) abort();
    return r;
}

__attribute__((noinline)) static int64_t sum(const int64_t *values, int64_t n) {
    int64_t acc = 0;
    for (int64_t i = 0; i < n; i++) acc = add(acc, values[i]);
    return acc;
}

__attribute__((noinline)) static int64_t stencil(const uint8_t *data, int64_t n) {
    int64_t acc = 0;
    for (int64_t i = 1; i < n - 1; i++) {
        int64_t window = (int64_t)data[i - 1] + 2 * (int64_t)data[i] + (int64_t)data[i + 1];
        acc = add(acc, window);
    }
    return acc;
}

__attribute__((noinline)) static uint32_t crc32(const uint32_t *table, uint32_t crc,
                                                const uint8_t *data, int64_t n) {
    uint32_t c = crc ^ 0xFFFFFFFFu;
    for (int64_t i = 0; i < n; i++) c = table[(c ^ data[i]) & 255] ^ (c >> 8);
    return c ^ 0xFFFFFFFFu;
}

__attribute__((noinline)) static int64_t lookup(const int64_t *table, const uint8_t *data,
                                                int64_t n) {
    int64_t acc = 0;
    for (int64_t i = 0; i < n; i++) acc = add(acc, table[data[i]]);
    return acc;
}

__attribute__((noinline)) static int64_t follow(const int64_t *values, int64_t n) {
    int64_t acc = 0, j = 0;
    for (int64_t i = 0; i < n; i++) {
        acc = add(acc, values[j]);
        if (values[i] > 0) j = add(j, 1);
    }
    return acc;
}

static int argument(const char *text, int64_t *out) {
    char *end;
    long long value = strtoll(text, &end, 10);
    if (*text == 0 || *end != 0) return 0;
    *out = value;
    return 1;
}

int main(int argc, char **argv) {
    int64_t n, repetitions, kernel, trusted;
    if (argc != 5 || !argument(argv[1], &n) || !argument(argv[2], &repetitions) ||
        !argument(argv[3], &kernel) || !argument(argv[4], &trusted))
        return 2;
    if (n < 3 || n > 8000000 || repetitions < 0 || repetitions > 100000000 || kernel < 0 ||
        kernel > 4 || trusted < 0 || trusted > 1)
        return 2;
    int64_t *values = malloc((size_t)n * sizeof *values);
    uint8_t *data = malloc((size_t)n);
    uint32_t table[256];
    if (!values || !data) abort();
    for (int64_t i = 0; i < n; i++) {
        values[i] = ((i * 7919 + 17) & 4095) - 2048;
        data[i] = (uint8_t)((i * 7 + 3) & 255);
    }
    for (uint32_t k = 0; k < 256; k++) {
        uint32_t c = k;
        for (int bit = 0; bit < 8; bit++) c = (c & 1) ? 0xEDB88320u ^ (c >> 1) : c >> 1;
        table[k] = c;
    }
    int64_t *codec = malloc(256 * sizeof *codec);
    if (!codec) abort();
    for (int64_t k = 0; k < 256; k++) codec[k] = ((k * 40503 + 7) & 1023) - 512;
    int64_t result = 0;
    for (int64_t round = 0; round < repetitions; round++) {
        int64_t step;
        if (kernel == 0) step = sum(values, n);
        else if (kernel == 1) step = stencil(data, n);
        else if (kernel == 3) step = lookup(codec, data, n);
        else if (kernel == 4) step = follow(values, n);
        else step = crc32(table, (uint32_t)round, data, n);
        result = add(result ^ step, round & 1);
    }
    printf("%lld\n", (long long)result);
    free(values);
    free(data);
    free(codec);
    return 0;
}
