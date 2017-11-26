#include <inttypes.h>
#include <stdio.h>
#include <time.h>
#include "pcg-c-basic/pcg_basic.h"

typedef struct {
    uintptr_t len;
    const uint8_t *data;
} KvasirString;

int64_t read_int64(void) {
    int64_t n;
    scanf("%" PRIi64, &n);
    return n;
}

uint64_t read_uint64(void) {
    uint64_t n;
    scanf("%" PRIu64, &n);
    return n;
}

void print_int64(int64_t n) {
    printf("%" PRIi64 "\n", n);
}

void print_uint64(uint64_t n) {
    printf("%" PRIu64 "\n", n);
}

void print_float64(double x) {
    printf("%f\n", x);
}

void c_display(KvasirString s) {
    printf("%.*s\n", (int)s.len, s.data);
}

uint64_t _clock(void) {
    return (uint64_t)clock();
}
