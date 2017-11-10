#include<inttypes.h>
#include<stdio.h>

uintptr_t read_int64(void) {
    uint64_t n;
    scanf("%" PRIu64, &n);
    return n;
}

void print_int64(int64_t n) {
    printf("%" PRIi64 "\n", n);
}

void print_float64(double x) {
    printf("%f\n", x);
}
