#include<inttypes.h>
#include<stdio.h>

uintptr_t read_int(void) {
    uintptr_t n;
    scanf("%" PRIuPTR, &n);
    return n;
}

void print_int(uintptr_t n) {
    printf("%" PRIuPTR "\n", n);
}
