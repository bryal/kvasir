clang -c -o pcg_c.o src/core/pcg-c-basic/pcg_basic.c
clang -c -o core_c.o src/core/core.c
rm libcore.a
ar rcs libcore.a pcg_c.o core_c.o
rm pcg_c.o core_c.o
