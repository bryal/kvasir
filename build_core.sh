clang -c -o pcg_c.o src/core/pcg-c-basic/pcg_basic.c
clang -c -o core_c.o src/core/core.c
llc -filetype obj -relocation-model pic -o core_ll.o src/core/core.ll
rm libcore.a
ar rcs libcore.a pcg_c.o core_c.o core_ll.o
rm pcg_c.o core_c.o core_ll.o
