clang -c -o core_c.o src/core.c
llc -filetype obj -relocation-model pic -o core_ll.o src/core.ll
ar rcs libcore.a core_c.o core_ll.o
rm core_c.o core_ll.o
