llc src/core.ll --filetype obj
cargo run -- $1 --emit obj
clang src/core.o ${1%.kvs}.o -o ${1%.kvs}.bin
./${1%.kvs}.bin
