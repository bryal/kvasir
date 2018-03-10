cd src/core
cargo build --release
cd ../../
cp src/core/target/release/libkvasir_core.a ./libcore.a
