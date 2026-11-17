#!/bin/sh
set -eu

project=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
build="$project/fuzz/build"
mkdir -p "$build/upstream"
cp "$project/upstream/"*.c "$project/upstream/"*.h "$build/upstream/"

cc=${CC:-clang}
sanitizers='-fsanitize=address,undefined,fuzzer-no-link'
for source in blocksort huffman crctable randtable compress decompress bzlib; do
    "$cc" -std=gnu99 -O1 -g -fno-omit-frame-pointer $sanitizers \
        -I"$build/upstream" -c "$build/upstream/$source.c" -o "$build/$source.o"
done
ar rcs "$build/libbz2.a" \
    "$build/blocksort.o" "$build/huffman.o" "$build/crctable.o" \
    "$build/randtable.o" "$build/compress.o" "$build/decompress.o" "$build/bzlib.o"

cd "$project"
lake build Bzip2Oracle:static Bzip2Ffi:static
"$cc" -std=c11 -O1 -g -fno-omit-frame-pointer $sanitizers \
    -I"$project/fuzz/ffi" -I"$build/upstream" \
    -I"$(lean --print-prefix)/include" \
    -c fuzz/ffi/bzip2_oracle.c -o "$build/bzip2_oracle.o"
# clang 14's ASan crashes at startup in some position-independent executables when the kernel
# randomises mmap with 32 bits (vm.mmap_rnd_bits), so every program is linked -no-pie.
lean_prefix=$(lean --print-prefix)
link() { # OUTPUT SANITIZERS OBJECT
    "$cc" -no-pie -o "$1" $2 \
        -L"$lean_prefix/lib" -L"$lean_prefix/lib/lean" \
        -Wl,--start-group "$3" "$build/bzip2_oracle.o" \
        .lake/build/lib/libbzip2_Bzip2Ffi.a \
        .lake/build/lib/libbzip2_Bzip2Oracle.a "$build/libbz2.a" \
        -lInit -lleanrt -lcadical -Wl,--end-group \
        -Wl,-Bstatic -lc++ -lc++abi -lunwind -Wl,-Bdynamic \
        -lgmp -luv -lpthread -ldl -lm
}
for harness in ffi_smoke decompress_diff; do
    "$cc" -std=c11 -O1 -g -fno-omit-frame-pointer $sanitizers \
        -I"$project/fuzz/ffi" -I"$build/upstream" -I"$lean_prefix/include" \
        -c "fuzz/$harness.c" -o "$build/$harness.o"
done
link "$build/ffi_smoke" "$sanitizers" "$build/ffi_smoke.o"
link "$build/decompress_diff" "-fsanitize=address,undefined,fuzzer" "$build/decompress_diff.o"
