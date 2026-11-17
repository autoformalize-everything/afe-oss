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
"$cc" -std=c11 -O1 -g -fno-omit-frame-pointer $sanitizers \
    -I"$build/upstream" -I"$(lean --print-prefix)/include" \
    -c fuzz/ffi_smoke.c -o "$build/ffi_smoke.o"
"$cc" -o "$build/ffi_smoke" $sanitizers \
    -L"$(lean --print-prefix)/lib" -L"$(lean --print-prefix)/lib/lean" \
    -Wl,--start-group "$build/ffi_smoke.o" "$build/bzip2_oracle.o" \
    .lake/build/lib/libbzip2_Bzip2Ffi.a \
    .lake/build/lib/libbzip2_Bzip2Oracle.a "$build/libbz2.a" \
    -lInit -lleanrt -lcadical -Wl,--end-group \
    -Wl,-Bstatic -lc++ -lc++abi -lunwind -Wl,-Bdynamic \
    -lgmp -luv -lpthread -ldl -lm
