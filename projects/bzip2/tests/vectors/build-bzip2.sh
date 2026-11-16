#!/bin/sh
# Builds the vendored bzip2 (upstream/) out of tree and prints the build directory. The build
# directory is $BZIP2_BUILD, default ${TMPDIR:-/tmp}/bzip2-golden-build. It holds `bzip2` and
# `classify` (see classify.c). Nothing is written under the repository.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
up=$here/../../upstream
b=${BZIP2_BUILD:-${TMPDIR:-/tmp}/bzip2-golden-build}
if [ ! -x "$b/bzip2" ] || [ ! -x "$b/classify" ]; then
  mkdir -p "$b"
  for f in blocksort huffman crctable randtable compress decompress bzlib bzip2; do
    gcc -O2 -D_FILE_OFFSET_BITS=64 -I"$up" -c "$up/$f.c" -o "$b/$f.o"
  done
  gcc -O2 -I"$up" -c "$here/classify.c" -o "$b/classify.o"
  objs="$b/blocksort.o $b/huffman.o $b/crctable.o $b/randtable.o $b/compress.o $b/decompress.o $b/bzlib.o"
  gcc -o "$b/bzip2" "$b/bzip2.o" $objs
  gcc -o "$b/classify" "$b/classify.o" $objs
fi
echo "$b"
