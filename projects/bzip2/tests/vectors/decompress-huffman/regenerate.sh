#!/bin/sh
# Rebuilds the vendored libbz2 out of tree (with ../build-bzip2.sh), builds huff.c against it,
# and regenerates the vector files here with generate.py. See ../README.md.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
up=$here/../../../upstream
b=$(sh "$here/../build-bzip2.sh")
d=$b/decompress-huffman
mkdir -p "$d"
# GET_MTF_VAL and the macros it uses, as the vendored source has them.
sed -n 40,102p "$up/decompress.c" > "$d/mtfval.h"
head -1 "$d/mtfval.h" | grep -q '^#define RETURN' || { echo "decompress.c moved" >&2; exit 1; }
tail -1 "$d/mtfval.h" | grep -q '^}' || { echo "decompress.c moved" >&2; exit 1; }
objs="$b/blocksort.o $b/huffman.o $b/crctable.o $b/randtable.o $b/compress.o $b/decompress.o $b/bzlib.o"
gcc -O2 -I"$up" -I"$d" -o "$d/huff" "$here/huff.c" $objs
python3 -I "$here/generate.py" "$d/huff" "$b/bzip2" "$here"
