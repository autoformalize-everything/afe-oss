#!/bin/sh
# Rebuilds the vendored libbz2 out of tree (with ../build-bzip2.sh), builds symbols.c against
# it, and regenerates the vector files here with generate.py. See ../README.md.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
up=$here/../../../upstream
b=$(sh "$here/../build-bzip2.sh")
d=$b/decompress-symbols
mkdir -p "$d"
objs="$b/blocksort.o $b/huffman.o $b/crctable.o $b/randtable.o $b/compress.o $b/decompress.o $b/bzlib.o"
gcc -O2 -I"$up" -o "$d/symbols" "$here/symbols.c" $objs
python3 -I "$here/generate.py" "$d/symbols" "$b/bzip2" "$here"
