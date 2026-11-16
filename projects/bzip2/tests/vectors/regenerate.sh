#!/bin/sh
# Rebuilds the vendored bzip2 out of tree and regenerates every vector under
# tests/vectors/decompress and tests/vectors/compress. See README.md.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
build=$(sh "$here/build-bzip2.sh")
python3 -I "$here/generate.py" "$build"
rm -f "$build/out.tmp"
