#!/bin/sh
# Builds the vendored bzip2 and the `classify` driver out of tree (with ../build-bzip2.sh) and
# regenerates the vector files here with generate.py. See ../README.md.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
b=$(sh "$here/../build-bzip2.sh")
python3 -I "$here/generate.py" "$b/classify" "$b/bzip2" "$here"
