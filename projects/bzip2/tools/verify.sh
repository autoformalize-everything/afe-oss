#!/bin/sh
# The checks every bzip2 task must leave passing; the fleet runs this as the task's verify.
# Works from any directory.
set -eu
cd "$(dirname "$0")/.."
log=$(mktemp)
trap 'rm -f "$log"' EXIT

step() {
  echo "== $*"
  if ! "$@" > "$log" 2>&1; then
    cat "$log"
    echo "verify: '$*' failed"
    exit 1
  fi
}

sh tools/use-image-packages.sh
if [ ! -L .lake/packages ]; then
  step lake exe cache get        # Mathlib's prebuilt .olean files (the image has them already)
fi
step lake build
if grep -n "declaration uses 'sorry'" "$log"; then
  echo "verify: the build uses sorry"
  exit 1
fi
step tools/check-sources.sh
step lake test
cat "$log"
echo "verify: ok"
