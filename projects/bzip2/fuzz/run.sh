#!/bin/sh
# run.sh TARGET SECONDS [LIBFUZZER-OPTION...]
#
# Runs the harness TARGET_diff.c for SECONDS seconds on corpus/TARGET/, which it creates and
# grows, seeded from corpus/seed/. Builds first (build.sh) when the harness is missing or older
# than any source. Crashes go to build/artifacts/TARGET/. Exits non-zero when libFuzzer finds
# something. Further arguments go to libFuzzer, after the defaults, so they override them.
set -eu

if [ $# -lt 2 ]; then
    echo "usage: $0 TARGET SECONDS [LIBFUZZER-OPTION...]" >&2
    exit 2
fi
target=$1
seconds=$2
shift 2

fuzz=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project=$(dirname -- "$fuzz")
harness="$fuzz/build/${target}_diff"
if [ ! -f "$fuzz/${target}_diff.c" ]; then
    echo "run.sh: no harness $fuzz/${target}_diff.c" >&2
    exit 2
fi

stale=yes
if [ -x "$harness" ]; then
    stale=$(find "$fuzz"/*.c "$fuzz/build.sh" "$fuzz/ffi" "$project/oracle" \
                 "$project/upstream" "$project/lakefile.toml" \
                 -newer "$harness" -type f -print | head -n 1)
fi
if [ -n "$stale" ]; then
    "$fuzz/build.sh"
fi

corpus="$fuzz/corpus/$target"
artifacts="$fuzz/build/artifacts/$target"
mkdir -p "$corpus" "$artifacts"
exec "$harness" -max_total_time="$seconds" -timeout=60 -print_final_stats=1 \
    -artifact_prefix="$artifacts/" "$@" "$corpus" "$fuzz/corpus/seed"
