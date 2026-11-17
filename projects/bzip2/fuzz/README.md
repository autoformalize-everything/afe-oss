# Differential fuzzing: the C library against the oracle

libFuzzer harnesses that feed the same input to the C library (built from
the vendored `../upstream`, copied to `build/` since `upstream/` is read-only, with sanitizers) and to the Lean oracle (linked in
as a static library), and abort on any disagreement.

Layout (the `bzip2/fuzz/*` tasks create it):

    ffi/                 Lean side: @[export] C entry points over Bzip2.Oracle, and their header
    build.sh             builds libbz2, the oracle library and the harnesses into build/
    run.sh TARGET SECS   runs one harness for SECS seconds on corpus/TARGET (seeded from corpus/seed)
    decompress_diff.c    same verdict (ok / magic / data / eof) and, on ok, the same bytes
    compress_diff.c      each side decompresses the other's output to the input; byte-identical
                         output once the oracle reproduces the C library exactly (planned)
    corpus/seed/         committed seed inputs; build/ and other corpora are not committed
    make_seeds.py        rewrites corpus/seed/

Build and run the FFI smoke test from the repository root:

    projects/bzip2/fuzz/build.sh
    projects/bzip2/fuzz/build/ffi_smoke

The C API is in `ffi/bzip2_oracle.h`. Each call returns a libbz2 status code or
`BZIP2_ORACLE_UNIMPLEMENTED` (-10), and fills a result whose buffer is released with
`bzip2_oracle_result_free`. `decompress_stream` also reports the consumed input bytes.

Every program is linked `-no-pie`: clang 14's ASan crashes at startup (a bare `SIGSEGV`, before
`main`) in some runs of a position-independent executable on kernels that randomise `mmap`
with 32 bits.

## Differential decompression

`decompress_diff.c` decompresses its input with libbz2's `BZ2_bzBuffToBuffDecompress` (one
stream, `small` 0, a 16 MiB output buffer) and with the oracle's `decompressStream`, and aborts
unless both give the same verdict (`ok`, `magic`, `data`, `eof`) and, on `ok`, the same bytes
and the same number of input bytes consumed. `BZ_OUTBUFF_FULL` is skipped (the oracle has no
output limit). The header comment of `decompress_diff.c` says how each verdict and the consumed
count are obtained.

A mutation inside a block nearly always breaks the block's CRC, and then both sides say `data`.
So the harness has its own mutator: after libFuzzer's mutation, half the time, it rewrites the
first block's CRC and the combined CRC to match what libbz2 decodes. Mutated blocks then
decode, and their bytes are compared.

Run it from the repository root (it builds first when a source is newer than the binary):

    projects/bzip2/fuzz/run.sh decompress 120

It reads and grows `corpus/decompress/`, reads `corpus/seed/`, and writes a crashing input to
`build/artifacts/decompress/crash-<sha1>`, after printing a stable disagreement line (for
instance `AFE-FUZZ: verdict libbz2=data oracle=eof`). The exit status is non-zero when it
found something. The standing campaign is configured in afe-tasks' `tasks/bzip2/fuzz.toml`
and run by `afe-fleet fuzz run`.

Longer campaigns: arguments after the seconds go to libFuzzer and override the defaults
(`-timeout=60`). In parallel, sharing one corpus and carrying on past crashes:

    projects/bzip2/fuzz/run.sh decompress 3600 -fork=16 -ignore_crashes=1

`-max_len=N` bounds the input size (by default the largest seed, 73732 bytes); small inputs run
much faster. Every crash lands in `build/artifacts/decompress/`. Shrink the corpus now and then
(`-merge=1` into a fresh directory, then replace `corpus/decompress/` with it):

    projects/bzip2/fuzz/build/decompress_diff -merge=1 /tmp/merged \
        projects/bzip2/fuzz/corpus/decompress projects/bzip2/fuzz/corpus/seed

Reproduce and minimise a crash:

    projects/bzip2/fuzz/build/decompress_diff projects/bzip2/fuzz/build/artifacts/decompress/crash-...
    projects/bzip2/fuzz/build/decompress_diff -minimize_crash=1 -runs=100000 \
        -exact_artifact_path=/tmp/min projects/bzip2/fuzz/build/artifacts/decompress/crash-...

The first line runs the one input and prints the failed check. The second writes a smaller
input with the same crash to `/tmp/min` (it accepts any crash; check that `/tmp/min` prints the
same check). Compare with the vendored `bzip2 -d` and the oracle CLI:

    b=$(sh projects/bzip2/tests/vectors/build-bzip2.sh)
    "$b/classify" /tmp/min /tmp/min.out                       # ok | magic | data | eof
    (cd projects/bzip2 && lake build bzip2-oracle && .lake/build/bin/bzip2-oracle -d < /tmp/min)

`classify` and the oracle CLI decode concatenated streams as `bzip2 -d` does; the harness looks
at the first stream only. A disagreement is either an oracle bug, fixed in
`oracle/Bzip2/Oracle/Decompress*` with the input added as a golden case in
`tests/vectors/generate.py`, or a question for the spec (`bzip2/spec/*`).

## Seeds

`corpus/seed/` holds the upstream samples (`upstream/sample{1,2,3}.bz2`) and hand-made streams:
the empty stream, short level 1 and level 9 streams, runs for the run-length stages, two
concatenated streams, a stream with trailing garbage, a truncated stream, and a one-block
stream with the randomised flag set and its CRCs fixed so that it decodes. The `made-*` seeds
are blocks no compressor writes, built by `make_seeds.py` from a BWT output and an `origPtr`
of its choice: a run of 259, four equal bytes at the end of a block (with and without the count
byte), 18010 selectors, an `origPtr` that starts the walk elsewhere, 100 000 and 100 001 bytes
in a level-1 block, and two blocks. Each comment in `make_seeds.py` cites the C code involved.
Regenerate them:

    b=$(sh projects/bzip2/tests/vectors/build-bzip2.sh)
    python3 projects/bzip2/fuzz/make_seeds.py "$b"

`git status` must show no change afterwards.
