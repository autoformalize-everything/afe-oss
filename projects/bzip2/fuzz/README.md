# Differential fuzzing: the C library against the oracle

libFuzzer harnesses that feed the same input to the C library (built from
the vendored `../upstream`, copied to `build/` since `upstream/` is read-only, with sanitizers) and to the Lean oracle (linked in
as a static library), and abort on any disagreement.

Planned layout (the `bzip2/fuzz/*` tasks create it):

    ffi/                 Lean side: @[export] C entry points over Bzip2.Oracle, and their header
    build.sh             builds libbz2, the oracle library and the harnesses into build/
    run.sh TARGET SECS   runs one harness for SECS seconds on corpus/TARGET (seeded from corpus/seed)
    decompress_diff.c    same verdict (ok / magic / data / eof) and, on ok, the same bytes
    compress_diff.c      each side decompresses the other's output to the input; byte-identical
                         output once the oracle reproduces the C library exactly
    corpus/seed/         committed seed inputs; build/ and other corpora are not committed

Build and run the FFI smoke test from the repository root:

    projects/bzip2/fuzz/build.sh
    projects/bzip2/fuzz/build/ffi_smoke

The C API is in `ffi/bzip2_oracle.h`. Each call returns a libbz2 status code or
`BZIP2_ORACLE_UNIMPLEMENTED` (-10), and fills a result whose buffer is released with
`bzip2_oracle_result_free`. `decompress_stream` also reports the consumed input bytes. The
current oracle stream APIs are stubs, so the smoke test accepts their unimplemented status.
