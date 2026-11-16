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
