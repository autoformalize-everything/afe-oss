# Golden vectors

Inputs and expected results for `lake test` (`tests/Bzip2/Tests.lean`). Expected results come
from the vendored bzip2 (`../../upstream`, built out of tree), never from the oracle.

## Format

One directory per case.

`decompress/<case>/`
- `input`: bytes given to `Oracle.decompress` (`bzip2 -d` semantics: concatenated streams).
- exactly one of
  - `expected`: the decompressed bytes, or
  - `error`: one line, the error class: `magic` (`BZ_DATA_ERROR_MAGIC`), `data`
    (`BZ_DATA_ERROR`, including CRC mismatches), `eof` (`BZ_UNEXPECTED_EOF`). The runner compares
    the oracle's `Error` constructor only, not its detail text.

`compress/<case>/`
- `input`: raw bytes. For levels 1 and 9 the runner checks that `Oracle.compress` succeeds and
  that its output decompresses to `input` through the oracle and through the vendored
  `bzip2 -d`. Byte identity with the vendored compressor is not checked here (that is
  `oracle/compress/byte-exact`).

Results: `PASS`, `SKIP` (the oracle function returned `Error.unimplemented`), `FAIL`. `lake test`
prints the counts and exits non-zero if any case failed.

## Cases

Decompression: the upstream samples 1-3, the empty stream, all 256 byte values, runs of 3, 4, 5,
255, 256 and 100 000 equal bytes, `block-at-limit` / `block-over-limit` (level 1, 99 981 and
99 982 bytes with no runs: `nblockMAX` is `100000 * level - 19`, `upstream/bzlib.c:194`, so the
first fills one block exactly and the second needs two), two concatenated streams, trailing
garbage (ignored after a first stream, as `uncompressStream` in `upstream/bzip2.c` does); errors:
truncated in the header (`trunc-header`), mid-block, in the footer, a flipped bit in the first
block CRC, bad magic, level `0` (`BZh0`; the header check rejects it as bad magic), and a
zero-length input.

## Regenerating

    sh tests/vectors/regenerate.sh

`build-bzip2.sh` builds `bzip2` and `classify` (`classify.c`, a driver that runs libbz2 as
`uncompressStream` does and reports `ok|magic|data|eof`) from `upstream/` into
`$BZIP2_BUILD` (default `${TMPDIR:-/tmp}/bzip2-golden-build`), outside the repository.
`generate.py` rewrites every case, deterministically, and asserts that the outcome of each
named case is the one intended. Afterwards `git status` must show no change. The runner uses the
same build for the `bzip2 -d` check; set `BZIP2_VECTORS` to run against another vectors directory.
