# bzip2

| | |
|---|---|
| Upstream | https://sourceware.org/git/bzip2.git (homepage https://sourceware.org/bzip2/) |
| Commit | `f5dfc96063fef2d9c5446d0733867d899ef9b942` (2026-07-11, "bzip2recover: create output block files safely with O_EXCL") |
| Release base | `bzip2-1.0.8` plus 21 later upstream fixes; the public API is that of 1.0.8 |
| License | bzip2's BSD-style license, `upstream/LICENSE` |

`upstream/` is `git archive` of that commit, unmodified. Do not edit it: changes to bzip2 itself
go upstream. To move the pin, replace the directory with a newer `git archive` and update this
file in the same commit.

## Layout

- `upstream/`: the vendored source. `bzlib.h` is the public API; `Makefile` builds `libbz2.a`,
  `bzip2` and `bzip2recover`.
- `docs/`: documentation produced by fleet tasks.
  - `surface-area.md`, `surface-area.json`: everything outside code can touch (task
    `bzip2/surface-area`).
- `spec/`, `oracle/`, `proofs/`, `fuzz/`, `tests/`: the Lean formalization (below).
- `tools/check_surface.py`: derives the surface from the source (public declarations, symbols
  exported by the library objects, `BZ_*` macros, installed programs) and checks that the docs
  cover all of it. `--only-docs` also rejects changes outside `docs/`.
- `tools/verify.sh`: what every formalization task must leave passing (below), with
  `check-sources.sh`, `lean_holes.py` and `use-image-packages.sh`.

```sh
python3 projects/bzip2/tools/check_surface.py --only-docs
```

It needs `cc`, `nm` and `python3`; it compiles the library in a temporary directory.

## The Lean formalization

A specification of the format, an executable Lean implementation (the oracle) proven to meet
it, and a differential fuzzer that holds the C library and the oracle to the same behaviour. It
is a Lake package rooted here (`lakefile.toml`; Lean 4.36, Mathlib v4.36.0).

| Directory | What | Lean library |
|---|---|---|
| `spec/` | What a bzip2 stream is and what it decodes to, stated declaratively | `Bzip2Spec` (`Bzip2.Spec.*`) |
| `oracle/` | The executable implementation: `decompress`, `decompressStream`, `compress`; the `bzip2-oracle` CLI | `Bzip2Oracle` (`Bzip2.Oracle.*`) |
| `proofs/` | Proofs that the oracle meets the spec | `Bzip2Proofs` (`Bzip2.Proofs.*`) |
| `fuzz/` | libFuzzer harnesses comparing libbz2 and the oracle ([fuzz/README.md](fuzz/README.md)) | |
| `tests/` | Golden vectors, run by `lake test` | |

Behaviour is the vendored source's (`upstream/`), and where any description disagrees with it,
the source wins. `docs/surface-area.md` is the cited inventory of that source (API, programs,
format); Joe Tsai's "The bzip2 file format" (github.com/dsnet/compress, `doc/bzip2-format.pdf`)
is a readable companion.

Rules:

- `spec/` imports Mathlib only. `oracle/` imports Lean core and `Std` only: no Mathlib, no spec,
  so the executable and the fuzzer's static library stay small. `proofs/` imports both.
- No `sorry`, `admit` or new `axiom` anywhere. Unfinished proofs are not committed; split the
  work instead and report what is left as `progress` or `followups`.
- One module per part, named as in the module docs of `Bzip2/Spec.lean`, `Bzip2/Oracle.lean`
  and `Bzip2/Proofs.lean`. Lake builds every module under each root by glob, so a part is added
  by adding its file, and a module imports the parts it needs directly
  (`import Bzip2.Spec.Crc`). **Do not edit the three root files** or any other file your task
  does not own: files several tasks touch conflict as soon as one of them merges, and
  `tools/check-sources.sh` rejects changes to the roots.
- The oracle's public API: `Error` in `oracle/Bzip2/Oracle/Error.lean` (fixed; parts import it
  for the error type), `decompressStream` and `decompress` in `Oracle/Decompress.lean` (owned by
  task `oracle/decompress/stream`), `compress` in `Oracle/Compress.lean` (owned by
  `oracle/compress/stream`). `Bzip2.Oracle` re-exports them for the CLI, tests and fuzzer FFI.
  Change a signature only together with its users, in the same change.
- Unit tests of a part go in their own module, `tests/Bzip2/Test/<Part>.lean`, as `#guard` and
  `example`: building them runs them. `tests/Bzip2/Tests.lean`, the golden-vector runner behind
  `lake test`, belongs to task `tests/golden`.
- Prefer definitions that are easy to reason about in the spec, and fast enough to run on
  100 MB inputs in the oracle (`ByteArray`, `Array`, `UInt32`; no `List` on hot paths).
- `upstream/` and `tools/` are not changed by tasks. Builds of the C code happen out of tree.

Build and check, from the repository root:

```sh
docker build -t afe-bzip2-lean:dev -f images/bzip2-lean/Dockerfile projects/bzip2   # once per host
projects/bzip2/tools/verify.sh     # packages, lake build with no sorry, source rules, lake test
```

The image carries the Lake dependencies of `lake-manifest.json`, Mathlib's build included,
read-only in `/opt/bzip2-lake/.lake/packages`. `tools/use-image-packages.sh` (the fleet runs it
as the project's `prepare`, and `verify.sh` runs it too) makes `.lake/packages` a symlink to
them, so a fresh checkout builds in seconds, offline, instead of cloning and unpacking about 7 GB.
Outside the image the script does nothing and Lake fetches packages as usual. Changing
`lake-manifest.json` means rebuilding the image; the script refuses a mismatch.

The tasks are in afe-tasks under `tasks/bzip2/`.
