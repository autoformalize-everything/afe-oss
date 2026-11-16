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
- `STYLE.md`, `checks/`: the formalization's rules, and what each task must provide.
- `tools/verify.sh`: what every formalization task must leave passing (below), in named stages,
  with the checkers it runs; `tools/check-task.sh`; `tools/use-image-packages.sh`.

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

The rules are in [STYLE.md](STYLE.md): one module per part in the namespace named after it,
no shared files between tasks (Lake builds every module by glob, and the root modules are never
edited), citations of the C source as `file.c:LINE`, no `sorry`, `native_decide`, heartbeat
overrides or silenced linters. `checks/<task>.lean` states what each task must provide, under
the names other tasks import.

Build and check, from the repository root:

```sh
docker build -t afe-bzip2-lean:dev -f images/bzip2-lean/Dockerfile projects/bzip2   # once per host
projects/bzip2/tools/verify.sh                 # every stage
projects/bzip2/tools/verify.sh build style     # only these, after fixing what they reported
projects/bzip2/tools/check-task.sh spec/rle1   # what that task must provide
```

`verify.sh` runs named stages and ends each with `verify: STAGE: ok` or `FAILED`:

| Stage | Checks |
|---|---|
| `packages` | the Lake packages are in place (the image's prebuilt copy, or `lake exe cache get`) |
| `sources` | no `sorry`/`admit`/`axiom`, the import rules, untouched root modules, citations that exist (`check-sources.sh`, `check_citations.py`) |
| `build` | `lake build`: every module by glob, the `#guard` unit tests included |
| `style` | STYLE.md's source rules (`lint_style.py`), and no warning from Lean's or Mathlib's linters in our sources |
| `axioms` | every declaration rests on `propext`, `Classical.choice`, `Quot.sound` only (`lean_audit.py`) |
| `lint` | environment linters: doc strings, unused arguments and `have`s, tautologies (`lean_audit.py`) |
| `test` | `lake test`: the golden vectors |

The image carries the Lake dependencies of `lake-manifest.json`, Mathlib's build included,
read-only in `/opt/bzip2-lake/.lake/packages`. `tools/use-image-packages.sh` (the fleet runs it
as the project's `prepare`, and `verify.sh` runs it too) makes `.lake/packages` a symlink to
them, so a fresh checkout builds in seconds, offline, instead of cloning and unpacking about 7 GB.
Outside the image the script does nothing and Lake fetches packages as usual. Changing
`lake-manifest.json` means rebuilding the image; the script refuses a mismatch.

The tasks are in afe-tasks under `tasks/bzip2/`.
