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
- `tools/check_surface.py`: derives the surface from the source (public declarations, symbols
  exported by the library objects, `BZ_*` macros, installed programs) and checks that the docs
  cover all of it. `--only-docs` also rejects changes outside `docs/`.

```sh
python3 projects/bzip2/tools/check_surface.py --only-docs
```

It needs `cc`, `nm` and `python3`; it compiles the library in a temporary directory.
