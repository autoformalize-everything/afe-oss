#!/usr/bin/env python3
"""Checks references into the vendored C sources: `decompress.c:283`, `bzlib.c:825-847`.

A wrong citation was the commonest review finding, and it is mechanical to catch part of it:
the cited file must exist in upstream/ and the line or range must lie inside it. Whether the
lines say what is claimed is still for the author to re-read and the reviewer to spot-check.

Scans the Lean sources and their READMEs (spec, oracle, proofs, tests, fuzz). Write citations
as `file.c:LINE` or `file.c:FROM-TO`, optionally with a leading `upstream/`. Prints every bad
one as `file:line: message`; exit status 1 if any. Run from projects/bzip2.
"""

import re
import sys
from pathlib import Path

SRC_DIRS = ("spec", "oracle", "proofs", "tests", "fuzz")
CITE = re.compile(r"(?<![\w/.-])(?:upstream/)?([A-Za-z0-9_]+\.[ch]):(\d+)(?:\s*[-–]\s*(\d+))?")
MAX_RANGE = 400


def main() -> int:
    lengths: dict[str, int] = {}
    for f in Path("upstream").glob("*.[ch]"):
        lengths[f.name] = len(f.read_text(encoding="latin-1").splitlines())
    files = [f for d in SRC_DIRS for f in Path(d).rglob("*") if f.suffix in (".lean", ".md") and f.is_file()]
    bad = total = 0
    for f in sorted(files):
        for i, line in enumerate(f.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
            for m in CITE.finditer(line):
                total += 1
                name, a, b = m.group(1), int(m.group(2)), int(m.group(3) or m.group(2))
                msg = None
                if name not in lengths:
                    msg = f"no upstream/{name}"
                elif not 1 <= a <= b <= lengths[name]:
                    msg = f"{name} has {lengths[name]} lines"
                elif b - a > MAX_RANGE:
                    msg = f"a range of {b - a + 1} lines cites nothing in particular"
                if msg:
                    print(f"{f}:{i}: bad citation `{m.group(0)}`: {msg}")
                    bad += 1
    print(f"citations: {'ok' if not bad else f'{bad} bad'} ({total} checked)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
