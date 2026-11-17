#!/usr/bin/env python3
"""Compare the compiled oracle with fixed vendored compressed streams, byte for byte."""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ORACLE = HERE.parents[2] / ".lake/build/bin/bzip2-oracle"
if not ORACLE.is_file():
    sys.exit("build the oracle first: cd projects/bzip2 && lake build bzip2-oracle")

passed = 0
for case in sorted(HERE.iterdir()):
    if not case.is_dir():
        continue
    data = (case / "input").read_bytes()
    for level in (1, 5, 9):
        expected = (case / f"level{level}.bz2").read_bytes()
        actual = subprocess.check_output([str(ORACLE), "-z", f"-{level}"], input=data)
        if actual != expected:
            pos = next((i for i, (a, b) in enumerate(zip(actual, expected)) if a != b),
                       min(len(actual), len(expected)))
            sys.exit(f"FAIL {case.name} level{level}: first difference at byte {pos}")
        passed += 1
print(f"byte-exact: {passed} passed, 0 failed")
