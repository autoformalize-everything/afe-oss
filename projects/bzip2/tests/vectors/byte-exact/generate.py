#!/usr/bin/env python3
"""Regenerate byte-exact compression vectors with the vendored bzip2 executable."""
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
BUILD = subprocess.check_output(["sh", str(HERE.parent / "build-bzip2.sh")], text=True).strip()
BZIP2 = Path(BUILD) / "bzip2"


def root1000():
    state = 1
    out = bytearray()
    for _ in range(1000):
        state = (state * 1103515245 + 12345) & 0xFFFFFFFF
        out.append((state >> 16) & 255)
    return bytes(out)


cases = {
    "empty": b"",
    "one": b"a",
    "abab-under": b"ab" * 4999,
    "abab-over": b"ab" * 5500,
    "same-under": b"a" * 9999,
    "same-over": b"a" * 11000,
    "pattern1000-under": root1000() * 9,
    "pattern1000-over": root1000() * 11,
}
for name, data in cases.items():
    case = HERE / name
    case.mkdir(exist_ok=True)
    (case / "input").write_bytes(data)
    for level in (1, 5, 9):
        z = subprocess.check_output([str(BZIP2), f"-{level}", "-c"], input=data)
        (case / f"level{level}.bz2").write_bytes(z)
