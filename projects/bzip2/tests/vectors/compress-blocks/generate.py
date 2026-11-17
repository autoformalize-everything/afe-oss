#!/usr/bin/env python3
"""Regenerates the vectors of `Bzip2.Test.CompressBlocks` from the vendored libbz2.

    python3 tests/vectors/compress-blocks/generate.py

The C side is an out-of-tree copy of `upstream/` (in a temporary directory) with one debug print
added at the top of `BZ2_compressBlock` (`compress.c:601-607`): for each block that is compressed,
`nblock`, the finalised `blockCRC`, an FNV-1a hash of `block[0 .. nblock-1]` and `inUse` as hex.
Each input is compressed twice at its level: as `bzip2` drives the library (`BZ_RUN` calls of
5000 bytes, then an empty `BZ_FINISH`) and as `BZ2_bzBuffToBuffCompress` does (one `BZ_FINISH`).
Nothing is written under the repository except the `*.txt` files here.
"""
import os
import subprocess
import sys
import tempfile

here = os.path.dirname(os.path.abspath(__file__))
upstream = os.path.join(here, "..", "..", "..", "upstream")

DRIVER = r"""
#include <stdio.h>
#include <stdlib.h>
#include "bzlib.h"
int main(int argc, char **argv) {
  int level = atoi(argv[1]), oneshot = atoi(argv[2]);
  static unsigned char in[3000000];
  static char out[4000000];
  unsigned n = fread(in, 1, sizeof in, stdin), olen = sizeof out;
  if (oneshot) return BZ2_bzBuffToBuffCompress(out, &olen, (char *)in, n, level, 0, 0);
  bz_stream st = {0};
  if (BZ2_bzCompressInit(&st, level, 0, 0) != BZ_OK) return 1;
  st.next_out = out; st.avail_out = olen;
  for (unsigned p = 0; p < n;) {
    unsigned c = n - p > 5000 ? 5000 : n - p;
    st.next_in = (char *)in + p; st.avail_in = c;
    if (BZ2_bzCompress(&st, BZ_RUN) != BZ_RUN_OK) return 2;
    p += c;
  }
  st.avail_in = 0; st.next_in = (char *)in;
  return BZ2_bzCompress(&st, BZ_FINISH) == BZ_STREAM_END ? 0 : 3;
}
"""

PRINT = r"""   if (s->nblock > 0) {

      BZ_FINALISE_CRC ( s->blockCRC );
      { UInt32 h = 2166136261u; Int32 q;
        for (q = 0; q < s->nblock; q++) h = (h ^ s->block[q]) * 16777619u;
        fprintf(stderr, "block %d %08x %08x ", s->nblock, s->blockCRC, h);
        for (q = 0; q < 256; q += 4)
          fprintf(stderr, "%x", s->inUse[q] | s->inUse[q+1] << 1 | s->inUse[q+2] << 2
                                | s->inUse[q+3] << 3);
        fprintf(stderr, "\n"); }"""


def build(tmp):
    src = os.path.join(tmp, "src")
    os.mkdir(src)
    for f in os.listdir(upstream):
        if f.endswith(".c") or f.endswith(".h"):
            with open(os.path.join(upstream, f), "rb") as r, open(os.path.join(src, f), "wb") as w:
                w.write(r.read())
    path = os.path.join(src, "compress.c")
    text = open(path).read()
    old = "   if (s->nblock > 0) {\n\n      BZ_FINALISE_CRC ( s->blockCRC );"
    assert text.count(old) == 1
    open(path, "w").write(text.replace(old, PRINT))
    open(os.path.join(tmp, "drv.c"), "w").write(DRIVER)
    exe = os.path.join(tmp, "drv")
    c = [os.path.join(src, f) for f in
         ["blocksort.c", "huffman.c", "crctable.c", "randtable.c", "compress.c",
          "decompress.c", "bzlib.c"]]
    subprocess.check_call(["gcc", "-O2", "-I" + src, "-o", exe, os.path.join(tmp, "drv.c")] + c)
    return exe


def make_input(segs):
    """`run B N`: N copies of byte B; `seq N`: bytes 0, 1, ..., 255, 0, ...; `pairs N`: N runs of
    four bytes, alternately 10 and 11."""
    out = bytearray()
    i = 0
    while i < len(segs):
        k = segs[i]
        if k == "run":
            out += bytes([int(segs[i + 1])]) * int(segs[i + 2])
            i += 3
        elif k == "seq":
            out += bytes(j % 256 for j in range(int(segs[i + 1])))
            i += 2
        elif k == "pairs":
            for j in range(int(segs[i + 1])):
                out += bytes([10 + j % 2]) * 4
            i += 2
        else:
            raise ValueError(k)
    return bytes(out)


CASES = []


def case(name, level, *segs):
    CASES.append((name, level, [str(s) for s in segs]))


# Level 1: nblockMAX = 99 981.
case("empty-l1", 1)
case("byte-l1", 1, "run", 65, 1)
case("short-runs-l1", 1, "run", 1, 1, "run", 2, 2, "run", 3, 3, "run", 4, 4, "run", 5, 5)
for n in (99980, 99981, 99982, 99983, 199964):
    case(f"seq{n}-l1", 1, "seq", n)
# Runs across the block boundary: a 600-byte run (255 + 255 + 90) after k distinct bytes.
for k in (99974, 99976, 99978, 99980, 99981, 99982, 99983):
    case(f"seq{k}-run600-l1", 1, "seq", k, "run", 9, 600, "seq", 7)
for r in (255, 256, 511):
    case(f"run{r}-l1", 1, "run", 5, r)
case("seq99978-run255-l1", 1, "seq", 99978, "run", 9, 255)
case("seq99978-run256-l1", 1, "seq", 99978, "run", 9, 256)
case("pairs19996-l1", 1, "pairs", 19996)
case("pairs19996-run600-l1", 1, "pairs", 19996, "run", 3, 600)
case("pairs19997-run600-l1", 1, "pairs", 19997, "run", 3, 600)
case("run100000-seq99900-l1", 1, "run", 0, 100000, "seq", 99900)
# Level 9: nblockMAX = 899 981.
case("empty-l9", 9)
case("seq899981-l9", 9, "seq", 899981)
case("seq899982-l9", 9, "seq", 899982)
case("seq899977-run600-l9", 9, "seq", 899977, "run", 9, 600, "seq", 7)


def main():
    with tempfile.TemporaryDirectory() as tmp:
        exe = build(tmp)
        for name, level, segs in CASES:
            data = make_input(segs)
            lines = ["input " + " ".join(segs), f"level {level}"]
            for oneshot, label in ((0, "program"), (1, "oneshot")):
                p = subprocess.run([exe, str(level), str(oneshot)], input=data,
                                   capture_output=True, check=True)
                lines.append(label)
                lines += [l for l in p.stderr.decode().splitlines() if l.startswith("block ")]
            with open(os.path.join(here, name + ".txt"), "w") as f:
                f.write("\n".join(lines) + "\n")
        print(len(CASES), "cases", file=sys.stderr)


main()
