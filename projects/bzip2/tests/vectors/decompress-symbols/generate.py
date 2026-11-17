"""Writes the vectors in this directory. Streams are made here (real ones by the vendored
bzip2, synthetic blocks by the bit writer below), and every result is what the vendored C code
printed (symbols.c). Usage: generate.py SYMBOLS BZIP2 OUTDIR. Deterministic."""
import os
import random
import subprocess
import sys
import tempfile

symbols_exe, bzip2, outdir = sys.argv[1:4]
rng = random.Random(7)


def bits(value, n):
    return format(value, "0%db" % n)


def tobytes(bs):
    bs += "0" * (-len(bs) % 8)
    return bytes(int(bs[i:i + 8], 2) for i in range(0, len(bs), 8))


def codes(lens):
    """Canonical codes (BZ2_hbAssignCodes, huffman.c:152-166), as bit strings."""
    out = [None] * len(lens)
    vec = 0
    for n in range(min(lens), max(lens) + 1):
        for i, l in enumerate(lens):
            if l == n:
                out[i] = bits(vec, n)
                vec += 1
        vec <<= 1
    return out


def header_bits(used, groups, selectors, orig_ptr):
    """Everything after the block magic up to the first symbol (decompress.c:241-352)."""
    out = bits(0, 32) + "0" + bits(orig_ptr, 24)
    top = [any(16 * i <= u < 16 * i + 16 for u in used) for i in range(16)]
    out += "".join("1" if t else "0" for t in top)
    for i in range(16):
        if top[i]:
            out += "".join("1" if 16 * i + j in used else "0" for j in range(16))
    out += bits(len(groups), 3) + bits(len(selectors), 15)
    pos = list(range(len(groups)))
    for g in selectors:  # selectors are move-to-front coded (decompress.c:311-319)
        v = pos.index(g)
        out += "1" * v + "0"
        pos.insert(0, pos.pop(v))
    for lens in groups:  # delta-coded lengths (decompress.c:321-337)
        curr = lens[0]
        out += bits(curr, 5)
        for target in lens:
            while curr != target:
                out += "10" if target > curr else "11"
                curr += 1 if target > curr else -1
            out += "0"
    return out


def coded(groups, selectors, syms):
    """The symbols' codes, each group of 50 with its selector's table; symbols past the last
    selector (which the decoder rejects) use the last one's."""
    cs = [codes(l) for l in groups]
    return "".join(cs[selectors[min(i // 50, len(selectors) - 1)]][s]
                   for i, s in enumerate(syms))


def stream(level, used, groups, selectors, syms, orig_ptr=0, eob=True, trailer=True):
    """A stream of one block with the symbols `syms` (EOB appended if `eob`)."""
    eob_sym = len(used) + 1
    allsyms = syms + ([eob_sym] if eob else [])
    body = (header_bits(used, groups, selectors, orig_ptr)
            + coded(groups, selectors, allsyms))
    bs = "".join(bits(b, 8) for b in b"BZh%d" % level) + bits(0x314159265359, 48) + body
    if trailer:
        bs += bits(0x177245385090, 48) + bits(0, 32)
    return tobytes(bs)


def run(n):
    """RUNA/RUNB digits of a run of length n (bijective base 2, decompress.c:392-401)."""
    out = []
    while n > 0:
        n -= 1
        out.append(n % 2)
        n //= 2
    return out


def result(path):
    return subprocess.run([symbols_exe, path], capture_output=True, text=True,
                          check=True).stdout


tmp = tempfile.mkdtemp()


def case(comment, level, data, expect=None):
    """One vector: the stream, and what the C code printed for it. `expect` is the intended
    first line (`result ok|data|eof`), asserted."""
    path = os.path.join(tmp, "case.bz2")
    with open(path, "wb") as f:
        f.write(data)
    out = result(path)
    if expect is not None:
        assert out.split("\n")[0] == "result " + expect, (comment, out[:80])
    return "# %s\nlevel %d\nhex %s\n%s\n" % (comment, level, data.hex(), out)


def write(name, cases):
    with open(os.path.join(outdir, name), "w") as f:
        f.write("\n".join(cases))


USED = [97, 98, 99]               # symbols: RUNA, RUNB, 2, 3, EOB (= 4)
G0 = [2, 2, 2, 3, 3]              # complete code sets over the five symbols
G1 = [1, 2, 3, 4, 4]


def fit(syms, residue=0, prefix=3):
    """`syms` with copies of the 3-bit-coded symbol `prefix` in front, until the coded block
    ends at bit `residue` of a byte (the header before it is whole bytes plus this much)."""
    for k in range(8):
        s = [prefix] * k + syms
        n = len(header_bits(USED, [G0, G0], [0] * 400, 0)) + len(coded([G0, G0], [0] * 400, s))
        if n % 8 == residue:
            return s
    raise AssertionError


def trunc(level, syms, residue):
    """A stream that stops, without EOB or trailer, after `syms` (and one filler bit when the
    residue is 7: too few bits left for any symbol)."""
    s = fit(syms, residue)
    bs = ("".join(bits(b, 8) for b in b"BZh%d" % level) + bits(0x314159265359, 48)
          + header_bits(USED, [G0, G0], [0] * 400, 0) + coded([G0, G0], [0] * 400, s))
    return tobytes(bs + "1" * (residue == 7))


# --- Real streams, made by the vendored bzip2 -------------------------------------------
words = ["alpha", "beta", "gamma", "delta", "huffman", "table", "code", "limit", "base",
         "perm", "symbol", "stream", "block", "the", "of", "and", "a", "to", "in", "is"]
inputs = [
    ("hello hello hello, bzip2! repeated", 1, b"hello hello hello, bzip2! " * 3),
    ("text, about 2.5 kB", 9, " ".join(rng.choice(words) for _ in range(400)).encode()),
    ("random bytes, 1500", 1, bytes(rng.randrange(256) for _ in range(1500))),
    ("runs of every length up to 300 (long RUNA/RUNB runs)", 9,
     b"".join(bytes([65 + i % 7]) * i for i in range(1, 30)) + b"x" * 300),
    ("all 256 byte values", 1, bytes(range(256)) * 2),
    ("two symbols, 50 kB text (hash only: more than 4096 bytes)", 9,
     "".join(rng.choice("ab ") for _ in range(50000)).encode()),
    ("text, 30 kB at level 1 (several selectors)", 1,
     " ".join(rng.choice(words) for _ in range(5000)).encode()),
]
real = []
for comment, level, data in inputs:
    z = subprocess.run([bzip2, "-%d" % level, "-c"], input=data, capture_output=True,
                       check=True).stdout
    real.append(case("%s, bzip2 -%d" % (comment, level), level, z, "ok"))
write("real.txt", real)

# --- Synthetic blocks: runs, move-to-front, groups --------------------------------------
sym_cases = []
body = [rng.choice([0, 1, 2, 2, 3, 3, 3]) for _ in range(120)]
sym_cases.append(case("120 random symbols over three groups of 50 (two tables)", 1,
                      stream(1, USED, [G0, G1], [0, 1, 0], body), "ok"))
sym_cases.append(case("selector order 1,1,0 (move-to-front coded selectors)", 1,
                      stream(1, USED, [G0, G1], [1, 1, 0], body), "ok"))
sym_cases.append(case("move to front of every entry, then RUNB", 1,
                      stream(1, USED, [G0, G0], [0], [2, 3, 3, 2, 3, 2, 2, 1, 3, 0, 3]), "ok"))
sym_cases.append(case("runs RUNA RUNA RUNB (length 1+2+4... digits) then bytes", 1,
                      stream(1, USED, [G0, G0], [0],
                             [3, 0, 0, 1, 2, 1, 1, 1, 0, 3, 3, 0]), "ok"))
write("symbols.txt", sym_cases)

# --- Limits ----------------------------------------------------------------------------
lim = []
two = [G0, G0]
sel = [0] * 100
lim.append(case("run of 100000 at level 1 (exactly the block size)", 1,
                stream(1, USED, two, sel, run(100000)), "ok"))
lim.append(case("run of 100001 at level 1 (one byte over)", 1,
                stream(1, USED, two, sel, run(100001)), "data"))
lim.append(case("run of 100001 at level 2 (the limit scales with the level)", 2,
                stream(2, USED, two, sel, run(100001)), "ok"))
lim.append(case("run of 99999 then a symbol: the last byte of the block", 1,
                stream(1, USED, two, sel, run(99999) + [2]), "ok"))
lim.append(case("run of 100000 then a symbol: one byte over", 1,
                stream(1, USED, two, sel, run(100000) + [2]), "data"))
lim.append(case("runs of 50000 and 49998 between symbols: exactly 100000 bytes", 1,
                stream(1, USED, two, sel, run(50000) + [2] + run(49998) + [3]), "ok"))
lim.append(case("runs of 50000 and 49999 between symbols: 100001 bytes (data)", 1,
                stream(1, USED, two, sel, run(50000) + [2] + run(49999) + [3]), "data"))
lim.append(case("22 RUNA at level 9: N reaches 2^21 (run too long)", 9,
                stream(9, USED, two, sel, [0] * 22), "data"))
lim.append(case("21 RUNA at level 9: 2^21-1 bytes, over the block size", 9,
                stream(9, USED, two, sel, [0] * 21), "data"))
lim.append(case("20 RUNA at level 9: 2^20-1 bytes, over the block size", 9,
                stream(9, USED, two, sel, [0] * 20), "data"))
lim.append(case("19 RUNA at level 9: 2^19-1 bytes, within the block size", 9,
                stream(9, USED, two, sel, [0] * 19 + [2]), "ok"))
lim.append(case("22 RUNA and then the input ends: the run check comes first", 9,
                trunc(9, [0] * 22, 0), "data"))
lim.append(case("21 RUNA and then the input ends: eof", 9, trunc(9, [0] * 21, 0), "eof"))
lim.append(case("run of 100001 at level 1, input ends after it: the next symbol is read "
                "first (eof)", 1, trunc(1, run(100001), 0), "eof"))
# out of selectors
alt = [2, 3] * 60
lim.append(case("one selector, 49 symbols and EOB: 50 symbols, all coded", 1,
                stream(1, USED, two, [0], alt[:49]), "ok"))
lim.append(case("one selector, 50 symbols and EOB: the 51st has no selector (data)", 1,
                stream(1, USED, two, [0], alt[:50]), "data"))
lim.append(case("two selectors, 99 symbols and EOB", 1,
                stream(1, USED, two, [0, 1], alt[:99]), "ok"))
lim.append(case("two selectors, 100 symbols and EOB: no selector for the 101st (data)", 1,
                stream(1, USED, two, [0, 1], alt[:100]), "data"))
# EOB missing
lim.append(case("no EOB: the input ends after whole symbols (eof)", 1,
                trunc(1, [2, 3, 2, 3, 3, 2], 0), "eof"))
lim.append(case("no EOB: the input ends inside a code, one bit left (eof)", 1,
                trunc(1, [2, 3, 2, 3, 3, 2], 7), "eof"))
lim.append(case("no EOB, full groups: 50 symbols then the input ends (eof)", 1,
                trunc(1, [2, 3] * 25, 0), "eof"))
write("limits.txt", lim)
