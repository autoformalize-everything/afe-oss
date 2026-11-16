"""Writes the vectors in this directory: cases are made here, and every result is what the
vendored C code printed (huff.c). Usage: generate.py HUFF BZIP2 OUTDIR. Deterministic."""
import random
import subprocess
import sys
import tempfile
import os

huff, bzip2, outdir = sys.argv[1:4]


def hexbits(bits):
    """Bytes of a string of '0'/'1' (padded with zeros), as a `bits` line."""
    bits += "0" * (-len(bits) % 8)
    return "bits " + " ".join("%02x" % int(bits[i:i + 8], 2) for i in range(0, len(bits), 8))


def codes(lens):
    """Canonical codes (BZ2_hbAssignCodes, huffman.c:152-166), as bit strings."""
    out = [None] * len(lens)
    vec = 0
    for n in range(min(lens), max(lens) + 1):
        for i, l in enumerate(lens):
            if l == n:
                out[i] = format(vec, "0%db" % n)
                vec += 1
        vec <<= 1
    return out


def block(comment, lens=None, bits="", n=1, raw=None):
    lines = ["# " + comment]
    if lens is not None:
        lines.append("len " + " ".join(map(str, lens)))
    if raw is not None:
        lines += raw
    lines.append(hexbits(bits) if bits else "bits")
    lines.append("n %d" % n)
    return "\n".join(lines) + "\n\n"


def run_cases(text):
    r = subprocess.run([huff, "cases"], input=text, capture_output=True, text=True, check=True)
    return r.stdout


def write(name, blocks):
    with open(os.path.join(outdir, name), "w") as f:
        f.write(run_cases("".join(blocks)))


# --- Tables of real streams -------------------------------------------------------------
rng = random.Random(2024)
words = ["alpha", "beta", "gamma", "delta", "huffman", "table", "code", "limit", "base",
         "perm", "symbol", "stream", "block", "the", "of", "and", "a", "to", "in", "is"]
inputs = {
    "tiny": b"hello hello hello, bzip2! " * 3,
    "text": " ".join(rng.choice(words) for _ in range(6000)).encode(),
    "bytes": bytes(rng.randrange(256) for _ in range(20000)),
}
real = []
with tempfile.TemporaryDirectory() as tmp:
    for name, data in inputs.items():
        raw = os.path.join(tmp, name)
        with open(raw, "wb") as f:
            f.write(data)
        z = subprocess.run([bzip2, "-9", "-c", raw], capture_output=True, check=True).stdout
        with open(raw + ".bz2", "wb") as f:
            f.write(z)
        groups = subprocess.run([huff, "lens", raw + ".bz2"], capture_output=True, text=True,
                                check=True).stdout.strip().split("\n\n")
        for t, g in enumerate(groups):
            rec = {l.split()[0]: l.split()[1:] for l in g.split("\n")}
            lens = list(map(int, rec["len"]))
            cs = codes(lens)
            syms = [rng.randrange(len(lens)) for _ in range(40)]
            bits = "".join(cs[s] for s in syms)
            comment = "%s.bz2 (bzip2 -9), table %d of %d, alphaSize %d: 40 symbols" % (
                name, t, len(groups), len(lens))
            case = block(comment, lens, bits, 40)
            out = run_cases(case)
            got = {l.split()[0]: l.split()[1:] for l in out.split("\n") if l and l[0] != "#"}
            # the library's own tables for this block, built while decompressing the stream
            assert got["minLen"] == rec["rminLen"], (name, t)
            assert got["limit"] == rec["rlimit"], (name, t)
            assert got["base"] == rec["rbase"], (name, t)
            assert got["perm"] == rec["rperm"], (name, t)
            assert "".join(got["syms"]) == "".join(map(str, syms)) and got["end"] == ["ok"]
            real.append(out)
            if t == 0:
                rb = "".join(rng.choice("01") for _ in range(400))
                real.append(run_cases(block(
                    "%s.bz2, table 0: random bits until the input ends" % name, lens, rb, 400)))
with open(os.path.join(outdir, "real.txt"), "w") as f:
    f.write("".join(real))

# --- Incomplete length sets: some codes of every length are unused ----------------------
def enc(lens, syms, tail=""):
    cs = codes(lens)
    return "".join(cs[s] for s in syms) + tail

write("incomplete.txt", [
    block("lengths 1 2 3: codes 0, 10, 110; 111... is unassigned and runs past 20 bits",
          [1, 2, 3], enc([1, 2, 3], [0, 1, 2, 2, 0], "1" * 30), 8),
    block("lengths 2 2 2: 11 is unassigned", [2, 2, 2], enc([2, 2, 2], [1, 0, 2], "11" * 12), 5),
    block("lengths 2 2 2: the unassigned code first", [2, 2, 2], "11" * 12, 1),
    block("lengths 1 3 3: 11 is unassigned, and the gap at length 2", [1, 3, 3],
          enc([1, 3, 3], [0, 1, 2, 0], "11" * 12), 6),
    block("lengths 5 5 5: minLen 5, limit 2 at length 5", [5, 5, 5],
          enc([5, 5, 5], [2, 1, 0], "1" * 40), 5),
    block("lengths 1 2 ... 20: the longest code is 20 bits, 1^20 is unassigned",
          list(range(1, 21)), "1" * 19 + "0" + "1" * 21 + "0", 3),
    block("lengths 1 2 ... 20: 21 ones end in zn = 21 (data)", list(range(1, 21)), "1" * 21, 1),
    block("lengths 1 2 ... 20: 16 ones, then the input ends inside the code (eof)",
          list(range(1, 21)), "1" * 16, 1),
    block("lengths 17 3 3 3: an incomplete set mixing short and long codes", [17, 3, 3, 3],
          enc([17, 3, 3, 3], [0, 3, 1], "1" * 24), 6),
])

# --- Over-subscribed length sets: Kraft sum above 1 -------------------------------------
write("oversubscribed.txt", [
    block("lengths 1 1 1: three symbols, two codes; symbol 2 is never returned", [1, 1, 1],
          "0110100", 7),
    block("lengths 2 2 2 2 2: five codes of two bits, only 00..11 occur", [2] * 5,
          "00011011" * 2, 8),
    block("lengths 1 2 2 2: 0, 10, 11 are returned, perm[3] never", [1, 2, 2, 2],
          "0" + "10" + "11" + "0" + "11" + "10", 6),
    block("lengths 3 x 9: nine codes of three bits, symbol 8 never", [3] * 9,
          "".join(format(i, "03b") for i in range(8)), 8),
    block("lengths 2 2 2 2 2 3: the three-bit code is never reached", [2, 2, 2, 2, 2, 3],
          "00011011", 4),
    block("lengths 8 x 258: 258 codes of 8 bits; symbols 0..255 occur", [8] * 258,
          "".join(format(i, "08b") for i in (0, 1, 255, 128, 7)), 5),
    block("lengths 1 1 2 2 3 3 4 4 (Kraft 1.5): short codes only", [1, 1, 2, 2, 3, 3, 4, 4],
          "0110" * 4, 8),
])

# --- Failures, and tables no lengths give -----------------------------------------------
def arr(vals):
    a = [0] * 23
    for i, v in vals.items():
        a[i] = v
    return " ".join(map(str, a))

def raw(minlen, lim, base, perm):
    return ["minLen %d" % minlen, "limit " + arr(lim), "base " + arr(base),
            "perm " + " ".join(map(str, perm))]

p258 = list(range(258))
write("failures.txt", [
    block("input empty: not even minLen bits (eof)", [3, 3, 3, 3, 3, 3, 3], "", 1),
    block("four symbols (00 01 10 11), then the input ends (eof)", [2, 2, 2, 2],
          "00011011", 5),
    block("input ends inside a code of an incomplete table (eof)", [1, 2, 3], "1" * 8, 1),
    block("zn = 21: code unassigned in a table of 3 bits (data)", [3, 3, 3, 3, 3, 3, 3], "1" * 40, 2),
    block("two codes, then an unassigned one (data), n larger than what is read",
          [2, 2, 2], "00" + "01" + "11" * 12, 5),
    block("minLen 1, limit[1] 5, base[1] 3: zvec 0 gives index -3 (data)",
          raw=raw(1, {1: 5}, {1: 3}, [0, 1, 2]), bits="0", n=1),
    block("base[1] 2, zvec 1: index -1 (data)",
          raw=raw(1, {1: 5}, {1: 2}, [0, 1, 2]), bits="1", n=1),
    block("base[1] 1, zvec 1: index 0 is the first perm entry",
          raw=raw(1, {1: 5}, {1: 1}, [9, 8, 7]), bits="1", n=1),
    block("base[1] -256, zvec 1: index 257, the last entry of perm",
          raw=raw(1, {1: 5}, {1: -256}, p258[:257] + [77]), bits="1", n=1),
    block("base[1] -257, zvec 1: index 258 (data)",
          raw=raw(1, {1: 5}, {1: -257}, p258), bits="1", n=1),
    block("base[1] -1000, zvec 0: index 1000 (data)",
          raw=raw(1, {1: 5}, {1: -1000}, p258), bits="0", n=1),
    block("limit all -1: the loop runs to zn = 21 and fails (data)",
          raw=raw(2, {i: -1 for i in range(23)}, {}, [4, 5]), bits="0" * 24, n=1),
    block("limit[20] 1048575, 20 bits: zn = 20 is still allowed",
          raw=raw(2, {i: -1 for i in range(2, 20)} | {20: 1048575}, {20: 0}, [5, 6, 7, 8]),
          bits="0" * 18 + "1" + "1" * 1 + "0" * 4, n=1),
    block("limit[21] large but zn = 21 is refused before limit[21] is read (data)",
          raw=raw(2, {i: -1 for i in range(2, 21)} | {21: 99999999}, {}, [5, 6]),
          bits="0" * 24, n=1),
    block("minLen 20: 20 bits at once, then limit[20] decides",
          raw=raw(20, {20: 5}, {20: 0}, [3, 2, 1]), bits="0" * 19 + "1" + "0" * 4, n=2),
])
