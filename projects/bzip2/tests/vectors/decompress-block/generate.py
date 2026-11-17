"""Writes the vectors in this directory. Streams of one block are made here (real ones by the
vendored bzip2, hand-made ones by the encoder below), and every result is what the vendored C
code gave for the stream (`classify`, ../classify.c): `ok` with the output, or the error class.
Usage: generate.py CLASSIFY BZIP2 OUTDIR. Deterministic."""
import os
import random
import subprocess
import sys
import tempfile

classify, bzip2, outdir = sys.argv[1:4]
rng = random.Random(11)
tmp = tempfile.mkdtemp()


# --- What the C code computes, for the hand-made blocks ---------------------------------

def crc_table():
    """BZ2_crc32Table (crctable.c:31-99): MSB-first CRC-32, polynomial 0x04c11db7."""
    out = []
    for i in range(256):
        c = i << 24
        for _ in range(8):
            c = ((c << 1) ^ 0x04C11DB7) if c & 0x80000000 else (c << 1)
        out.append(c & 0xFFFFFFFF)
    return out


TABLE = crc_table()


def crc(data):
    """The block CRC (BZ_INITIALISE_CRC, BZ_UPDATE_CRC, BZ_FINALISE_CRC)."""
    c = 0xFFFFFFFF
    for b in data:
        c = ((c << 8) & 0xFFFFFFFF) ^ TABLE[(c >> 24) ^ b]
    return c ^ 0xFFFFFFFF


def rnums(path):
    """BZ2_rNums, read from randtable.c."""
    text = open(path).read()
    body = text[text.index("{") + 1:text.index("}")]
    nums = [int(w) for w in body.replace(",", " ").split()]
    assert len(nums) == 512
    return nums


RNUMS = rnums(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "..", "..", "..", "upstream", "randtable.c"))


def rand_mask(n):
    """The randomisation mask of the first n positions (BZ_RAND_UPD_MASK, BZ_RAND_MASK)."""
    out, to_go, t_pos = [], 0, 0
    for _ in range(n):
        if to_go == 0:
            to_go = RNUMS[t_pos]
            t_pos = (t_pos + 1) % 512
        to_go -= 1
        out.append(1 if to_go == 1 else 0)
    return out


def bwt(block):
    """Last column and origPtr of the sorted rotations (blocksort.c:1083-1086)."""
    n = len(block)
    ptr = sorted(range(n), key=lambda i: block[i:] + block[:i])
    return [block[(p - 1) % n] for p in ptr], ptr.index(0)


def unrle(last, orig_ptr, randomised):
    """The bytes the C decoder writes for a block, and whether it reports corruption: the
    links (decompress.c:566-572) walked as unRLE_obuf_to_output_FAST does (bzlib.c:536-688)."""
    n = len(last)
    cftab = [0] * 257
    for b in last:
        cftab[b + 1] += 1
    for i in range(1, 257):
        cftab[i] += cftab[i - 1]
    tt = list(last)
    for i, b in enumerate(last):
        tt[cftab[b]] |= i << 8
        cftab[b] += 1
    state = {"pos": tt[orig_ptr] >> 8, "to_go": 0, "t_pos": 0, "used": 0}

    def get():
        state["pos"] = tt[state["pos"]]
        k = state["pos"] & 0xFF
        state["pos"] >>= 8
        if randomised:
            if state["to_go"] == 0:
                state["to_go"] = RNUMS[state["t_pos"]]
                state["t_pos"] = (state["t_pos"] + 1) % 512
            state["to_go"] -= 1
            k ^= 1 if state["to_go"] == 1 else 0
        state["used"] += 1
        return k

    out = []
    k0 = get()
    ch, length = 0, 0
    while True:
        out += [ch] * length
        if state["used"] == n + 1:
            return bytes(out), False
        if state["used"] > n + 1:
            return bytes(out), True
        ch, length = k0, 1
        stop = False
        for length in (1, 2, 3):
            k1 = get()
            if state["used"] == n + 1 or k1 != k0:
                k0 = k1
                stop = True
                break
        if stop:
            continue
        length = get() + 4
        k0 = get()


# --- Encoding a block -------------------------------------------------------------------

def bits(value, n):
    return format(value, "0%db" % n)


def tobytes(bs):
    bs += "0" * (-len(bs) % 8)
    return bytes(int(bs[i:i + 8], 2) for i in range(0, len(bs), 8))


def mtf_rle2(last, used):
    """The block's symbols: move-to-front over the used bytes, zero runs as RUNA/RUNB
    (the inverse of decompress.c:386-487), EOB last."""
    mtf = list(range(len(used)))
    syms, zeros = [], 0

    def flush(z):
        while z > 0:
            z -= 1
            syms.append(z % 2)
            z //= 2

    for b in last:
        j = mtf.index(used.index(b))
        if j == 0:
            zeros += 1
            continue
        flush(zeros)
        zeros = 0
        mtf.insert(0, mtf.pop(j))
        syms.append(j + 1)
    flush(zeros)
    syms.append(len(used) + 1)
    return syms


def lengths(m):
    """Code lengths of a complete prefix code over m symbols: as even as possible."""
    k = (m - 1).bit_length()
    short = 2 ** k - m
    return [k - 1] * short + [k] * (m - short)


def codes(lens):
    """Canonical codes (huffman.c:152-166), as bit strings."""
    out = [None] * len(lens)
    vec = 0
    for n in range(min(lens), max(lens) + 1):
        for i, l in enumerate(lens):
            if l == n:
                out[i] = bits(vec, n)
                vec += 1
        vec <<= 1
    return out


def block_stream(level, block, randomised=False, orig_ptr=None, block_crc=None):
    """A stream of one block holding `block` (the bytes before the BWT, after RLE1). Unless
    given, origPtr is the right one and the block CRC is that of what the C decoder writes;
    the stream CRC is the block CRC."""
    mask = rand_mask(len(block)) if randomised else [0] * len(block)
    stored = bytes(b ^ m for b, m in zip(block, mask))
    last, ptr = bwt(stored)
    if orig_ptr is None:
        orig_ptr = ptr
    if block_crc is None:
        out, corrupt = unrle(last, orig_ptr, randomised)
        assert not corrupt
        block_crc = crc(out)
    used = sorted(set(last))
    syms = mtf_rle2(last, used)
    code = codes(lengths(len(used) + 2))
    selectors = (len(syms) + 49) // 50
    bs = "".join(bits(b, 8) for b in b"BZh%d" % level) + bits(0x314159265359, 48)
    bs += bits(block_crc, 32) + ("1" if randomised else "0") + bits(orig_ptr, 24)
    top = [any(16 * i <= u < 16 * i + 16 for u in used) for i in range(16)]
    bs += "".join("1" if t else "0" for t in top)
    for i in range(16):
        if top[i]:
            bs += "".join("1" if 16 * i + j in used else "0" for j in range(16))
    bs += bits(2, 3) + bits(selectors, 15) + "0" * selectors
    for _ in range(2):  # two groups, the same lengths (decompress.c:321-337)
        lens = lengths(len(used) + 2)
        curr = lens[0]
        bs += bits(curr, 5)
        for target in lens:
            while curr != target:
                bs += "10" if target > curr else "11"
                curr += 1 if target > curr else -1
            bs += "0"
    bs += "".join(code[s] for s in syms)
    bs += bits(0x177245385090, 48) + bits(block_crc, 32)
    return tobytes(bs)


def rle1(data):
    """RLE1 as the compressor applies it: runs of 4 to 255 as four bytes and a count."""
    out, i = [], 0
    while i < len(data):
        j = i
        while j < len(data) and data[j] == data[i] and j - i < 255:
            j += 1
        r = j - i
        out += [data[i]] * min(r, 4) + ([r - 4] if r >= 4 else [])
        i = j
    return bytes(out)


# --- Cases -------------------------------------------------------------------------------

def case(comment, level, data, expect):
    """One vector: the stream and what `classify` gave for it, asserted to be `expect`."""
    src, dst = os.path.join(tmp, "in.bz2"), os.path.join(tmp, "out")
    with open(src, "wb") as f:
        f.write(data)
    res = subprocess.run([classify, src, dst], capture_output=True, text=True,
                         check=True).stdout.strip()
    assert res == expect, (comment, res)
    lines = ["# " + comment, "level %d" % level, "hex " + data.hex(), "result " + res]
    if res == "ok":
        out = open(dst, "rb").read()
        h = 0
        for b in out:
            h = (h * 31 + b) & 0xFFFFFFFF
        lines += ["size %d" % len(out), "hash %d" % h]
        if len(out) <= 4096:
            lines.append("out " + out.hex())
    return "\n".join(lines) + "\n"


def write(name, cases):
    with open(os.path.join(outdir, name), "w") as f:
        f.write("\n".join(cases))


words = ["alpha", "beta", "gamma", "delta", "inverse", "cftab", "origPtr", "the", "of",
         "and", "a", "to", "in", "is", "aaaa", "zzzzzzzz"]

# Real blocks: one-block streams made by the vendored bzip2.
inputs = [
    ("hello, repeated", 1, b"hello hello hello, bzip2! " * 3),
    ("one byte", 9, b"x"),
    ("periodic: abc six times (the links form three cycles)", 1, b"abc" * 6),
    ("a run of 4 (count byte 0)", 9, b"q" * 4),
    ("a run of 5", 9, b"q" * 5),
    ("a run of 255 (count byte 251)", 9, b"q" * 255),
    ("a run of 256 (a run of 255, then one byte)", 9, b"q" * 256),
    ("a run of 1000", 1, b"r" * 1000),
    ("all 256 byte values, twice", 1, bytes(range(256)) * 2),
    ("random bytes, 1500", 1, bytes(rng.randrange(256) for _ in range(1500))),
    ("text with runs, about 3 kB", 9,
     " ".join(rng.choice(words) for _ in range(500)).encode()),
    ("runs of every length up to 40 (hash only: more than 4096 bytes)", 9,
     b"".join(bytes([65 + i % 5]) * i for i in range(1, 41)) * 6),
]
real = []
for comment, level, data in inputs:
    z = subprocess.run([bzip2, "-%d" % level, "-c"], input=data, capture_output=True,
                       check=True).stdout
    real.append(case("%s, bzip2 -%d" % (comment, level), level, z, "ok"))
write("real.txt", real)

# Hand-made blocks.
text = " ".join(rng.choice(words) for _ in range(500)).encode()
long_text = " ".join(rng.choice(words) for _ in range(1200)).encode()
hand = []
hand.append(case("randomised block, 3 kB of text with runs (bzip2 0.9.0's flag)", 9,
                 block_stream(9, rle1(text), randomised=True), "ok"))
hand.append(case("randomised block, 8 kB: the mask past several rNums entries", 1,
                 block_stream(1, rle1(long_text), randomised=True), "ok"))
hand.append(case("randomised block, 618 bytes: only the last byte is flipped", 1,
                 block_stream(1, bytes(rng.randrange(97, 123) for _ in range(618)),
                              randomised=True), "ok"))
hand.append(case("the same text not randomised (hand-made encoder)", 9,
                 block_stream(9, rle1(text)), "ok"))
hand.append(case("count byte 252: a run of 256", 1, block_stream(1, b"xqqqq\xfcy"), "ok"))
hand.append(case("count byte 255: a run of 259", 1, block_stream(1, b"xqqqq\xffy"), "ok"))
hand.append(case("count byte 255 ends the block", 1, block_stream(1, b"xyqqqq\xff"), "ok"))
hand.append(case("count byte 0 ends the block", 1, block_stream(1, b"xyqqqq\x00"), "ok"))
hand.append(case("three equal bytes end the block (no count byte)", 1,
                 block_stream(1, b"xyqqq"), "ok"))
hand.append(case("count byte 251 in a randomised block of 700 bytes", 1,
                 block_stream(1, bytes(rng.randrange(97, 123) for _ in range(650))
                              + b"zzzz\xfb" + bytes(rng.randrange(97, 123) for _ in range(45)),
                              randomised=True), "ok"))
# Four equal bytes end the block: the count byte is read past the end (data error). The CRC
# is that of the bytes as if the run were four long, so only the cut-off can fail it.
hand.append(case("four equal bytes end the block: a run cut off (data)", 1,
                 block_stream(1, b"xyqqqq", block_crc=crc(b"xyqqqq")), "data"))
hand.append(case("only four equal bytes (data)", 1,
                 block_stream(1, b"qqqq", block_crc=crc(b"qqqq")), "data"))
hand.append(case("randomised, four equal bytes end the block (data)", 1,
                 block_stream(1, b"xyqqqq", randomised=True, block_crc=crc(b"xyqqqq")),
                 "data"))
good = rle1(b"hello hello hello, bzip2!")
_, ptr = bwt(good)
right_crc = crc(b"hello hello hello, bzip2!")
hand.append(case("block CRC with one bit flipped (data)", 1,
                 block_stream(1, good, block_crc=right_crc ^ 1), "data"))
hand.append(case("origPtr == nblock (data)", 1,
                 block_stream(1, good, orig_ptr=len(good), block_crc=right_crc), "data"))
hand.append(case("origPtr == nblock + 1000 (data)", 1,
                 block_stream(1, good, orig_ptr=len(good) + 1000, block_crc=right_crc), "data"))
# A wrong origPtr below nblock: the walk starts elsewhere and C writes a rotation of the
# block. With the CRC of what it writes, the block is accepted.
wrong = (ptr + 5) % len(good)
last, _ = bwt(good)
rotated, corrupt = unrle(last, wrong, False)
assert not corrupt and rotated != b"hello hello hello, bzip2!"
hand.append(case("origPtr off by 5, CRC of the rotation C writes", 1,
                 block_stream(1, good, orig_ptr=wrong), "ok"))
hand.append(case("origPtr off by 5, CRC of the right bytes (data)", 1,
                 block_stream(1, good, orig_ptr=wrong, block_crc=right_crc), "data"))
write("blocks.txt", hand)
