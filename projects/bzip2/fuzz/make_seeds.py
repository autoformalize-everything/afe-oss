#!/usr/bin/env python3
"""Rewrites fuzz/corpus/seed/ (stdlib only): the upstream samples and a few hand-made streams.

Usage: python3 fuzz/make_seeds.py "$(sh tests/vectors/build-bzip2.sh)"

The streams come from the vendored bzip2 that tests/vectors/build-bzip2.sh builds out of tree,
so the output is deterministic; afterwards `git status` must show no change."""
import os, shutil, subprocess, sys

here = os.path.dirname(os.path.abspath(__file__))
build, = sys.argv[1:]
upstream = os.path.join(here, "..", "upstream")
seed = os.path.join(here, "corpus", "seed")


def compress(data, level):
    return subprocess.run([os.path.join(build, "bzip2"), f"-{level}", "-c"], input=data,
                          check=True, stdout=subprocess.PIPE).stdout


def crc32(data):
    # The block CRC: CRC-32, polynomial 0x04c11db7, most significant bit first
    # (crctable.c:31-35, bzlib_private.h:157-172).
    crc = 0xFFFFFFFF
    for b in data:
        crc ^= b << 24
        for _ in range(8):
            crc = ((crc << 1) ^ 0x04C11DB7 if crc & 0x80000000 else crc << 1) & 0xFFFFFFFF
    return crc ^ 0xFFFFFFFF


def randomised(data):
    """A one-block level-1 stream of `data` (at most 1337 bytes, no four equal bytes in a
    row) with the randomised flag set and both CRCs fixed, so that it decodes."""
    stream = bytearray(compress(data, 1))
    # The flag is the bit after the 4-byte header, 6-byte block magic and 4-byte block CRC
    # (compress.c:624-648).
    stream[14] |= 0x80
    # The mask flips the low bit of the byte at index 617 (BZ2_rNums[0] - 2, randtable.c:27,
    # bzlib_private.h:137-149), and the next one 720 bytes later, past the end of `data`.
    out = bytearray(data)
    out[617] ^= 1
    crc = crc32(out).to_bytes(4, "big")
    stream[10:14] = crc
    # One block, so the combined CRC equals the block CRC (bzlib.c:832-835). It is the last
    # 32 bits of the stream, before 0-7 bits of zero padding (decompress.c:601-609).
    bits = int.from_bytes(stream, "big")
    nbits = len(stream) * 8
    for pad in range(8):
        old = (bits >> pad) & 0xFFFFFFFF
        magic = (bits >> (pad + 32)) & 0xFFFFFFFFFFFF
        if magic == 0x177245385090:
            bits ^= (old ^ int.from_bytes(crc, "big")) << pad
            return bits.to_bytes(nbits // 8, "big")
    raise AssertionError("end-of-stream magic not found")


def no_runs(n):
    return bytes((i * 37 + i // 256) % 256 for i in range(n))


# Hand-made blocks, for what no compressor writes. A block is given by its BWT output `tt`
# (the bytes before the inverse BWT) and `origPtr`, which the decoder takes as they come.

class Bits:
    """A bit string, most significant bit first, as bsW writes it (compress.c:73-78)."""

    def __init__(self):
        self.bits = []

    def put(self, value, n):
        self.bits += [(value >> (n - 1 - i)) & 1 for i in range(n)]

    def bytes(self):
        bits = self.bits + [0] * (-len(self.bits) % 8)
        return bytes(int("".join(map(str, bits[i:i + 8])), 2) for i in range(0, len(bits), 8))


def walk(tt, orig_ptr, steps):
    """`steps` bytes of the inverse BWT walk (decompress.c:566-572, BZ_GET_FAST at
    bzlib_private.h:444-449); past `len(tt)` it goes on as the C walk does."""
    cftab = [0] * 257
    for b in tt:
        cftab[b + 1] += 1
    for i in range(256):
        cftab[i + 1] += cftab[i]
    links = [0] * len(tt)
    for i, b in enumerate(tt):
        links[cftab[b]] = i
        cftab[b] += 1
    pos, out = links[orig_ptr], []
    for _ in range(steps):
        out.append(tt[pos])
        pos = links[pos]
    return out


def unrle(tt, orig_ptr):
    """The block's bytes, by the loop of unRLE_obuf_to_output_FAST (bzlib.c:608-661), or None
    where it reports corrupt data (bzlib.c:633-634)."""
    w = walk(tt, orig_ptr, len(tt) + 3)
    stop = len(tt) + 1
    used, out, run, ch, k0 = 1, bytearray(), 0, 0, w[0]

    def get():
        nonlocal used
        used += 1
        return w[used - 1]
    while True:
        out += bytes([ch]) * run
        if used > stop:
            return None
        if used == stop:
            return bytes(out)
        ch, k1 = k0, get()
        if k1 != k0 or used == stop:
            k0, run = k1, 1
            continue
        run, k1 = 2, get()
        if used == stop:
            continue
        if k1 != k0:
            k0 = k1
            continue
        run, k1 = 3, get()
        if used == stop:
            continue
        if k1 != k0:
            k0 = k1
            continue
        run = get() + 4
        k0 = get()


def bwt(data):
    """The BWT output of `data` and its origPtr, by sorting rotations (small inputs only)."""
    rows = sorted(range(len(data)), key=lambda i: data[i:] + data[:i])
    return bytes(data[i - 1] for i in rows), rows.index(0)


def put_block(bits, tt, orig_ptr, n_selectors=None):
    """Writes one block (decompress.c:222-489): two coding tables (the fewest,
    decompress.c:288), both giving every symbol a word of the same length. Returns the
    block's bytes, or None where the decoder finds them corrupt."""
    out = unrle(tt, orig_ptr)
    bits.put(0x314159265359, 48)
    bits.put(crc32(out) if out is not None else 0, 32)
    bits.put(0, 1)
    bits.put(orig_ptr, 24)
    used = sorted(set(tt))
    groups = [g for g in range(16) if any(b // 16 == g for b in used)]
    for g in range(16):
        bits.put(g in groups, 1)
    for g in groups:
        for j in range(16):
            bits.put(g * 16 + j in used, 1)
    # MTF, with runs of zeros as RUNA (0) and RUNB (1) digits (decompress.c:385-423).
    mtf, syms, zeros = list(range(len(used))), [], 0

    def flush():
        nonlocal zeros
        while zeros > 0:  # bijective base 2, RUNA the digit 1 and RUNB the digit 2
            syms.append(1 - zeros % 2)
            zeros = (zeros - 2 + zeros % 2) // 2
    for b in tt:
        i = mtf.index(used.index(b))
        if i == 0:
            zeros += 1
            continue
        flush()
        syms.append(i + 1)
        mtf.insert(0, mtf.pop(i))
    flush()
    syms.append(len(used) + 1)  # EOB (decompress.c:357)
    alpha_size = len(used) + 2
    length = (alpha_size - 1).bit_length()
    if n_selectors is None:
        n_selectors = (len(syms) + 49) // 50
    bits.put(2, 3)
    bits.put(n_selectors, 15)
    bits.put(0, n_selectors)
    for _ in range(2):
        bits.put(length, 5)
        bits.put(0, alpha_size)
    for s in syms:
        bits.put(s, length)
    return out


def made(level, *blocks):
    """A stream of hand-made blocks, each (tt, origPtr) or (tt, origPtr, nSelectors), with the
    combined CRC of bzlib.c:832-835."""
    bits = Bits()
    bits.put(int.from_bytes(b"BZh" + bytes([0x30 + level]), "big"), 32)
    combined = 0
    for block in blocks:
        out = put_block(bits, *block)
        crc = crc32(out) if out is not None else 0
        combined = (((combined << 1) | (combined >> 31)) & 0xFFFFFFFF) ^ crc
    bits.put(0x177245385090, 48)
    bits.put(combined, 32)
    return bits.bytes()


seeds = {
    "empty.bz2": compress(b"", 9),
    "hello-1.bz2": compress(b"hello\n", 1),
    "all256.bz2": compress(bytes(range(256)) * 2, 9),
    "runs.bz2": compress(b"a" * 1000 + b"b" * 4 + b"c" * 5 + b"d" * 255 + b"xyz" * 50, 1),
    "concatenated.bz2": compress(b"hello\n", 9) + compress(b"world\n", 1),
    "trailing-garbage.bz2": compress(b"hello\n", 9) + b"this is not bzip2\n",
    "randomised.bz2": randomised(no_runs(1000)),
}
seeds["truncated.bz2"] = seeds["runs.bz2"][:-10]
hello = bwt(b"hello, world\n")
assert unrle(*hello) == b"hello, world\n"
seeds.update({
    # A count byte of 255: a run of 259 (bzlib.c:658-660).
    "made-run-259.bz2": made(1, bwt(b"xaaaa\xffy")),
    # Four equal bytes end the block, so the count is read past its end (bzlib.c:633-634).
    "made-run-at-end.bz2": made(1, bwt(b"xyaaaa")),
    "made-count-at-end.bz2": made(1, bwt(b"xyaaaa\x05")),
    # More than BZ_MAX_SELECTORS (18002) selectors: the rest are ignored (decompress.c:299-306).
    "made-selectors-18010.bz2": made(1, (*hello, 18010)),
    # An origPtr that starts the walk elsewhere: other bytes, no error (decompress.c:572).
    "made-orig-ptr.bz2": made(1, (hello[0], (hello[1] + 1) % 13)),
    # nblock up to 100000 * level is accepted (decompress.c:358, decompress.c:417).
    "made-nblock-100000.bz2": made(1, (b"a" * 50000 + b"b" * 50000, 0)),
    "made-nblock-100001.bz2": made(1, (b"a" * 50000 + b"b" * 50001, 0)),
    "made-two-blocks.bz2": made(9, bwt(b"hello, "), bwt(b"world\n")),
})
for i in (1, 2, 3):
    with open(os.path.join(upstream, f"sample{i}.bz2"), "rb") as f:
        seeds[f"sample{i}.bz2"] = f.read()

shutil.rmtree(seed, ignore_errors=True)
os.makedirs(seed)
for name, data in sorted(seeds.items()):
    with open(os.path.join(seed, name), "wb") as f:
        f.write(data)
