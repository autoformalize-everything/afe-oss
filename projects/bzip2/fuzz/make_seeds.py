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
for i in (1, 2, 3):
    with open(os.path.join(upstream, f"sample{i}.bz2"), "rb") as f:
        seeds[f"sample{i}.bz2"] = f.read()

shutil.rmtree(seed, ignore_errors=True)
os.makedirs(seed)
for name, data in sorted(seeds.items()):
    with open(os.path.join(seed, name), "wb") as f:
        f.write(data)
