#!/usr/bin/env python3
"""Regenerates tests/vectors/{decompress,compress}/* from the vendored bzip2 (stdlib only).

Run via regenerate.sh. Inputs are deterministic; expected results come from the vendored
build (bzip2 for the compressed inputs, classify for the expected output / error class)."""
import os, shutil, subprocess, sys

here = os.path.dirname(os.path.abspath(__file__))
build, = sys.argv[1:]
upstream = os.path.join(here, "..", "..", "upstream")
bzip2 = os.path.join(build, "bzip2")
classify = os.path.join(build, "classify")

def compress(data, level):
    return subprocess.run([bzip2, f"-{level}", "-c"], input=data, check=True,
                          stdout=subprocess.PIPE).stdout

def read(p):
    with open(p, "rb") as f:
        return f.read()

def block_bytes(n):
    # no two equal neighbours, so the initial run-length encoding (`bzlib.c:260-283`; runs of
    # 1-3 are copied as they are, `bzlib.c:223-247`) leaves the length alone
    return bytes((i * 37 + i // 256) % 256 for i in range(n))

# Raw inputs (the compression cases use these; the decompression cases use their bzip2 -9 form).
raw = {
    "empty": b"",
    "all256": bytes(range(256)),
    "run3": b"a" * 3,
    "run4": b"a" * 4,
    "run5": b"a" * 5,
    "run255": b"a" * 255,
    "run256": b"a" * 256,
    "run100000": b"a" * 100000,
    "text": b"The quick brown fox jumps over the lazy dog.\n" * 20,
}
for i in (1, 2, 3):
    raw[f"sample{i}"] = read(os.path.join(upstream, f"sample{i}.ref"))

# nblockMAX = 100000 * level - 19 (`bzlib.c:194`): a level-1 block holds 99981 bytes.
level1_limit = 99981

# (name, compressed input, level) for decompression: valid streams
valid = {name: compress(data, 9) for name, data in raw.items() if not name.startswith("sample")}
for i in (1, 2, 3):
    valid[f"sample{i}"] = read(os.path.join(upstream, f"sample{i}.bz2"))
valid["block-at-limit"] = compress(block_bytes(level1_limit), 1)
valid["block-over-limit"] = compress(block_bytes(level1_limit + 1), 1)
valid["concatenated"] = compress(b"hello\n", 9) + compress(b"world\n", 1)
valid["trailing-garbage"] = compress(b"hello\n", 9) + b"this is not bzip2\n"

stream = compress(raw["text"], 9)
bad = {
    "trunc-header": stream[:3],
    "trunc-block": stream[:len(stream) // 2],
    "trunc-footer": stream[:-2],
    "flip-block-crc": stream[:10] + bytes([stream[10] ^ 0x01]) + stream[11:],  # CRC at byte 10: 4-byte header + 6-byte block magic (`compress.c:624-637`)
    "bad-magic": b"XYZ9" + stream[4:],
    "level0": b"BZh0" + stream[4:],
    "zero-length": b"",
}

for d in ("decompress", "compress"):
    shutil.rmtree(os.path.join(here, d), ignore_errors=True)

def write(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "wb") as f:
        f.write(data)

def decomp_case(name, data):
    d = os.path.join(here, "decompress", name)
    write(os.path.join(d, "input"), data)
    out = os.path.join(build, "out.tmp")
    cls = subprocess.run([classify, os.path.join(d, "input"), out], check=True,
                         stdout=subprocess.PIPE, text=True).stdout.strip()
    if cls == "ok":
        write(os.path.join(d, "expected"), read(out))
    else:
        assert cls in ("magic", "data", "eof"), (name, cls)
        write(os.path.join(d, "error"), (cls + "\n").encode())

for name, data in {**valid, **bad}.items():
    decomp_case(name, data)
for name, data in raw.items():
    write(os.path.join(here, "compress", name, "input"), data)
write(os.path.join(here, "compress", "block-at-limit", "input"), block_bytes(level1_limit))
write(os.path.join(here, "compress", "block-over-limit", "input"), block_bytes(level1_limit + 1))
write(os.path.join(here, "compress", "concatenated", "input"), b"hello\nworld\n")

# Sanity: the cases the task names must have the expected outcome.
for name in valid:
    assert os.path.exists(os.path.join(here, "decompress", name, "expected")), name
for i in (1, 2, 3):
    assert read(os.path.join(here, "decompress", f"sample{i}", "expected")) == raw[f"sample{i}"]
assert read(os.path.join(here, "decompress", "concatenated", "expected")) == b"hello\nworld\n"
assert read(os.path.join(here, "decompress", "trailing-garbage", "expected")) == b"hello\n"
assert read(os.path.join(here, "decompress", "block-over-limit", "expected")) == block_bytes(level1_limit + 1)
for name, cls in [("trunc-header", "eof"), ("trunc-block", "eof"), ("trunc-footer", "eof"),
                  ("flip-block-crc", "data"), ("bad-magic", "magic"), ("level0", "magic"),
                  ("zero-length", "eof")]:
    got = read(os.path.join(here, "decompress", name, "error")).decode().strip()
    assert got == cls, (name, got, cls)
