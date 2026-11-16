import Mathlib.Data.List.Basic
import Mathlib.Data.BitVec

/-!
# bzip2: CRC-32, the block CRC and the combined stream CRC

References: `upstream/crctable.c` (the table, polynomial 0x04C11DB7), `BZ_UPDATE_CRC`,
`BZ_INITIALISE_CRC`, `BZ_FINALISE_CRC` in `upstream/bzlib_private.h`, and `combinedCRC` in
`upstream/compress.c` (lines 606–608; the compressor's combination). The decompressor combines
and compares in `BZ2_bzDecompress`, `upstream/bzlib.c` lines 825–847 (`decompress.c`
lines 601–609 only read the stored trailer CRC). The block CRC covers the original bytes:
the compressor updates it per input byte in `add_pair_to_block` (`bzlib.c` lines 217–221) and
the `ADD_CHAR_TO_BLOCK` macro (`bzlib.c` lines 263–267), before the RLE1 run is coded.

The type is `BitVec 32`, not `UInt32`: `BitVec` has the full library of `bv_decide`/`simp`
lemmas (`xor`, shifts, `rotateLeft`, `getLsbD`), and later proofs over the spec need them;
`UInt32` is the oracle's business. The CRC is bitwise over `List (BitVec 8)`, with
no table, so it states what the table computes.
-/

namespace Bzip2.Spec.Crc

/-- The generator polynomial, MSB first (not reflected). -/
def crcPoly : BitVec 32 := 0x04C11DB7

/-- One bit step, MSB first: shift left, and xor the polynomial if the bit shifted out was 1. -/
def crcBit (c : BitVec 32) : BitVec 32 :=
  if c.msb then (c <<< 1) ^^^ crcPoly else c <<< 1

/-- Feed one byte, most significant bit first (`BZ_UPDATE_CRC`): xor it into the top byte, then
eight bit steps. -/
def crcUpdate (c : BitVec 32) (b : BitVec 8) : BitVec 32 :=
  (Nat.iterate crcBit 8) (c ^^^ (b.zeroExtend 32 <<< 24))

/-- The CRC-32 bzip2 uses: initial value 0xFFFFFFFF, final complement. -/
def crc32 (bytes : List (BitVec 8)) : BitVec 32 :=
  ~~~ (bytes.foldl crcUpdate 0xFFFFFFFF#32)

/-- The block CRC: the CRC of the block's original bytes (before the initial RLE and the
transform). -/
def blockCrc (bytes : List (BitVec 8)) : BitVec 32 := crc32 bytes

/-- One step of the combined CRC: `c := rotl1 c xor blockCrc`. -/
def combineCrc (c blk : BitVec 32) : BitVec 32 := c.rotateLeft 1 ^^^ blk

/-- The combined stream CRC of a list of block CRCs, starting from 0. -/
def streamCrc (blockCrcs : List (BitVec 32)) : BitVec 32 :=
  blockCrcs.foldl combineCrc 0

private def ascii (s : String) : List (BitVec 8) :=
  s.toList.map fun c => BitVec.ofNat 8 c.toNat

example : crc32 (ascii "123456789") = 0xFC891918#32 := by decide +kernel
example : crc32 [] = 0#32 := by decide +kernel
example : blockCrc (ascii "123456789") = 0xFC891918#32 := by decide +kernel

/-- A real two-block stream: `bzip2 -1` of 150000 bytes `(7*i + i/251) % 256`, `i < 150000`
compresses to two blocks; `bzip2 -vv` reports block CRCs 0xfc70ec8f and 0xb88cb15b and final
combined CRC 0x406d6844 (also the stream trailer). -/
example : streamCrc [0xfc70ec8f#32, 0xb88cb15b#32] = 0x406d6844#32 := by decide +kernel

end Bzip2.Spec.Crc
