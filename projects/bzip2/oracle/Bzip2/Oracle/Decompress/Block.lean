import Bzip2.Oracle.Crc
import Bzip2.Oracle.Decompress.Symbols
import Bzip2.Oracle.Decompress.Block.Rand

/-!
# Oracle: a block's bytes

`output` turns a block's BWT output (`Symbols.Block`) into the bytes it stands for, as the end
of `BZ2_decompress` (`decompress.c:497-580`, the fast mode) and `unRLE_obuf_to_output_FAST`
(`bzlib.c:536-682`) do, and checks the block CRC as `BZ2_bzDecompress` does
(`bzlib.c:824-831`). `decodeBlock` is a whole block: `Header.parse`, `Symbols.decode`, `output`.

The steps, and what is settled here:
* `origPtr` must be below `nblock`, the block's length (`decompress.c:497-498`), so an empty
  block is always `Error.data`. (`Header.parse` has already checked the looser bound
  `origPtr ≤ 10 + 100000 * blockSize100k`, `decompress.c:263`.)
* `cftab` is the running sum of the byte counts `unzftab` (`decompress.c:507-509`), after the
  checks that each count (`decompress.c:502-505`) and each sum (`decompress.c:511-516`) is at
  most `nblock`; all of them are `Error.data`. The sums are `Nat`s here, so the third check,
  that they do not descend (`decompress.c:518-522`), always holds. For a block that
  `Symbols.decode` made, `unzftab` is the true count of each byte and none of them fail.
* The links: entry `cftab[b]` of `tt` gets the index of the next byte `b` in its upper 24 bits
  (`decompress.c:566-570`). The walk starts at `tt[origPtr] >> 8` (`decompress.c:572`), and
  each step (`BZ_GET_FAST`, `bzlib_private.h:444-449`) moves to the link of the current entry
  and yields that entry's byte. The C walk is `nblock` steps long, plus one that reads the
  byte after the last one and ignores it; it never checks that the links form one cycle, so a
  wrong `origPtr` below `nblock` gives other bytes, which only the CRC can reject. The bound
  check of `BZ_GET_FAST` (`bzlib_private.h:446`) cannot fail: every link is below `nblock`.
* A randomised block (the flag, `decompress.c:251`) has the low bit of each byte flipped by
  the mask `Rand.next` after the step (`decompress.c:574-577`, `bzlib.c:565-586`).
* RLE1: four equal bytes are followed by a count byte `k`, and stand for `k + 4` copies
  (`bzlib.c:582-586`, `bzlib.c:658-660`). Any count is accepted: a count over 251 gives a run
  over 255, which no compressor writes. A run of 1 to 3 may end the block. When four equal
  bytes end the block, the C code reads the count and the byte after it from past the end,
  writes the run, and then finds it has read two bytes too many: `Error.data`
  (`bzlib.c:560-561`, `bzlib.c:633-634`).
* The CRC of the bytes is compared with the stored one (`bzlib.c:824-831`); a mismatch is
  `Error.data`.

That is the behaviour of `BZ2_bzDecompress` (the library); the C code writes the bytes of a
block before it finds its CRC wrong or its last run cut off, so a caller of the library sees
them. Here a block that fails gives only the error.

Choices: `tt` is the `Array UInt32` of `Symbols.Block`, updated in place, with the links in
the upper 24 bits as in C (`nblock ≤ 900000 < 2 ^ 24`). The C decoder has two output loops,
for randomised blocks and others (`bzlib.c:540-587`, `bzlib.c:589-680`). Apart from the mask
they differ only in the order of their tests on `nblock_used` (`bzlib.c:557-561` against
`bzlib.c:633-639`, `bzlib.c:567-568` against `bzlib.c:642-646`), which changes neither the
bytes written nor the result; this module has one loop, which follows the randomised one. The
`smallDecompress` mode (`unRLE_obuf_to_output_SMALL`) writes the same bytes and is not
modelled. The output is a `ByteArray` that grows by one byte at a time, with the CRC updated
as it grows.
-/

namespace Bzip2.Oracle.Decompress.Block

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Header
  Bzip2.Oracle.Decompress.Symbols

/-- A decoded block: its bytes, and their CRC (which equals the stored one). -/
structure Output where
  /-- The block's bytes. -/
  bytes : ByteArray
  /-- The block CRC, as the combined stream CRC takes it in. -/
  blockCRC : UInt32
  deriving Inhabited

/-- `cftab` (`decompress.c:500-522`): entry `b` is the number of bytes below `b` in a block of
`nblock` bytes with byte counts `unzftab` (257 entries). `Error.data` if a count or a sum is
over `nblock`. -/
def cftab (unzftab : Array UInt32) (nblock : Nat) : Except Error (Array Nat) := Id.run do
  let mut c : Array Nat := Array.replicate 257 0
  for i in [0:256] do
    let n := (unzftab[i]?.getD 0).toNat
    if n > nblock then return .error (.data "Block: unzftab entry over nblock")
    c := c.set! (i + 1) (c[i]! + n)
    if c[i + 1]! > nblock then return .error (.data "Block: cftab entry over nblock")
  return .ok c

/-- `tt` with the links of the inverse transform in its upper 24 bits (`decompress.c:566-570`):
the entry of the `j`-th byte `b` in sorted order, `cftab[b] + j`, links to the index of the
`j`-th `b` in `tt`. -/
def links (tt : Array UInt32) (cftab : Array Nat) : Array UInt32 := Id.run do
  let mut tt := tt
  let mut c := cftab
  for i in [0:tt.size] do
    let uc := (tt[i]! &&& 0xff).toNat
    tt := tt.modify c[uc]! (· ||| (i.toUInt32 <<< 8))
    c := c.modify uc (· + 1)
  return tt

/-- Where the walk is: the C decoder's `tPos`, `nblock_used` and randomisation state. -/
structure Walk where
  /-- The entry of `tt` the next step reads (`tPos`). -/
  tPos : Nat
  /-- The number of steps taken (`nblock_used`). -/
  used : Nat
  /-- The randomisation mask's state (`rNToGo`, `rTPos`). -/
  rand : Rand.State

/-- One step of the walk: `BZ_GET_FAST` (`bzlib_private.h:444-449`), then, in a randomised
block, `BZ_RAND_UPD_MASK` and the flip by `BZ_RAND_MASK` (`bzlib.c:565-566`). -/
@[inline] def Walk.next (tt : Array UInt32) (randomised : Bool) (w : Walk) : UInt8 × Walk :=
  let e := tt[w.tPos]!
  let k := (e &&& 0xff).toUInt8
  let tPos := (e >>> 8).toNat
  if randomised then
    let (flip, rand) := Rand.next w.rand
    (if flip then k ^^^ 1 else k, { tPos, used := w.used + 1, rand })
  else (k, { tPos, used := w.used + 1, rand := w.rand })

/-- Appends `n` copies of `ch` to `out`, folding them into the CRC state `crc`
(`bzlib.c:544-554`). -/
def emit (out : ByteArray) (crc : UInt32) (ch : UInt8) : Nat → ByteArray × UInt32
  | 0 => (out, crc)
  | n + 1 => emit (out.push ch) (Crc.updateByte crc ch) ch n

/-- The output loop of `unRLE_obuf_to_output_FAST` (`bzlib.c:542-587`) for a block of
`nblock` bytes, from the walk `w` with the byte `k0` read and not yet written. Returns the
bytes appended to `out` and the CRC state. Each pass takes at least one step, so `nblock + 1`
passes (`fuel`) are enough. -/
def unRLE (tt : Array UInt32) (randomised : Bool) (nblock : Nat) (w : Walk) (k0 : UInt8)
    (out : ByteArray) (crc : UInt32) (fuel : Nat) : Except Error (ByteArray × UInt32) :=
  match fuel with
  | 0 => .error (.data "Block: out of fuel")
  | fuel + 1 =>
    if w.used == nblock + 1 then .ok (out, crc)
    else if w.used > nblock + 1 then .error (.data "Block: run cut off by the block end")
    else
      -- A run ends at a different byte, or at the block end (`bzlib.c:563-580`).
      let (k1, w) := w.next tt randomised
      if w.used == nblock + 1 || k1 != k0 then
        let (out, crc) := emit out crc k0 1
        unRLE tt randomised nblock w k1 out crc fuel
      else
      let (k1, w) := w.next tt randomised
      if w.used == nblock + 1 || k1 != k0 then
        let (out, crc) := emit out crc k0 2
        unRLE tt randomised nblock w k1 out crc fuel
      else
      let (k1, w) := w.next tt randomised
      if w.used == nblock + 1 || k1 != k0 then
        let (out, crc) := emit out crc k0 3
        unRLE tt randomised nblock w k1 out crc fuel
      else
      -- Four equal bytes: the count, then the next byte (`bzlib.c:582-586`).
      let (count, w) := w.next tt randomised
      let (k1, w) := w.next tt randomised
      let (out, crc) := emit out crc k0 (count.toNat + 4)
      unRLE tt randomised nblock w k1 out crc fuel

/-- The bytes of the block with header `h` and BWT output `b`, and their CRC. Errors, all
`Error.data`: `origPtr ≥ nblock`, `unzftab` or `cftab` out of range, four equal bytes at the
end of the block, a CRC other than the stored one. -/
def output (h : Header) (b : Symbols.Block) : Except Error Output := do
  let nblock := b.tt.size
  if h.origPtr ≥ nblock then throw (.data "Block: origPtr not below nblock")
  let c ← cftab b.unzftab nblock
  let tt := links b.tt c
  let w : Walk := { tPos := (tt[h.origPtr]! >>> 8).toNat, used := 0, rand := Rand.init }
  let (k0, w) := w.next tt h.blockRandomised
  let (bytes, crc) ← unRLE tt h.blockRandomised nblock w k0
    (ByteArray.emptyWithCapacity nblock) Crc.init (nblock + 1)
  let blockCRC := Crc.finalise crc
  if blockCRC != h.storedBlockCRC then throw (.data "Block: block CRC mismatch")
  return { bytes, blockCRC }

/-- Decodes one block of a stream of level `blockSize100k`, reading from `reader` just after
the block's 48-bit magic: its header, symbols and bytes. Returns the block and the reader
after its end-of-block symbol. Errors: those of `Header.parse` and `Symbols.decode`
(`Error.param` for a level outside 1..9, `Error.eof` for input that ends inside the block,
`Error.data`), then those of `output`. -/
def decodeBlock (blockSize100k : Nat) (reader : BitReader) :
    Except Error (Output × BitReader) := do
  let (h, r) ← parse blockSize100k reader
  let (b, r) ← decode blockSize100k h r
  let out ← output h b
  return (out, r)

end Bzip2.Oracle.Decompress.Block
