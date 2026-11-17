import Bzip2.Oracle.Decompress.Header

/-!
# Oracle: block symbols to BWT output

`decode` reads a block's Huffman-coded symbols, 50 to a selector, until the end-of-block symbol,
and undoes the zero-run code (RUNA/RUNB) and the move-to-front transform, as the loop after the
coding tables in `BZ2_decompress` does (`decompress.c:354-490`). Its result is the block's
`tt` contents (`Block.tt`, the bytes of the Burrows-Wheeler transform's last column, before the
inverse transform adds the links in the upper 24 bits) and the byte counts `unzftab`
(`decompress.c:362`).

What is settled here:
* A symbol is read with `Huffman.decodeSym` (`GET_MTF_VAL`, `decompress.c:74-102`). Each group
  of 50 symbols uses the table of the next selector (`decompress.c:77-87`); a 51st symbol after
  the last selector is `Error.data` (`decompress.c:78-79`), before any bit is read. The header
  keeps at most 18002 selectors (`decompress.c:305-306`), which is all the C loop sees.
* Symbol 0 and 1 (RUNA, RUNB) start a run whose length is the bijective base 2 number of the
  following run symbols (`decompress.c:386-404`); the byte repeated is the front of the
  move-to-front list (`decompress.c:405`). A run symbol seen with `N ≥ 2 * 1024 * 1024`
  already is `Error.data` (`decompress.c:396`). The symbol after a run is read before the run is
  written, so an input that ends there is `Error.eof` even if the run is over the block limit.
* A byte past `100000 * level` is `Error.data` (`decompress.c:410`, `decompress.c:417`,
  `decompress.c:427`); a run is checked as a whole, which gives the same error. The block may
  be exactly that long.
* Any other symbol `s` (`2 ≤ s < EOB`) moves entry `s - 1` of the move-to-front list to the
  front and emits the byte it maps to (`decompress.c:427-487`). `EOB` is `alphaSize - 1`
  (`decompress.c:357`).
* Running out of input anywhere before EOB is `Error.eof`: the C code's `GET_BITS` returns
  `BZ_OK` with no input left (`decompress.c:54`), which `BZ2_bzRead` turns into
  `BZ_UNEXPECTED_EOF` (`bzlib.c:1204-1209`).
* The checks after EOB (`origPtr < nblock`, `unzftab` and `cftab` ranges,
  `decompress.c:497-523`) belong to the inverse transform, not to this part; an empty block
  (EOB first) is returned as it is.

Choices: the C code keeps the move-to-front list as 16 lists of 16 inside a 4096-byte array
(`mtfa`, `mtfbase`, `decompress.c:364-376`) to move less memory; this module keeps one
256-byte `ByteArray` and shifts, which gives the same list at every step. `tt` is an
`Array UInt32` holding one byte per entry, as C's `tt` does before the inverse transform;
`unzftab` is an `Array UInt32` of 256 counts. The C code has a second, `smallDecompress`
mode, whose `ll16` holds the same bytes; it is not modelled. Arrays and the list are updated in
place (they are never shared inside the loop).
-/

namespace Bzip2.Oracle.Decompress.Symbols

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Huffman
  Bzip2.Oracle.Decompress.Header

/-- `BZ_G_SIZE`: symbols coded with one selector (`bzlib_private.h:122`). -/
def groupSize : Nat := 50

/-- The decoded contents of a block. -/
structure Block where
  /-- The block's bytes in transform order: the low byte of each `tt` entry. -/
  tt : Array UInt32
  /-- How many times each byte value occurs in `tt` (256 entries). -/
  unzftab : Array UInt32
  deriving Inhabited

/-- Where the next symbol is read from: the reader, the number of selectors used so far
(`groupNo + 1` in the C code) and how many symbols are left of the current group (`groupPos`). -/
structure Cursor where
  /-- The input after the symbols read so far. -/
  reader : BitReader
  /-- Number of selectors consumed. -/
  groupsUsed : Nat
  /-- Symbols left in the current group. -/
  groupPos : Nat

/-- `GET_MTF_VAL` with its selector bookkeeping (`decompress.c:76-101`): when the group is used
up, takes the next selector or fails with `Error.data` if none is left. -/
def nextSym (h : Header) (c : Cursor) : Except Error (Nat × Cursor) :=
  if c.groupPos == 0 && c.groupsUsed ≥ h.selectors.size then
    .error (.data "Symbols: out of selectors")
  else
    let groupsUsed := if c.groupPos == 0 then c.groupsUsed + 1 else c.groupsUsed
    let groupPos := if c.groupPos == 0 then groupSize else c.groupPos
    let sel := h.selectors[groupsUsed - 1]!
    match decodeSym h.tables[sel]! c.reader with
    | .error e => .error e
    | .ok (s, r) => .ok (s, { reader := r, groupsUsed, groupPos := groupPos - 1 })

/-- Moves entry `k` of the list to the front, in place: entries `0 ..< k` shift up by one
(`decompress.c:427-487`). -/
private def shiftUp (m : ByteArray) : Nat → ByteArray
  | 0 => m
  | k + 1 => shiftUp (m.set! (k + 1) (m.get! k)) k

/-- The list with entry `k` moved to the front, and that entry. -/
private def moveToFront (m : ByteArray) (k : Nat) : UInt8 × ByteArray :=
  let b := m.get! k
  (b, (shiftUp m k).set! 0 b)

/-- Appends `n` copies of `b` to `tt` (the run loops, `decompress.c:407-421`). -/
private def pushRun (tt : Array UInt32) (b : UInt32) : Nat → Array UInt32
  | 0 => tt
  | n + 1 => pushRun (tt.push b) b n

/-- The symbol loop of `BZ2_decompress` (`decompress.c:379-490`), run to EOB. Each pass adds
at least one byte (a run is at least one byte long), so `fuel = nblockMAX + 1` passes are
enough: after `nblockMAX` bytes the next pass reaches EOB or the size limit. -/
private def loop (h : Header) (nblockMAX : Nat) (c : Cursor) (sym : Nat)
    (tt : Array UInt32) (unzftab : Array UInt32) (mtf : ByteArray) (fuel : Nat) :
    Except Error (Block × BitReader) :=
  match fuel with
  | 0 => .error (.data "Symbols: too many symbols")
  | fuel + 1 =>
    if sym + 1 == h.alphaSize then .ok ({ tt, unzftab }, c.reader)
    else if sym < 2 then
      match runLength h c sym 0 0 with
      | .error e => .error e
      | .ok (es, sym, c) =>
        let uc := h.usedBytes[(mtf.get! 0).toNat]!
        if tt.size + es > nblockMAX then .error (.data "Symbols: block over the size limit")
        else
          loop h nblockMAX c sym (pushRun tt uc.toUInt32 es)
            (unzftab.modify uc.toNat (· + es.toUInt32)) mtf fuel
    else if tt.size ≥ nblockMAX then .error (.data "Symbols: block over the size limit")
    else
      let (i, mtf) := moveToFront mtf (sym - 1)
      let uc := h.usedBytes[i.toNat]!
      match nextSym h c with
      | .error e => .error e
      | .ok (sym', c) =>
        loop h nblockMAX c sym' (tt.push uc.toUInt32) (unzftab.modify uc.toNat (· + 1)) mtf fuel
where
  /-- The RUNA/RUNB loop (`decompress.c:392-401`): the run length so far `es`, and `e` with
  `N = 2 ^ e` the weight of the digit `sym`; returns the run length and the first symbol after
  the run. `N ≥ 2 * 1024 * 1024` is `e ≥ 21` (`decompress.c:396`). -/
  runLength (h : Header) (c : Cursor) (sym es e : Nat) :
      Except Error (Nat × Nat × Cursor) :=
    if e ≥ 21 then .error (.data "Symbols: run too long")
    else
      match nextSym h c with
      | .error e => .error e
      | .ok (sym', c) =>
        let es := es + (sym + 1) * 2 ^ e
        if sym' < 2 then runLength h c sym' es (e + 1) else .ok (es, sym', c)
  termination_by 21 - e

/-- Decodes the symbols of a block that follows the header `h`, reading from `reader` (the
position `Header.parse` returned), for stream level `blockSize100k`, up to and including EOB.
Returns the block and the reader after EOB. Errors: `Error.param` for a level outside 1..9;
`Error.data` for a run that is too long, a block over `100000 * blockSize100k` bytes, or no
selector left for the next symbol, or a code that the tables do not give; `Error.eof` if the
input ends before EOB. -/
def decode (blockSize100k : Nat) (h : Header) (reader : BitReader) :
    Except Error (Block × BitReader) :=
  if blockSize100k < 1 || blockSize100k > 9 then
    .error (.param "block size outside 1..9")
  else
    let nblockMAX := 100000 * blockSize100k
    match nextSym h { reader, groupsUsed := 0, groupPos := 0 } with
    | .error e => .error e
    | .ok (sym, c) =>
      loop h nblockMAX c sym (Array.emptyWithCapacity nblockMAX) (Array.replicate 256 0)
        (ByteArray.mk ((Array.range 256).map Nat.toUInt8)) (nblockMAX + 1)

end Bzip2.Oracle.Decompress.Symbols
