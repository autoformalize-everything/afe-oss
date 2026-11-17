import Bzip2.Oracle.Decompress.Huffman

/-!
# Oracle: block header

`parse` reads the block CRC, randomisation flag, original pointer, symbol map, selectors and
Huffman lengths after the block magic, stopping before the first coded symbol. It follows
`BZ2_decompress` (`decompress.c:241-352`). `blockSize100k` is the already validated stream
level, 1 through 9. An invalid caller-supplied level is `Error.param`.

The used-byte map is an `Array UInt8` in byte order, as `makeMaps_d` produces
(`decompress.c:27-35`). Selectors are the decoded group indices, capped at 18002, while the
reader still consumes and validates every encoded selector (`decompress.c:291-319`). Lengths
become one `Huffman.Tables` per group. A short read is `Error.eof`; in the C streaming API,
the corresponding `GET_BITS` returns `BZ_OK` until more input arrives (`decompress.c:43-65`).
-/

namespace Bzip2.Oracle.Decompress.Header

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Huffman

/-- Maximum number of selectors stored for a block (`bzlib_private.h:125`). -/
def maxSelectors : Nat := 18002

/-- Header state used by the next decompression stage. -/
structure Header where
  /-- CRC stored at the start of the block. -/
  storedBlockCRC : UInt32
  /-- Whether the block uses the legacy randomisation transform. -/
  blockRandomised : Bool
  /-- Original row of the block sorting transform. -/
  origPtr : Nat
  /-- Bytes present in the block, in increasing byte order. -/
  usedBytes : Array UInt8
  /-- Number of Huffman symbols, including RUNA and end of block. -/
  alphaSize : Nat
  /-- Decoded group index for each retained selector. -/
  selectors : Array Nat
  /-- One Huffman decoding table for each group. -/
  tables : Array Tables
  deriving Inhabited

/-- Reads the fields after a block's 48-bit magic, up to the first Huffman-coded symbol.
`blockSize100k` is the level read from the stream header. -/
def parse (blockSize100k : Nat) (reader : BitReader) : Except Error (Header × BitReader) := do
  if blockSize100k < 1 || blockSize100k > 9 then
    throw (.param "block size outside 1..9")
  let mut r := reader
  let (crc, r') ← r.readBits 32
  r := r'
  let (randomised, r') ← r.readBit
  r := r'
  let (ptr, r') ← r.readBits 24
  r := r'
  let origPtr := ptr.toNat
  if origPtr > 10 + 100000 * blockSize100k then
    throw (.data "origPtr exceeds block size")

  let mut inUse16 := Array.replicate 16 false
  for i in [0:16] do
    let (bit, r') ← r.readBit
    r := r'
    inUse16 := inUse16.set! i bit
  let mut usedBytes : Array UInt8 := #[]
  for i in [0:16] do
    if inUse16[i]! then
      for j in [0:16] do
        let (bit, r') ← r.readBit
        r := r'
        if bit then usedBytes := usedBytes.push (i * 16 + j).toUInt8
  if usedBytes.isEmpty then throw (.data "empty symbol map")
  let alphaSize := usedBytes.size + 2

  let (groups, r') ← r.readBits 3
  r := r'
  let nGroups := groups.toNat
  if nGroups < 2 || nGroups > 6 then throw (.data "group count outside 2..6")
  let (selectorCount, r') ← r.readBits 15
  r := r'
  let nSelectors := selectorCount.toNat
  if nSelectors == 0 then throw (.data "zero selectors")
  let mut selectorMtf : Array Nat := #[]
  for i in [0:nSelectors] do
    let mut v := 0
    let mut more := true
    while more do
      let (bit, r') ← r.readBit
      r := r'
      if bit then
        v := v + 1
        if v ≥ nGroups then throw (.data "selector exceeds group count")
      else more := false
    if i < maxSelectors then selectorMtf := selectorMtf.push v

  let mut pos := (Array.range nGroups)
  let mut selectors : Array Nat := #[]
  for v in selectorMtf do
    let group := pos[v]!
    for k in [0:v] do
      pos := pos.set! (v - k) (pos[v - k - 1]!)
    pos := pos.set! 0 group
    selectors := selectors.push group

  let mut tables : Array Tables := #[]
  for _ in [0:nGroups] do
    let (initial, r') ← r.readBits 5
    r := r'
    let mut curr := initial.toNat
    let mut lengths : Array UInt8 := #[]
    for _ in [0:alphaSize] do
      let mut changing := true
      while changing do
        if curr < 1 || curr > 20 then throw (.data "code length outside 1..20")
        let (bit, r') ← r.readBit
        r := r'
        if bit then
          let (direction, r') ← r.readBit
          r := r'
          curr := if direction then curr - 1 else curr + 1
        else changing := false
      lengths := lengths.push curr.toUInt8
    tables := tables.push (createDecodeTables lengths
      (lengths.foldl (fun m l => min m l.toNat) 32)
      (lengths.foldl (fun m l => max m l.toNat) 0))
  let header : Header :=
    { storedBlockCRC := crc
      blockRandomised := randomised
      origPtr := origPtr
      usedBytes := usedBytes
      alphaSize := alphaSize
      selectors := selectors
      tables := tables }
  return (header, r)

end Bzip2.Oracle.Decompress.Header
