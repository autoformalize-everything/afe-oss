import Bzip2.Oracle.BitIO
import Bzip2.Oracle.Crc
import Bzip2.Oracle.Compress.Blocks
import Bzip2.Oracle.Compress.Bwt
import Bzip2.Oracle.Compress.Mtf
import Bzip2.Oracle.Compress.Huffman

/-!
# Oracle: compressed stream writer

Writes the stream header, blocks and trailer of `BZ2_compressBlock` (`compress.c:602-668`),
using the symbol map, selectors, code lengths and codes of `sendMTFValues`
(`compress.c:497-597`). The writer keeps bits between blocks and pads only after the trailer.
The input is split like the program's streaming compressor, as described by `Blocks.split`.
-/

namespace Bzip2.Oracle.Compress.Stream

open BitIO

/-- Writes a sequence of bytes at the current bit position. -/
def writeBytes (w : BitWriter) (bytes : Array UInt8) : BitWriter :=
  bytes.foldl (fun w b => w.writeByte b) w

/-- Writes a 32-bit CRC, most significant byte first (`compress.c:83-89`). -/
def writeUInt32 (w : BitWriter) (v : UInt32) : BitWriter :=
  (((w.writeByte (v >>> 24).toUInt8).writeByte (v >>> 16).toUInt8).writeByte
    (v >>> 8).toUInt8).writeByte v.toUInt8

/-- Writes the 16 group flags and the 16 flags of each used group (`compress.c:497-517`). -/
def writeMap (w : BitWriter) (inUse : Array Bool) : BitWriter := Id.run do
  let mut w := w
  for i in [0:16] do
    let mut used := false
    for j in [0:16] do
      used := used || inUse[i * 16 + j]!
    w := w.writeBit used
  for i in [0:16] do
    let mut used := false
    for j in [0:16] do
      used := used || inUse[i * 16 + j]!
    if used then
      for j in [0:16] do
        w := w.writeBit inUse[i * 16 + j]!
  return w

/-- Writes MTF-coded unary selectors (`compress.c:462-477`, `compress.c:520-526`). -/
def writeSelectors (w : BitWriter) (tables : Huffman.Tables) : BitWriter := Id.run do
  let mut w := (w.writeBits 3 tables.nGroups.toUInt32).writeBits 15
    tables.selector.size.toUInt32
  let mut pos := Array.range tables.nGroups
  for sel in tables.selector do
    let mut j := 0
    while pos[j]! != sel do
      j := j + 1
    for _ in [0:j] do
      w := w.writeBit true
    w := w.writeBit false
    let mut k := j
    while k > 0 do
      pos := pos.set! k pos[k - 1]!
      k := k - 1
    pos := pos.set! 0 sel
  return w

/-- Writes the initial length and successive deltas for each table (`compress.c:533-542`). -/
def writeLengths (w : BitWriter) (tables : Huffman.Tables) : BitWriter := Id.run do
  let mut w := w
  for lens in tables.len do
    let mut curr := lens[0]!
    w := w.writeBits 5 curr.toUInt32
    for len in lens do
      while curr < len do
        w := w.writeBits 2 2
        curr := curr + 1
      while curr > len do
        w := w.writeBits 2 3
        curr := curr - 1
      w := w.writeBit false
  return w

/-- Writes each MTF symbol with the selected table's canonical code (`compress.c:551-597`). -/
def writeSymbols (w : BitWriter) (syms : Array UInt16) (tables : Huffman.Tables) :
    BitWriter := Id.run do
  let mut w := w
  for i in [0:syms.size] do
    let table := tables.selector[i / Huffman.groupSize]!
    let sym := syms[i]!.toNat
    w := w.writeBits (tables.len[table]![sym]!) (tables.code[table]![sym]!).toUInt32
  return w

/-- Writes one nonempty block, including its CRC, BWT pointer and coded symbols
(`compress.c:630-653`). -/
def writeBlock (w : BitWriter) (block : Blocks.Block) : BitWriter := Id.run do
  let mut w := writeBytes w #[0x31, 0x41, 0x59, 0x26, 0x53, 0x59]
  w := writeUInt32 w block.crc
  w := w.writeBit false
  let (last, origPtr) := Bwt.bwt block.data
  w := w.writeBits 24 origPtr.toUInt32
  let mtf := Mtf.generateMtf last block.inUse
  let tables := Huffman.choose mtf.syms (mtf.nInUse + 2)
  w := writeMap w block.inUse
  w := writeSelectors w tables
  w := writeLengths w tables
  return writeSymbols w mtf.syms tables

/-- Compresses `input` at `level` in 1..9 as one stream (`compress.c:622-668`). -/
def compress (level : Nat) (input : ByteArray) : ByteArray := Id.run do
  let mut w := writeBytes BitWriter.empty #[0x42, 0x5a, 0x68, (0x30 + level).toUInt8]
  let mut combined : UInt32 := 0
  for block in Blocks.split level input do
    combined := Crc.combine combined block.crc
    w := writeBlock w block
  w := writeBytes w #[0x17, 0x72, 0x45, 0x38, 0x50, 0x90]
  return (writeUInt32 w combined).finish

end Bzip2.Oracle.Compress.Stream
