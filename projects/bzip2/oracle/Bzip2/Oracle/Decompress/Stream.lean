import Bzip2.Oracle.Crc
import Bzip2.Oracle.Decompress.Block

/-!
# Oracle: one stream

`decode` reads one bzip2 stream: the header `BZh` and the level, then blocks until the
end-of-stream magic, then the combined CRC, as `BZ2_decompress` (`decompress.c:197-208`,
`decompress.c:222-235`, `decompress.c:588-612`) and `BZ2_bzDecompress` (`bzlib.c:808-855`)
do. It returns the stream's bytes and how many bytes of input the stream took.

What is settled here, in the order the C code checks it:
* The header bytes are read and checked one at a time (`decompress.c:197-208`): a byte other
  than `B`, `Z`, `h` (`bzlib_private.h:108-110`), or a level byte outside `1`..`9`, is
  `Error.magic`; an input that ends before the byte that differs is `Error.eof`. So `BX` is
  `Error.magic`, `BZ` is `Error.eof`, and the empty input is `Error.eof`.
* Each block or the end of the stream starts with a byte read at any bit offset
  (`GET_UCHAR`, `decompress.c:67-68`): `0x17` starts the end-of-stream magic, `0x31` a block
  magic, anything else is `Error.data` (`decompress.c:222-225`). The other five bytes of
  either magic are checked one at a time, and a wrong one is `Error.data`
  (`decompress.c:226-235`, `decompress.c:590-599`).
* A block is `Block.decodeBlock` (header, symbols, bytes, block CRC). Its CRC is folded into the
  combined CRC (`bzlib.c:832-835`), which starts at 0 (`bzlib.c:515`).
* After the end-of-stream magic come the 32 bits of the stored combined CRC
  (`decompress.c:601-609`); once all of them are read, a mismatch is `Error.data`
  (`bzlib.c:847-848`). Running out of input anywhere before that is `Error.eof`: `GET_BITS`
  returns `BZ_OK` with no input left (`decompress.c:54`), which `BZ2_bzBuffToBuffDecompress`
  turns into `BZ_UNEXPECTED_EOF` (`bzlib.c:1331`, `bzlib.c:1339-1342`), as `BZ2_bzRead` does
  (`bzlib.c:1207-1209`).
* Padding: the stream ends at the byte holding its last bit. `GET_BITS` takes a whole byte
  only when it needs more bits (`decompress.c:46-61`), so the bytes taken are the bits read
  rounded up to bytes, the rest of the last byte is never examined, and nothing after it is
  read. That count is what `BZ2_bzBuffToBuffDecompress` leaves of `avail_in`, subtracted from
  the input size.

The memory the C decoder allocates per stream (`decompress.c:211-219`, `BZ_MEM_ERROR`) is not
modelled.

Choices: `decode` starts at a byte offset of its input instead of taking a slice, so that
`decompress` reads concatenated streams without copying the rest of the input. The blocks are
a recursion with fuel: every block takes its 48-bit magic, so `remaining / 48 + 1` passes are
enough, and running out of fuel cannot happen.
-/

namespace Bzip2.Oracle.Decompress.Stream

open Bzip2.Oracle Bzip2.Oracle.BitIO

/-- The stream header's first three bytes, `BZh` (`bzlib_private.h:108-110`). -/
def headerMagic : Array UInt8 := #[0x42, 0x5a, 0x68]

/-- The bytes of a block magic after its first byte `0x31` (`decompress.c:226-235`). -/
def blockMagic : Array UInt8 := #[0x41, 0x59, 0x26, 0x53, 0x59]

/-- The bytes of the end-of-stream magic after its first byte `0x17` (`decompress.c:590-599`).
-/
def endMagic : Array UInt8 := #[0x72, 0x45, 0x38, 0x50, 0x90]

/-- Reads the stream header (`decompress.c:197-208`) and returns its level, 1 to 9.
`Error.magic` for a wrong byte, `Error.eof` if the input ends first. -/
def readHeader (reader : BitReader) : Except Error (Nat × BitReader) := do
  let mut r := reader
  for b in headerMagic do
    let (c, r') ← r.readByte
    r := r'
    if c != b then throw .magic
  let (level, r') ← r.readByte
  r := r'
  -- `BZ_HDR_0` is `'0'` (`bzlib_private.h:111`).
  if level < 0x31 || level > 0x39 then throw .magic
  return (level.toNat - 0x30, r)

/-- Reads the bytes `expected` one at a time; `Error.data` at the first that differs,
`Error.eof` if the input ends first. -/
def expectBytes (expected : Array UInt8) (reader : BitReader) : Except Error BitReader := do
  let mut r := reader
  for b in expected do
    let (c, r') ← r.readByte
    r := r'
    if c != b then throw (.data "Stream: bad block or end-of-stream magic")
  return r

/-- Reads blocks of a stream of level `level` from `reader`, at the first byte of a block or
end-of-stream magic, up to and including the stored combined CRC. `out` is the output so far
and `combined` the combined CRC so far. Returns the output and the reader after the stored
CRC. -/
def blocks (level : Nat) (reader : BitReader) (out : ByteArray) (combined : UInt32)
    (fuel : Nat) : Except Error (ByteArray × BitReader) :=
  match fuel with
  | 0 => .error (.data "Stream: out of fuel")
  | fuel + 1 => do
    let (first, r) ← reader.readByte
    if first == 0x17 then
      let r ← expectBytes endMagic r
      let (stored, r) ← r.readBits 32
      if stored != combined then throw (.data "Stream: combined CRC mismatch")
      return (out, r)
    else if first != 0x31 then
      throw (.data "Stream: bad block or end-of-stream magic")
    else
      let r ← expectBytes blockMagic r
      let (block, r) ← Block.decodeBlock level r
      blocks level r (out ++ block.bytes) (Crc.combine combined block.blockCRC) fuel

/-- Decodes the stream that starts at byte `start` of `input`: its bytes, and how many bytes of
`input` from `start` on the stream took. Bytes after the stream are not read. -/
def decode (input : ByteArray) (start : Nat := 0) : Except Error (ByteArray × Nat) := do
  let (level, r) ← readHeader { data := input, pos := start * 8 }
  let (out, r) ← blocks level r ByteArray.empty 0 (r.remaining / 48 + 1)
  return (out, r.bytePos - start)

end Bzip2.Oracle.Decompress.Stream
