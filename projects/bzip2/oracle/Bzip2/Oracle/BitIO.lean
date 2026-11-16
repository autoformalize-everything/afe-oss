import Bzip2.Oracle.Error

/-!
# Oracle: bit reader and writer

Bits over `ByteArray`, most significant bit first: the first bit read or written is bit 7 of
byte 0, as in bzip2's `GET_BITS` (`decompress.c:43-65`: a byte is shifted into the low end of
`bsBuff`, a value is taken from the top of the live bits) and `bsW` (`compress.c:73-78`: a value
is or-ed in just below the live bits), and `bsFinishWrite` (`compress.c:46-55`: the last byte is
padded with zero bits). Nothing here is specific to bzip2 beyond that bit order.

Choices: `readBits` and `writeBits` take any `n ≤ 32` (the C code never asks for more than 24);
`readBits` with `n > 32` is `Error.param`, `writeBits` clamps `n` to 32. A short read is
`Error.eof` and leaves the reader unchanged. `writeBits` keeps only the low `n` bits of its
argument. The position is a `Nat` of bits, so inputs of any size are fine.

Neither side allocates per bit: reads gather whole byte fragments into a `UInt64`, writes
accumulate in a `UInt64` and push whole bytes.
-/

namespace Bzip2.Oracle.BitIO

/-- A reader: the input and the position in bits from its start. -/
structure BitReader where
  /-- The input. -/
  data : ByteArray
  /-- Bit position; bit `p` is bit `7 - p % 8` of byte `p / 8`. -/
  pos : Nat := 0
  deriving Inhabited

namespace BitReader

/-- A reader at the first bit of `data`. -/
def ofByteArray (data : ByteArray) : BitReader := { data }

/-- Number of bits left. -/
def remaining (r : BitReader) : Nat := r.data.size * 8 - r.pos

/-- Whether all bits are consumed. -/
def atEnd (r : BitReader) : Bool := r.data.size * 8 ≤ r.pos

/-- Reads `n ≤ 32` bits as a number, the first bit read being the most significant. Fails with
`Error.eof` (reader unchanged) if fewer than `n` bits remain, and with `Error.param` if `n > 32`. -/
def readBits (r : BitReader) (n : Nat) : Except Error (UInt32 × BitReader) :=
  if n > 32 then .error (.param "readBits: n > 32")
  else if n > r.remaining then .error .eof
  else Id.run do
    let mut acc : UInt64 := 0
    let mut p := r.pos
    let mut left := n
    while left > 0 do
      let byte := (r.data.get! (p / 8)).toUInt64
      let avail := 8 - p % 8
      let take := if left < avail then left else avail
      let bits := (byte >>> (avail - take).toUInt64) &&& ((1 <<< take.toUInt64) - 1)
      acc := (acc <<< take.toUInt64) ||| bits
      p := p + take
      left := left - take
    return .ok (acc.toUInt32, { r with pos := p })

/-- Reads one bit. `Error.eof` at the end. -/
def readBit (r : BitReader) : Except Error (Bool × BitReader) :=
  if r.atEnd then .error .eof
  else
    let b := ((r.data.get! (r.pos / 8)) >>> (7 - r.pos % 8).toUInt8) &&& 1
    .ok (b != 0, { r with pos := r.pos + 1 })

/-- Reads one byte (8 bits, not necessarily aligned). -/
def readByte (r : BitReader) : Except Error (UInt8 × BitReader) :=
  match r.readBits 8 with
  | .ok (v, r') => .ok (v.toUInt8, r')
  | .error e => .error e

/-- Position in bits. -/
def bitPos (r : BitReader) : Nat := r.pos

/-- Position in whole bytes, rounding up (bytes touched so far). -/
def bytePos (r : BitReader) : Nat := (r.pos + 7) / 8

end BitReader

/-- A writer: finished bytes plus up to 7 pending bits in `acc` (low `nbits` bits). -/
structure BitWriter where
  /-- Whole bytes written so far. -/
  buf : ByteArray := ByteArray.empty
  /-- The pending bits, in the low `nbits` bits; the rest is zero. -/
  acc : UInt64 := 0
  /-- How many bits are pending (at most 7). -/
  nbits : Nat := 0
  deriving Inhabited

namespace BitWriter

/-- A writer with nothing written. -/
def empty : BitWriter := {}

/-- Number of bits written so far. -/
def bitLen (w : BitWriter) : Nat := w.buf.size * 8 + w.nbits

/-- Pushes whole bytes out of the top of `acc` while `nb ≥ 8`; at most 5 bytes can be pending. -/
private def flush (buf : ByteArray) (acc : UInt64) (nb : Nat) (fuel : Nat) : ByteArray × Nat :=
  match fuel with
  | 0 => (buf, nb)
  | fuel + 1 =>
    if nb ≥ 8 then flush (buf.push ((acc >>> (nb - 8).toUInt64).toUInt8)) acc (nb - 8) fuel
    else (buf, nb)

/-- Writes the low `n ≤ 32` bits of `v`, most significant first. Larger `n` is clamped to 32. -/
def writeBits (w : BitWriter) (n : Nat) (v : UInt32) : BitWriter :=
  let n := if n > 32 then 32 else n
  let masked : UInt64 := v.toUInt64 &&& ((1 <<< n.toUInt64) - 1)
  let acc := (w.acc <<< n.toUInt64) ||| masked
  let (buf, nb) := flush w.buf acc (w.nbits + n) 5
  { buf, acc := acc &&& ((1 <<< nb.toUInt64) - 1), nbits := nb }

/-- Writes one bit. -/
def writeBit (w : BitWriter) (b : Bool) : BitWriter := w.writeBits 1 (if b then 1 else 0)

/-- Writes one byte (8 bits, not necessarily aligned). -/
def writeByte (w : BitWriter) (b : UInt8) : BitWriter := w.writeBits 8 b.toUInt32

/-- Pads the last byte with zero bits and returns all bytes. -/
def finish (w : BitWriter) : ByteArray :=
  if w.nbits = 0 then w.buf
  else w.buf.push ((w.acc <<< (8 - w.nbits).toUInt64).toUInt8)

end BitWriter

end Bzip2.Oracle.BitIO
