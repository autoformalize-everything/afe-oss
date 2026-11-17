import Bzip2.Oracle.BitIO
import Bzip2.Oracle.Crc
import Bzip2.Oracle.Decompress
import Bzip2.Oracle.Decompress.Block

/-!
Tests for `Bzip2.Oracle.Decompress.Stream`, `decompressStream` and `decompress`. Every check
is a `#guard`, so building this module runs them.

The streams are made by the vendored `bzip2` (`printf 'hello, world\n' | bzip2 -9`,
`printf ab | bzip2 -9`, `printf ab | bzip2 -1`), and the results expected are those the
vendored libbz2 gave, run as `uncompressStream` does by `tests/vectors/classify.c`, for the
same inputs: header and trailing-data cases, every proper prefix (`eof`), bit flips in the
combined CRC (`data`) and in the padding after it (ignored). The two-block stream is spliced
here from two one-block streams, with the combined CRC computed from their block CRCs.
-/

open Bzip2.Oracle Bzip2.Oracle.BitIO

namespace Bzip2.Test.DecompressStream

/-- A hex digit's value. -/
def hexDigit (ch : Char) : UInt8 :=
  (if ch.isDigit then ch.toNat - 48 else ch.toNat - 87).toUInt8

/-- Bytes from contiguous hex digits. -/
def fromHex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut bytes := ByteArray.empty
  for i in [0:s.length / 2] do
    bytes := bytes.push (hexDigit chars[2 * i]! * 16 + hexDigit chars[2 * i + 1]!)
  return bytes

/-- The stream of the empty input, `bzip2 -9 < /dev/null`. -/
def empty : ByteArray := fromHex "425a683917724538509000000000"

/-- `printf 'hello, world\n' | bzip2 -9`: one block, and no padding. -/
def hello : ByteArray :=
  fromHex ("425a683931415926535954a49784000002d180001040040644908020003100302068620049d4" ++
    "b21f3f17724538509054a49784")

/-- `printf ab | bzip2 -9`: one block, and 4 bits of padding. -/
def ab9 : ByteArray :=
  fromHex ("425a6839314159265359e993fdcd000000010030002000210082b177245385090e993fdcd0")

/-- `printf ab | bzip2 -1`. -/
def ab1 : ByteArray :=
  fromHex ("425a6831314159265359e993fdcd000000010030002000210082b177245385090e993fdcd0")

/-- The text of `hello`. -/
def helloText : ByteArray := "hello, world\n".toUTF8

/-- `b` with byte `i` xor-ed with `x`. -/
def flip (b : ByteArray) (i : Nat) (x : UInt8) : ByteArray := b.set! i (b.get! i ^^^ x)

/-- Whether `r` is the error `e`, by constructor. -/
def isError {α : Type} (r : Except Error α) (e : Error) : Bool :=
  match r, e with
  | .error .magic, .magic | .error .eof, .eof | .error (.data _), .data _ => true
  | _, _ => false

/-- Whether `r` is the output `out`. -/
def gives (r : Except Error ByteArray) (out : ByteArray) : Bool :=
  match r with
  | .ok o => o == out
  | .error _ => false

/-- Whether `r` is the output `out` of a stream of `used` bytes. -/
def streamGives (r : Except Error (ByteArray × Nat)) (out : ByteArray) (used : Nat) : Bool :=
  match r with
  | .ok (o, n) => o == out && n == used
  | .error _ => false

/-- A `data` error to compare with. -/
def data : Error := .data ""

-- One stream.
#guard streamGives (decompressStream empty) ByteArray.empty 14
#guard gives (decompress empty) ByteArray.empty
#guard streamGives (decompressStream hello) helloText 51
#guard gives (decompress hello) helloText
#guard gives (decompress ab9) ("ab".toUTF8)
#guard gives (decompress ab1) ("ab".toUTF8)
#guard streamGives (decompressStream ab9) ("ab".toUTF8) 37

-- The header: a wrong byte is `magic`, a short input `eof`; then a bad first byte of a block
-- or end-of-stream magic is `data`.
#guard isError (decompress ByteArray.empty) .eof
#guard isError (decompress "B".toUTF8) .eof
#guard isError (decompress "BX".toUTF8) .magic
#guard isError (decompress "BZ".toUTF8) .eof
#guard isError (decompress "BZh".toUTF8) .eof
#guard isError (decompress "BZhA".toUTF8) .magic
#guard isError (decompress "BZh0".toUTF8) .magic
#guard isError (decompress "BZh9".toUTF8) .eof
#guard isError (decompress ("BZh9".toUTF8.push 0)) data
#guard isError (decompress (fromHex "425a68393141")) .eof
#guard isError (decompress (fromHex "425a6839314100")) data
#guard isError (decompressStream "BX".toUTF8) .magic
#guard isError (decompressStream ByteArray.empty) .eof

-- Every proper prefix of a stream is `eof`, for both functions.
#guard (List.range hello.size).all fun i => isError (decompress (hello.extract 0 i)) .eof
#guard (List.range ab9.size).all fun i => isError (decompressStream (ab9.extract 0 i)) .eof

-- Block magic, block CRC, end-of-stream magic and combined CRC: a flipped bit is `data`.
#guard isError (decompress (flip hello 4 0x01)) data
#guard isError (decompress (flip hello 9 0x01)) data
#guard isError (decompress (flip hello 10 0x01)) data
#guard isError (decompress (flip empty 4 0x01)) data
#guard isError (decompress (flip empty 9 0x01)) data
#guard isError (decompress (flip empty 13 0x01)) data
#guard (List.range 8).all fun k =>
  isError (decompress (flip hello 50 (1 <<< k.toUInt8))) data
-- The first byte of a block magic changed to `0x17`: the end-of-stream magic is expected.
#guard isError (decompress (hello.set! 4 0x17)) data

-- The padding after the combined CRC (the low 4 bits of the last byte of `ab9`) is not read.
#guard (List.range 4).all fun k =>
  gives (decompress (flip ab9 36 (1 <<< k.toUInt8))) ("ab".toUTF8)
#guard isError (decompress (flip ab9 36 0x10)) data

-- Concatenated streams, of any levels: `decompress` reads them all, `decompressStream` the
-- first.
#guard gives (decompress (hello ++ ab1 ++ empty ++ ab9)) (helloText ++ "abab".toUTF8)
#guard streamGives (decompressStream (hello ++ ab1)) helloText 51
#guard streamGives (decompressStream (ab9 ++ hello)) ("ab".toUTF8) 37

/-- What the C library gave for `hello` followed by each of these bytes: `none` for the output
of `hello`, else the error. -/
def trailing : List (String × Option Error) :=
  [("", none), ("x", none), ("garbage", none), ("BZh0", none), ("B", some .eof),
   ("BZ", some .eof), ("BZh", some .eof), ("BZh9", some .eof), ("BZh9\x17", some .eof),
   ("BZh91AY&SY", some .eof), ("BZh9\x00", some data)]

-- After a first stream, a wrong header ends the input; any other error is the error.
#guard trailing.all fun (t, r) =>
  match r with
  | none => gives (decompress (hello ++ t.toUTF8)) helloText
  | some e => isError (decompress (hello ++ t.toUTF8)) e
#guard gives (decompress (hello ++ ByteArray.mk #[0])) helloText
-- A first stream with a wrong header is `magic` even after nothing else.
#guard isError (decompress ("BZh0".toUTF8 ++ hello)) .magic
-- A later stream that is corrupt or cut off is the error, not the output so far.
#guard isError (decompress (hello ++ flip hello 50 0x01)) data
#guard isError (decompress (hello ++ hello.extract 0 30)) .eof
-- `decompressStream` does not read past its stream.
#guard trailing.all fun (t, _) =>
  streamGives (decompressStream (hello ++ t.toUTF8)) helloText 51

/-- Bits `[lo, hi)` of `src` appended to `w`. -/
def copyBits (w : BitWriter) (src : ByteArray) (lo hi : Nat) : BitWriter := Id.run do
  let mut w := w
  for p in [lo:hi] do
    match ({ data := src, pos := p } : BitReader).readBit with
    | .ok (b, _) => w := w.writeBit b
    | .error _ => pure ()
  return w

/-- The bit position where the one block of the level-9 stream `z` ends, and its CRC. -/
def blockEnd (z : ByteArray) : Nat × UInt32 :=
  match Decompress.Block.decodeBlock 9 { data := z, pos := 80 } with
  | .ok (out, r) => (r.pos, out.blockCRC)
  | .error _ => (0, 0)

/-- A level-9 stream with the block of `a`, then the block of `b`, and the combined CRC
`combined` computed from the two block CRCs. -/
def spliced (a b : ByteArray) (combined : UInt32 → UInt32 → UInt32) : ByteArray :=
  let (endA, crcA) := blockEnd a
  let (endB, crcB) := blockEnd b
  let w := copyBits BitWriter.empty a 0 endA
  let w := copyBits w b 32 endB
  let w := copyBits w empty 32 80
  (w.writeBits 32 (combined crcA crcB)).finish

/-- Two blocks: `hello`'s, then `ab9`'s. -/
def twoBlocks : ByteArray :=
  spliced hello ab9 fun a b => Crc.combine (Crc.combine 0 a) b

#guard gives (decompress twoBlocks) (helloText ++ "ab".toUTF8)
#guard streamGives (decompressStream twoBlocks) (helloText ++ "ab".toUTF8) twoBlocks.size
-- The combined CRC is order-dependent: the CRCs folded in the other order are `data`.
#guard isError (decompress (spliced hello ab9 fun a b => Crc.combine (Crc.combine 0 b) a)) data
#guard (List.range twoBlocks.size).all fun i =>
  isError (decompress (twoBlocks.extract 0 i)) .eof

end Bzip2.Test.DecompressStream
