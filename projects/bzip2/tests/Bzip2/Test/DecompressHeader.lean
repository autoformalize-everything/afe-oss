import Bzip2.Oracle.Decompress.Header

/-!
# Block header parser tests

The four vector files are bzip2 streams made with Python's `bz2.compress` at levels 1 and 9.
Their expected fields were read independently from the stream bits. Tests start at bit 80,
after the stream header and block magic. The synthetic cases exercise the error checks in
`decompress.c:261-327`, including a selector count beyond the stored limit.
-/

namespace Bzip2.Test.DecompressHeader

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Header

/-- The value after a vector field name. -/
def field (s key : String) : String :=
  (((s.splitOn "\n").find? (·.startsWith (key ++ " "))).getD "").drop
    (key.length + 1) |>.toString

/-- A byte encoded as two lowercase hexadecimal digits. -/
def hexByte (s : String) : UInt8 :=
  s.foldl (fun a ch => a * 16 +
    (if ch.isDigit then ch.toNat - 48 else ch.toNat - 87).toUInt8) 0

/-- Bytes encoded as contiguous lowercase hexadecimal digits. -/
def fromHex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut bytes := ByteArray.empty
  for i in [0:s.length / 2] do
    bytes := bytes.push (hexByte (String.ofList [chars[2 * i]!, chars[2 * i + 1]!]))
  return bytes

/-- A comma-separated array of natural numbers. -/
def naturals (s : String) : Array Nat :=
  if s.isEmpty then #[] else (s.splitOn ",").toArray.map String.toNat!

/-- Whether the parser gives the fields recorded from a real compressed stream. -/
def agrees (s : String) : Bool :=
  let r : BitReader := { data := fromHex (field s "hex"), pos := 80 }
  match parse (field s "level").toNat! r with
  | .error _ => false
  | .ok (h, after) =>
    h.storedBlockCRC.toNat == (field s "crc").toNat! &&
    h.blockRandomised == ((field s "randomised") == "1") &&
    h.origPtr == (field s "origPtr").toNat! &&
    h.usedBytes.map UInt8.toNat == naturals (field s "used") &&
    h.alphaSize == h.usedBytes.size + 2 &&
    h.selectors == naturals (field s "selectors") &&
    h.tables.size >= 2 && h.tables.size <= 6 &&
    h.tables.map (·.minLen) == naturals (field s "minLens") &&
    after.bitPos == (field s "pos").toNat!

#guard agrees (include_str "../../vectors/decompress-header/level1.txt")
#guard agrees (include_str "../../vectors/decompress-header/level9.txt")
#guard agrees (include_str "../../vectors/decompress-header/all256.txt")
#guard agrees (include_str "../../vectors/decompress-header/onebyte.txt")

/-- A compact header with one used byte, chosen group and selector fields, and constant
code lengths. `delta` changes the first length before its terminating bit. -/
def synthetic (groups : Nat) (selectors : Array Nat) (initial : Nat := 2)
    (delta : Option Bool := none) : BitWriter := Id.run do
  let mut w := BitWriter.empty
  w := w.writeBits 32 0 |>.writeBit false |>.writeBits 24 0
  w := w.writeBits 16 0x8000
  w := w.writeBits 16 0x8000
  w := w.writeBits 3 groups.toUInt32
  w := w.writeBits 15 selectors.size.toUInt32
  for v in selectors do
    for _ in [0:v] do w := w.writeBit true
    w := w.writeBit false
  for _ in [0:groups] do
    w := w.writeBits 5 initial.toUInt32
    for i in [0:3] do
      if i == 0 then
        if let some direction := delta then
          w := w.writeBit true |>.writeBit direction
      w := w.writeBit false
  return w

/-- Parses synthetic bits at the first header field. -/
def parseSynthetic (w : BitWriter) : Except Error (Header × BitReader) :=
  parse 1 (BitReader.ofByteArray w.finish)

/-- Whether the synthetic header fails as corrupt data. -/
def dataError (w : BitWriter) : Bool :=
  match parseSynthetic w with | .error (.data _) => true | _ => false

#guard dataError (synthetic 1 #[0])
#guard dataError (synthetic 7 #[0])
#guard dataError (synthetic 2 #[])
#guard dataError (synthetic 2 #[2])
#guard dataError (synthetic 2 #[0] 20 (some false))
#guard dataError (synthetic 2 #[0] 1 (some true))

-- All encoded selectors are read; only the first 18002 are retained (`decompress.c:299-306`).
#guard (let w := synthetic 2 (Array.replicate 18003 0)
  match parseSynthetic w with
  | .ok (h, r) => h.selectors.size == maxSelectors && r.bitPos == w.bitLen
  | .error _ => false)
#guard dataError (synthetic 2 ((Array.replicate 18002 0).push 2))

-- The reader reports an incomplete header as EOF, before the first coded symbol.
#guard (match parse 1 (BitReader.ofByteArray (fromHex "0000000000000000")) with
  | .error .eof => true | _ => false)

end Bzip2.Test.DecompressHeader
