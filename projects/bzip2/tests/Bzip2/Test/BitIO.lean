import Bzip2.Oracle.BitIO

/-! Unit tests of `Bzip2.Oracle.BitIO`: reads across byte boundaries, 32-bit reads, reads past
the end, and write-then-read roundtrips. -/

open Bzip2.Oracle Bzip2.Oracle.BitIO

namespace Bzip2.Test.BitIO

/-- The bytes `l` as a `ByteArray`. -/
def bytes (l : List Nat) : ByteArray := ⟨(l.map (·.toUInt8)).toArray⟩

/-- Reads the widths `ws` in order from `d`: the values and the final reader, or the error. -/
def readAll (d : ByteArray) (ws : List Nat) : Except Error (List UInt32 × BitReader) :=
  ws.foldlM (init := ([], BitReader.ofByteArray d)) fun (acc, r) w => do
    let (v, r) ← r.readBits w
    return (acc ++ [v], r)

/-- The values read by `readAll`, or `none` on error. -/
def values (d : ByteArray) (ws : List Nat) : Option (List UInt32) :=
  match readAll d ws with
  | .ok (vs, _) => some vs
  | .error _ => none

/-- Whether `readAll` fails with `Error.eof`. -/
def isEof (d : ByteArray) (ws : List Nat) : Bool :=
  match readAll d ws with
  | .error .eof => true
  | _ => false

/-- The data used by most tests. -/
def sample : ByteArray := bytes [0xA5, 0x3C, 0xFF, 0x00, 0x81]

-- MSB first
#guard values sample [1, 1, 1, 1, 1, 1, 1, 1] == some [1, 0, 1, 0, 0, 1, 0, 1]
#guard (match (BitReader.ofByteArray sample).readBit with
  | .ok (true, r) => (match r.readBit with | .ok (false, _) => true | _ => false)
  | _ => false)
-- reads across byte boundaries
#guard values sample [4, 8, 4] == some [0xA, 0x53, 0xC]
#guard values sample [12] == some [0xA53]
#guard values sample [3, 13] == some [5, 0x053C]
#guard values sample [7, 2, 9] == some [0x52, 2, 0xF3]
#guard values sample [0, 8] == some [0, 0xA5]
-- 32-bit reads
#guard values sample [32] == some [0xA53CFF00]
#guard values sample [4, 32] == some [0xA, 0x53CFF008]
#guard values (bytes [255, 255, 255, 255, 255]) [3, 32] == some [7, 0xFFFFFFFF]
-- positions
#guard (match readAll sample [5, 9] with | .ok (_, r) => r.bitPos == 14 | _ => false)
#guard (match readAll sample [5, 9] with | .ok (_, r) => r.remaining == 26 | _ => false)
-- past the end
#guard isEof (bytes [0xFF]) [9]
#guard isEof (bytes [0xFF]) [4, 5]
#guard isEof .empty [1]
#guard isEof (bytes [1, 2, 3, 4]) [32, 1]
#guard values (bytes [1, 2, 3, 4]) [32] == some [0x01020304]
#guard (match (BitReader.ofByteArray (bytes [0xFF])).readBits 9 with
  | .error .eof => true | _ => false)
#guard (match (BitReader.ofByteArray .empty).readBit with | .error .eof => true | _ => false)
#guard (match readAll (bytes [1, 2]) [16] with
  | .ok (_, r) => r.atEnd && (match r.readBit with | .error .eof => true | _ => false)
  | _ => false)
#guard (match (BitReader.ofByteArray (bytes [0xFF])).readBits 33 with
  | .error (.param _) => true | _ => false)
-- a failed read leaves the reader where it was
#guard (match (BitReader.ofByteArray (bytes [0xFF])).readBits 5 with
  | .ok (_, r) => (match r.readBits 4 with | .error .eof => r.bitPos == 5 | _ => false)
  | _ => false)
-- readByte
#guard (match (BitReader.ofByteArray sample).readBits 4 with
  | .ok (_, r) => (match r.readByte with | .ok (b, _) => b == 0x53 | _ => false)
  | _ => false)

/-- Writes the (width, value) pairs in order and finishes. -/
def writeAll (items : List (Nat × UInt32)) : ByteArray :=
  (items.foldl (fun w (n, v) => w.writeBits n v) BitWriter.empty).finish

-- writing
#guard writeAll [(3, 5), (5, 0x1F)] == bytes [0xBF]
#guard writeAll [(1, 1)] == bytes [0x80]
#guard writeAll [] == .empty
#guard writeAll [(8, 0xAB)] == bytes [0xAB]
#guard writeAll [(4, 0xA), (32, 0x12345678)] == bytes [0xA1, 0x23, 0x45, 0x67, 0x80]
#guard writeAll [(32, 0xFFFFFFFF), (32, 0)] == bytes [255, 255, 255, 255, 0, 0, 0, 0]
#guard writeAll [(4, 0xFFFFFFF3)] == bytes [0x30]
#guard writeAll [(0, 0xFFFFFFFF)] == .empty
#guard ((BitWriter.empty.writeBit true).writeByte 0xFF).finish == bytes [0xFF, 0x80]
#guard (BitWriter.empty.writeBits 13 0).bitLen == 13

/-- A pseudo-random list of (width, value) pairs, the value fitting in the width. -/
def randomItems (count : Nat) : List (Nat × UInt32) := Id.run do
  let mut seed : UInt64 := 12345
  let mut items : Array (Nat × UInt32) := #[]
  for _ in [0:count] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let n := ((seed >>> 33) % 33).toNat
    let v := (seed >>> 8).toUInt32
    items := items.push (n, if n = 32 then v else v &&& ((1 <<< n.toUInt32) - 1))
  return items.toList

/-- Whether writing `items` and reading them back gives them again. -/
def roundtrips (items : List (Nat × UInt32)) : Bool :=
  match readAll (writeAll items) (items.map (·.1)) with
  | .ok (vs, r) => vs == items.map (·.2) && r.remaining < 8
  | .error _ => false

-- roundtrips
#guard roundtrips (randomItems 3000)
#guard roundtrips [(32, 0xDEADBEEF), (1, 1), (31, 0x7FFFFFFF), (7, 0x55)]
#guard (writeAll (randomItems 3000)).size ==
  ((randomItems 3000).foldl (fun a (n, _) => a + n) 0 + 7) / 8

end Bzip2.Test.BitIO
