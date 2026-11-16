import Bzip2.Oracle


/-! Unit tests for `Bzip2.Oracle.BitIO`. `run` returns the number of failed checks. -/

namespace Bzip2.Tests.BitIO
open Bzip2.Oracle

def bytes (l : List Nat) : ByteArray := ⟨(l.map (·.toUInt8)).toArray⟩

def check (name : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"FAIL: {name}"
  return 1

/-- Reads the widths in order; `none` if any read fails. -/
def readAll (d : ByteArray) (ws : List Nat) : Option (List UInt32 × BitReader) :=
  ws.foldl (init := some ([], BitReader.ofByteArray d)) fun st w =>
    match st with
    | none => none
    | some (acc, r) => match r.readBits w with
      | .ok (v, r') => some (acc ++ [v], r')
      | .error _ => none

def run : IO Nat := do
  let mut bad := 0
  -- MSB first, within a byte
  let d := bytes [0xA5, 0x3C, 0xFF, 0x00, 0x81]
  bad := bad + (← check "bit order" (match (BitReader.ofByteArray d).readBit with
    | .ok (true, r) => match r.readBit with | .ok (false, _) => true | _ => false
    | _ => false))
  -- crossing byte boundaries
  bad := bad + (← check "cross 4+8+4" ((readAll d [4, 8, 4]).map (·.1) == some [0xA, 0x53, 0xC]))
  bad := bad + (← check "cross 12" ((readAll d [12]).map (·.1) == some [0xA53]))
  bad := bad + (← check "cross 3,13" ((readAll d [3, 13]).map (·.1) == some [5, 0x053C]))
  -- 32-bit reads
  bad := bad + (← check "32 aligned" ((readAll d [32]).map (·.1) == some [0xA53CFF00]))
  bad := bad + (← check "32 unaligned" ((readAll d [4, 32]).map (·.1) == some [0xA, 0x53CFF008]))
  bad := bad + (← check "32 all ones"
    ((readAll (bytes [255, 255, 255, 255, 255]) [3, 32]).map (·.1) == some [7, 0xFFFFFFFF]))
  bad := bad + (← check "0 bits" ((readAll d [0, 8]).map (·.1) == some [0, 0xA5]))
  -- position
  bad := bad + (← check "pos" ((readAll d [5, 9]).map (·.2.bitPos) == some 14))
  -- reading past the end
  let r0 := BitReader.ofByteArray (bytes [0xFF])
  bad := bad + (← check "eof 9" (match r0.readBits 9 with | .error .eof => true | _ => false))
  bad := bad + (← check "eof leaves reader" (match r0.readBits 9 with
    | .error _ => r0.bitPos == 0 | _ => false))
  bad := bad + (← check "eof empty bit" (match (BitReader.ofByteArray .empty).readBit with
    | .error .eof => true | _ => false))
  bad := bad + (← check "eof after exact" (match readAll (bytes [1, 2]) [16] with
    | some (_, r) => (match r.readBit with | .error .eof => true | _ => false) && r.atEnd
    | none => false))
  bad := bad + (← check "eof 33 bits of 4 bytes" (match (BitReader.ofByteArray (bytes [1,2,3,4])).readBits 32 with
    | .ok (v, r) => v == 0x01020304 && (match r.readBits 1 with | .error .eof => true | _ => false)
    | _ => false))
  bad := bad + (← check "n > 32" (match r0.readBits 33 with | .error (.param _) => true | _ => false))
  -- writer
  let w := (BitWriter.empty.writeBits 3 5).writeBits 5 0x1F
  bad := bad + (← check "write 3+5" (w.finish == bytes [0xBF]))
  bad := bad + (← check "pad" ((BitWriter.empty.writeBits 1 1).finish == bytes [0x80]))
  bad := bad + (← check "empty" (BitWriter.empty.finish == .empty))
  bad := bad + (← check "write32"
    (((BitWriter.empty.writeBits 4 0xA).writeBits 32 0x12345678).finish == bytes [0xA1, 0x23, 0x45, 0x67, 0x80]))
  bad := bad + (← check "masks high bits" ((BitWriter.empty.writeBits 4 0xFFFFFFF3).finish == bytes [0x30]))
  bad := bad + (← check "writeByte unaligned" (((BitWriter.empty.writeBit true).writeByte 0xFF).finish == bytes [0xFF, 0x80]))
  -- roundtrip with a pseudo-random sequence of widths and values
  let mut seed : UInt64 := 12345
  let mut items : Array (Nat × UInt32) := #[]
  for _ in [0:5000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let n := ((seed >>> 33) % 33).toNat
    let v := (seed >>> 8).toUInt32
    items := items.push (n, if n = 32 then v else v &&& ((1 <<< n.toUInt32) - 1))
  let mut w := BitWriter.empty
  for (n, v) in items do w := w.writeBits n v
  let total := items.foldl (fun a (n, _) => a + n) 0
  bad := bad + (← check "bitLen" (w.bitLen == total))
  let out := w.finish
  bad := bad + (← check "size" (out.size == (total + 7) / 8))
  let mut r := BitReader.ofByteArray out
  let mut ok := true
  for (n, v) in items do
    match r.readBits n with
    | .ok (x, r') => if x != v then ok := false
                     r := r'
    | .error _ => ok := false
  bad := bad + (← check "roundtrip" (ok && r.remaining < 8))
  return bad

end Bzip2.Tests.BitIO

/-!
`lake test`: unit tests of oracle parts, then the oracle on the golden vectors in `tests/vectors`.

No vectors exist yet; the `bzip2/tests/golden` task adds them and the runner. Until then this
only checks that the oracle's API links.
-/

open Bzip2.Oracle

def main : IO UInt32 := do
  match decompress .empty with
  | .error _ => pure ()
  | .ok _ => pure ()
  let bad ← Bzip2.Tests.BitIO.run
  if bad > 0 then
    IO.eprintln s!"bzip2-tests: {bad} BitIO test(s) failed"
    return 1
  IO.println "bzip2-tests: BitIO ok; no golden vectors yet"
  return 0
