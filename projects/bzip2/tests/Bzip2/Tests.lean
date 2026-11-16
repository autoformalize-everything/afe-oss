import Bzip2.Oracle

/-!
`lake test`: runs the oracle on the golden vectors in `tests/vectors`.

No vectors exist yet; the `bzip2/tests/golden` task adds them and the runner. Until then this
only checks that the oracle's API links.
-/

open Bzip2.Oracle

/-- Checks of `Bzip2.Oracle.Crc`. Entries 0, 1, 128, 255 are from `upstream/crctable.c`; if the C
file is reachable from the working directory, the whole table is compared with it. -/
def crcTests : IO Bool := do
  let mut ok := true
  let check (name : String) (b : Bool) : IO Bool := do
    unless b do IO.eprintln s!"FAIL: {name}"
    pure b
  ok := (← check "crc32 check value" (Crc.crc32 "123456789".toUTF8 == 0xFC891918)) && ok
  ok := (← check "crc32 empty" (Crc.crc32 .empty == 0)) && ok
  ok := (← check "crc32 slice" (Crc.crc32 "xx123456789yy".toUTF8 2 11 == 0xFC891918)) && ok
  ok := (← check "table size" (Crc.table.size == 256)) && ok
  ok := (← check "table entries"
    (Crc.table[0]! == 0 && Crc.table[1]! == 0x04c11db7 && Crc.table[128]! == 0x690ce0ee
      && Crc.table[255]! == 0xb1f740b4)) && ok
  ok := (← check "combine" (Crc.combine 0x80000001 0x10 == 0x00000013)) && ok
  for path in ["upstream/crctable.c", "projects/bzip2/upstream/crctable.c"] do
    if ← System.FilePath.pathExists path then
      let text ← IO.FS.readFile path
      let mut vals : Array UInt32 := #[]
      for w in text.split (fun c => c == ' ' || c == ',' || c == '\n') do
        if w.startsWith "0x" && w.endsWith "L" then
          let hex := (w.drop 2).dropEnd 1
          vals := vals.push (hex.toString.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87).toUInt32) 0)
      ok := (← check "table equals crctable.c" (vals == Crc.table)) && ok
      break
  pure ok

def main : IO UInt32 := do
  match decompress .empty with
  | .error _ => pure ()
  | .ok _ => pure ()
  unless ← crcTests do return 1
  IO.println "bzip2-tests: no golden vectors yet"
  return 0
