import Bzip2.Oracle

/-!
`lake test`: runs the oracle on the golden vectors in `tests/vectors`.

No vectors exist yet; the `bzip2/tests/golden` task adds them and the runner. Until then this
only checks that the oracle's API links.
-/

open Bzip2.Oracle

open Bzip2.Oracle.Compress in
def naiveBwt (b : ByteArray) : ByteArray × Nat := Id.run do
  let n := b.size
  let rot (s : Nat) : Array UInt8 := Array.ofFn (n := n) fun i => b.get! ((s + i.val) % n)
  let idx := (Array.range n).qsort fun x y =>
    let a := rot x; let c := rot y
    a.toList < c.toList || (a.toList == c.toList && x < y)
  let mut out := ByteArray.empty
  let mut o := 0
  let mut found := false
  for i in [0:n] do
    out := out.push (b.get! ((idx[i]! + n - 1) % n))
    if !found && (rot idx[i]!) == rot 0 then o := i; found := true
  return (out, o)

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def bwtTests : IO Bool := do
  let mut ok := true
  let mut s : UInt64 := 12345
  for t in [0:400] do
    s := lcg s
    let len := (s >>> 33).toNat % 40
    let alpha := 1 + t % 4
    let mut b := ByteArray.empty
    for _ in [0:len] do
      s := lcg s
      b := b.push (UInt8.ofNat ((s >>> 40).toNat % alpha + 250))
    let got := Bzip2.Oracle.Compress.bwt b
    let exp := naiveBwt b
    if got.1 != exp.1 || got.2 != exp.2 then
      IO.eprintln s!"bwt mismatch on {b.toList}: {got.1.toList},{got.2} vs {exp.1.toList},{exp.2}"
      ok := false
  -- banana
  let g := Bzip2.Oracle.Compress.bwt "banana".toUTF8
  if g.1 != "nnbaaa".toUTF8 || g.2 != 3 then
    IO.eprintln "bwt banana wrong"; ok := false
  -- big blocks
  let t0 ← IO.monoMsNow
  let r := Bzip2.Oracle.Compress.bwt (ByteArray.mk (Array.replicate 900000 (7 : UInt8)))
  if r.1.size != 900000 || r.2 != 0 then IO.eprintln "bwt run wrong"; ok := false
  let t1 ← IO.monoMsNow
  let mut b := ByteArray.empty
  for _ in [0:900000] do
    s := lcg s
    b := b.push (s >>> 56).toUInt8
  let r2 := Bzip2.Oracle.Compress.bwt b
  if r2.1.size != 900000 then ok := false
  let t2 ← IO.monoMsNow
  IO.println s!"bwt: run {t1 - t0} ms, random {t2 - t1} ms"
  if t1 - t0 > 10000 || t2 - t1 > 10000 then IO.eprintln "bwt too slow"; ok := false
  return ok

def main : IO UInt32 := do
  unless (← bwtTests) do return 1
  match decompress .empty with
  | .error _ => pure ()
  | .ok _ => pure ()
  IO.println "bzip2-tests: no golden vectors yet"
  return 0
