import Bzip2.Oracle

/-!
`lake test`: runs the oracle on the golden vectors in `tests/vectors`.

No vectors exist yet; the `bzip2/tests/golden` task adds them and the runner. Until then this
only checks that the oracle's API links.
-/

-- Tests for `generateMtf` (expected values from `generateMTFValues` in `upstream/compress.c`, copied
-- into a small C driver built out of tree and run on the same BWT-output bytes).
open Bzip2.Oracle.Compress

namespace Bzip2.Tests.Mtf

private def check (name : String) (bwt : ByteArray) (syms : List Nat) (freq : List Nat)
    (nInUse : Nat) : IO Bool := do
  let r := generateMtf bwt (inUseOf bwt)
  let ok := r.syms.toList.map (·.toNat) == syms && r.freq.toList == freq && r.nInUse == nInUse
  unless ok do
    IO.eprintln s!"FAIL mtf {name}: got {repr r.syms} {repr r.freq} {r.nInUse}"
  return ok

private def rep (b : UInt8) (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n b)

def run : IO Bool := do
  let mut ok := true
  let s := "banana".toUTF8
  ok := ok && (← check "banana" s [2,2,3,2,2,2,4] [0,0,5,1,1] 3)
  ok := ok && (← check "annb0aa" (ByteArray.mk #[97,110,110,98,0,97,97]) [2,4,0,4,4,4,0,5]
    [2,0,1,0,4,1] 4)
  ok := ok && (← check "abracadabra" "abracadabra".toUTF8 [0,2,5,3,4,2,5,2,5,5,3,6] [1,0,3,2,1,4,1] 5)
  -- runs of 1..7 of the front byte, then a different byte
  let expRuns : List (List Nat) := [[0],[1],[0,0],[1,0],[0,1],[1,1],[0,0,0]]
  for k in [1:8] do
    let bwt := rep 120 k ++ rep 121 1
    let e := expRuns[k-1]!
    let f := (List.range 4).map fun i => (e ++ [2,3]).count i
    ok := ok && (← check s!"run {k}+y" bwt (e ++ [2,3]) f 2)
  -- only runs, one byte value
  for k in [1:7] do
    let e := expRuns[k-1]!
    ok := ok && (← check s!"run {k}" (rep 120 k) (e ++ [2]) ((List.range 3).map fun i => (e ++ [2]).count i) 1)
  ok := ok && (← check "run 1000" (rep 0 1000) [1,0,0,1,0,1,1,1,1,2] [3,6,1] 1)
  ok := ok && (← check "999 zeros then 1" (rep 0 999 ++ rep 1 1) [0,0,0,1,0,1,1,1,1,2,3] [4,5,1,1] 2)
  ok := ok && (← check "empty" .empty [1] [0,1] 0)
  return ok

end Bzip2.Tests.Mtf

open Bzip2.Oracle

def main : IO UInt32 := do
  match decompress .empty with
  | .error _ => pure ()
  | .ok _ => pure ()
  IO.println "bzip2-tests: no golden vectors yet"
  unless (← Bzip2.Tests.Mtf.run) do return 1
  IO.println "bzip2-tests: mtf ok"
  return 0
