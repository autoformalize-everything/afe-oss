import Bzip2.Oracle
import Bzip2.Oracle.Compress.Huffman

/-!
`lake test`: runs the oracle on the golden vectors in `tests/vectors`.

No vectors exist yet; the `bzip2/tests/golden` task adds them and the runner. Until then this
only checks that the oracle's API links.
-/

/-!
Tests for `Bzip2.Oracle.Compress.Huffman` against what the C code computes.

`tests/vectors/huffman/b*-b0.txt` are blocks compressed by the vendored libbz2 with a debug
print added (out of tree) at the end of table selection in `sendMTFValues`: the block's symbols
(`mtfv`), `alpha` = nInUse+2, `groups`, selectors, and per table the lengths and codes.
`mcl.txt` holds `BZ2_hbMakeCodeLengths(·, ·, n, 17)` calls, including inputs that need the
weight-scaling retry.
-/

open Bzip2.Oracle.Compress.Huffman

namespace Bzip2.Tests.Huffman

def nums (l : String) : Array Nat :=
  ((l.splitOn " ").drop 1).filter (· ≠ "") |>.toArray.map String.toNat!

/-- Checks one block file; returns an error message on mismatch. -/
def checkBlock (path : System.FilePath) : IO (Option String) := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "") |>.toArray
  let alpha := (nums lines[0]!)[0]!
  let mtfv := (nums lines[1]!).map (·.toUInt16)
  let groups := (nums lines[2]!)[0]!
  let sel := nums lines[3]!
  let mut len : Array (Array Nat) := #[]
  let mut code : Array (Array Nat) := #[]
  for t in [0:groups] do
    len := len.push (nums lines[4 + 2 * t]!)
    code := code.push (nums lines[5 + 2 * t]!)
  let r := choose mtfv alpha
  if r.nGroups != groups then return some s!"{path}: nGroups {r.nGroups} ≠ {groups}"
  if r.selector != sel then return some s!"{path}: selectors differ"
  if r.len != len then return some s!"{path}: code lengths differ"
  if r.code != code then return some s!"{path}: codes differ"
  return none

def run : IO UInt32 := do
  let dir : System.FilePath := "tests/vectors/huffman"
  let mut bad := 0
  let mut n := 0
  for e in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    if e.fileName == "mcl.txt" then
      let lines := (← IO.FS.readFile e.path).splitOn "\n" |>.filter (· ≠ "") |>.toArray
      for k in [0:lines.size / 3] do
        n := n + 1
        if makeCodeLengths (nums lines[3 * k + 1]!) 17 != nums lines[3 * k + 2]! then
          IO.eprintln s!"mcl case {k}: lengths differ"
          bad := bad + 1
    else if e.fileName.endsWith ".txt" then
      n := n + 1
      if let some m ← checkBlock e.path then
        IO.eprintln m
        bad := bad + 1
  IO.println s!"huffman: {n - bad}/{n} vector files ok"
  return if bad == 0 then 0 else 1

end Bzip2.Tests.Huffman

open Bzip2.Oracle

def main : IO UInt32 := do
  match decompress .empty with
  | .error _ => pure ()
  | .ok _ => pure ()
  IO.println "bzip2-tests: no golden vectors yet"
  Bzip2.Tests.Huffman.run
