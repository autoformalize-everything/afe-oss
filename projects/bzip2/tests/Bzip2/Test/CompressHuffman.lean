import Bzip2.Oracle.Compress.Huffman

/-!
Tests for `Bzip2.Oracle.Compress.Huffman` against what the C code computes; building this module
runs them (the `#eval`s throw on a mismatch).

`tests/vectors/compress-huffman/*-b0.txt` are blocks compressed by the vendored libbz2 with a
debug print added (out of tree) at the end of table selection in `sendMTFValues`: the block's
symbols (`mtfv`), `alpha` = nInUse+2, `groups`, selectors, and per table the lengths and codes.
`mcl.txt` holds `BZ2_hbMakeCodeLengths(·, ·, n, 17)` calls, including inputs that need the
weight-scaling retry.
-/

open Bzip2.Oracle.Compress.Huffman

namespace Bzip2.Test.CompressHuffman

/-- The numbers on a vector line after its label. -/
def nums (l : String) : Array Nat :=
  ((l.splitOn " ").drop 1).filter (· ≠ "") |>.toArray.map String.toNat!

/-- The non-empty lines of a vector file. -/
def readLines (path : System.FilePath) : IO (Array String) := do
  return (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "") |>.toArray

/-- Checks one block file; returns an error message on mismatch. -/
def checkBlock (path : System.FilePath) : IO (Option String) := do
  let lines ← readLines path
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

/-- Runs every vector file; throws on the first mismatch. -/
def run : IO Unit := do
  let dir : System.FilePath := "tests/vectors/compress-huffman"
  let mut n := 0
  for e in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    if e.fileName == "mcl.txt" then
      let lines ← readLines e.path
      for k in [0:lines.size / 3] do
        n := n + 1
        if makeCodeLengths (nums lines[3 * k + 1]!) 17 != nums lines[3 * k + 2]! then
          throw (IO.userError s!"mcl case {k}: lengths differ")
    else if e.fileName.endsWith ".txt" then
      n := n + 1
      if let some m ← checkBlock e.path then
        throw (IO.userError m)
  if n == 0 then throw (IO.userError "no vectors found")

#eval run

end Bzip2.Test.CompressHuffman
