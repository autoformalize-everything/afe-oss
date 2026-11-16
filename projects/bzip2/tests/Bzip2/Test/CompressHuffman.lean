import Bzip2.Oracle.Compress.Huffman

/-!
Tests for `Bzip2.Oracle.Compress.Huffman` against what the C code computes; every check is a
`#guard`, so building this module runs them.

`tests/vectors/compress-huffman/*-b0.txt` are blocks compressed by the vendored libbz2 with a
debug print added (out of tree) at the end of table selection in `sendMTFValues`: the block's
symbols (`mtfv`), `alpha` = nInUse+2, `groups`, selectors, and per table the lengths and codes.
`mcl.txt` holds `BZ2_hbMakeCodeLengths(·, ·, n, 17)` calls, including inputs that need the
weight-scaling retry. The files are embedded with `include_str`, so the guards read the same
text the C driver wrote.
-/

open Bzip2.Oracle.Compress.Huffman

namespace Bzip2.Test.CompressHuffman

/-- The numbers on a vector line after its label. -/
def nums (l : String) : Array Nat :=
  ((l.splitOn " ").drop 1).filter (· ≠ "") |>.toArray.map String.toNat!

/-- The non-empty lines of a vector file's text. -/
def lines (text : String) : Array String :=
  text.splitOn "\n" |>.filter (· ≠ "") |>.toArray

/-- What `choose` returns for the block in a `*-b0.txt` file's text. -/
def run (text : String) : Tables :=
  let l := lines text
  choose (nums l[1]!|>.map (·.toUInt16)) (nums l[0]!)[0]!

/-- The number of tables recorded in a `*-b0.txt` file's text. -/
def groups (text : String) : Nat := (nums (lines text)[2]!)[0]!

/-- The selectors recorded in a `*-b0.txt` file's text. -/
def selectors (text : String) : Array Nat := nums (lines text)[3]!

/-- The code lengths of every table recorded in a `*-b0.txt` file's text. -/
def lens (text : String) : Array (Array Nat) :=
  (Array.range (groups text)).map fun t => nums (lines text)[4 + 2 * t]!

/-- The codes of every table recorded in a `*-b0.txt` file's text. -/
def codes (text : String) : Array (Array Nat) :=
  (Array.range (groups text)).map fun t => nums (lines text)[5 + 2 * t]!

/-- Whether `choose` agrees with the C on tables, selectors, lengths and codes. -/
def agrees (text : String) : Bool :=
  let r := run text
  r.nGroups == groups text && r.selector == selectors text && r.len == lens text &&
    r.code == codes text

/-- Whether every `mcl` case of `mcl.txt`'s text (label, `f` counts, `l` lengths) agrees. -/
def mclAgrees (text : String) : Bool :=
  let l := lines text
  (Array.range (l.size / 3)).all fun k =>
    makeCodeLengths (nums l[3 * k + 1]!) 17 == nums l[3 * k + 2]!

-- Blocks of 18, 300, 900, 2000, 10000 and 60000 symbols and of text: 2 to 6 tables.
#guard agrees (include_str "../../vectors/compress-huffman/tiny-b0.txt")
#guard agrees (include_str "../../vectors/compress-huffman/s300-b0.txt")
#guard agrees (include_str "../../vectors/compress-huffman/s900-b0.txt")
#guard agrees (include_str "../../vectors/compress-huffman/s2000-b0.txt")
#guard agrees (include_str "../../vectors/compress-huffman/s10000-b0.txt")
#guard agrees (include_str "../../vectors/compress-huffman/s60000-b0.txt")
#guard agrees (include_str "../../vectors/compress-huffman/text-b0.txt")

-- `BZ2_hbMakeCodeLengths` calls, including ones that need the weight-scaling retry.
#guard mclAgrees (include_str "../../vectors/compress-huffman/mcl.txt")

end Bzip2.Test.CompressHuffman
