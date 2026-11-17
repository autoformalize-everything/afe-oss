import Bzip2.Oracle.Decompress.Huffman

/-!
Tests for `Bzip2.Oracle.Decompress.Huffman` against what the vendored libbz2 computes; every
check is a `#guard`, so building this module runs them.

`tests/vectors/decompress-huffman/*.txt` are cases run through the C code by `huff.c` (see
`regenerate.sh` there): code lengths (or `minLen`, `limit`, `base` and `perm` given directly),
input bytes and a symbol count, followed by what C gave: the tables `BZ2_hbCreateDecodeTables`
builds, the symbols `GET_MTF_VAL` read, the bit position after the last of them, and how it
ended (`ok` after the requested count, `data` for `BZ_DATA_ERROR`, `eof` when the input ran
out). `real.txt` has the tables of three real streams, `incomplete.txt` and
`oversubscribed.txt` length sets whose Kraft sum is not 1, `failures.txt` the failures and
tables no lengths give. The files are embedded with `include_str`, so the guards read the text
the C driver wrote.
-/

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Huffman

namespace Bzip2.Test.DecompressHuffman

/-- The cases of a vector file's text: blocks of lines, each ended by an empty line. -/
def cases (text : String) : Array (Array String) :=
  (text.splitOn "\n\n").toArray.map (fun b => (b.splitOn "\n").toArray.filter (· ≠ ""))
    |>.filter (fun b => !b.isEmpty)

/-- The words after the label `key` on the case's line starting with `key`, if there is one. -/
def field (c : Array String) (key : String) : Option (Array String) :=
  (c.find? (fun l => (l.splitOn " ").head! == key)).map
    (fun l => ((l.splitOn " ").drop 1).filter (· ≠ "") |>.toArray)

/-- The integers on the line `key`, if there is one. -/
def ints (c : Array String) (key : String) : Option (Array Int) :=
  (field c key).map (·.map String.toInt!)

/-- A two-digit hex number. -/
def hexByte (s : String) : UInt8 :=
  s.foldl (fun a ch => a * 16 + (if ch.isDigit then ch.toNat - 48 else ch.toNat - 87).toUInt8) 0

/-- The input bytes of a case (none if it has no `bits` line). -/
def input (c : Array String) : ByteArray :=
  ⟨(field c "bits").getD #[] |>.map hexByte⟩

/-- The tables the case describes: built from its `len` line as `ofLengths` does, or its
`minLen`, `limit`, `base` and `perm` lines taken as they are. -/
def tablesOf (c : Array String) : Option Tables :=
  match ints c "len" with
  | some lens =>
    match ofLengths (lens.map (·.toNat.toUInt8)) with
    | .ok t => some t
    | .error _ => none
  | none =>
    match ints c "minLen", ints c "limit", ints c "base", ints c "perm" with
    | some m, some limit, some base, some perm =>
      let pad := Array.replicate (maxAlphaSize - perm.size) 0
      some { limit, base, perm := perm.map Int.toNat ++ pad, minLen := m[0]!.toNat }
    | _, _, _, _ => none

/-- Reads up to `n` symbols; the symbols, the bit position after the last, and `ok`, `eof`,
`data` or `other` for how it ended. -/
def decodeAll (t : Tables) (r : BitReader) (n : Nat) : Array Nat × Nat × String :=
  go t r n #[] r.bitPos
where
  /-- The loop of `decodeAll`, with the symbols read so far and the position after them. -/
  go (t : Tables) (r : BitReader) : Nat → Array Nat → Nat → Array Nat × Nat × String
    | 0, syms, pos => (syms, pos, "ok")
    | n + 1, syms, pos =>
      match decodeSym t r with
      | .ok (s, r') => go t r' n (syms.push s) r'.bitPos
      | .error .eof => (syms, pos, "eof")
      | .error (.data _) => (syms, pos, "data")
      | .error _ => (syms, pos, "other")

/-- Whether the oracle gives what the C driver wrote for the case: the tables (when built from
lengths) and the symbols, the position and the ending. -/
def agrees (c : Array String) : Bool :=
  match tablesOf c with
  | none => false
  | some t =>
    let tablesOk :=
      if (field c "len").isNone then true
      else
        ints c "limit" == some t.limit && ints c "base" == some t.base &&
        (ints c "perm").map (·.map Int.toNat) ==
          some (t.perm.extract 0 ((ints c "perm").getD #[]).size) &&
        (ints c "minLen").map (·.map Int.toNat) == some #[t.minLen]
    let (syms, pos, e) := decodeAll t (BitReader.ofByteArray (input c))
      ((field c "n").getD #[])[0]!.toNat!
    tablesOk && (ints c "syms").getD #[] == syms.map Nat.cast &&
      (field c "pos").getD #[] == #[toString pos] && (field c "end").getD #[] == #[e]

/-- Whether every case of a vector file's text is `agrees` and there are `count` of them. -/
def allAgree (text : String) (count : Nat) : Bool :=
  (cases text).size == count && (cases text).all agrees

#guard allAgree (include_str "../../vectors/decompress-huffman/real.txt") 17
#guard allAgree (include_str "../../vectors/decompress-huffman/incomplete.txt") 9
#guard allAgree (include_str "../../vectors/decompress-huffman/oversubscribed.txt") 7
#guard allAgree (include_str "../../vectors/decompress-huffman/failures.txt") 15

/-- How the case in `failures.txt` or `incomplete.txt` with this title ended, by C. -/
def endOf (text title : String) : Option String :=
  ((cases text).find? (fun c => c[0]! == "# " ++ title)).bind
    (fun c => (field c "end").map (·[0]!))

-- The failure classes the task names, each as the C code gave them (also checked in bulk above).
#guard endOf (include_str "../../vectors/decompress-huffman/incomplete.txt")
  "lengths 1 2 ... 20: 21 ones end in zn = 21 (data)" == some "data"
#guard endOf (include_str "../../vectors/decompress-huffman/failures.txt")
  "base[1] -257, zvec 1: index 258 (data)" == some "data"
#guard endOf (include_str "../../vectors/decompress-huffman/failures.txt")
  "input empty: not even minLen bits (eof)" == some "eof"

-- `ofLengths` refuses what `BZ2_decompress` refuses before building (`decompress.c:327`).
#guard match ofLengths #[1, 2, 0] with | .error (.data _) => true | _ => false
#guard match ofLengths #[1, 2, 21] with | .error (.data _) => true | _ => false
#guard match ofLengths #[] with | .error (.param _) => true | _ => false
#guard match ofLengths (Array.replicate 259 8) with | .error (.param _) => true | _ => false

end Bzip2.Test.DecompressHuffman
