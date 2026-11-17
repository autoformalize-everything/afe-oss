import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# bzip2: Huffman code lengths, the assigned code, decoding

A table is one code length per symbol of the alphabet (`lens : List Nat`, `lens[i]` the length of
symbol `i`). In a stream every length is in `1 .. 20`: the decoder rejects any `curr` outside
that range while reading the lengths (`decompress.c:323-333`). The alphabet has
`alphaSize = nInUse + 2` symbols (`decompress.c:282-284`), at most `BZ_MAX_ALPHA_SIZE = 258`
(`bzlib_private.h:115`). The definitions are total on `List Nat`; the C correspondence below
concerns tables the stream can carry, and the properties requiring legal lengths say so.

## The assigned code (`huffman.c:152-165`)

`minLen`/`maxLen` are the least and greatest length (C starts them at 32 and 0, so an empty
table leaves those values; `decompress.c:337-344`). Codes are handed out by increasing length,
within a length by increasing symbol index, `vec` incrementing per symbol and doubling between
lengths (`huffman.c:160-164`). `code lens i` is the number `code[i]`; `codeword lens i` is a
low-bit representation of that integer in `lens[i]` bits, most significant bit first. When an
over-subscribed table assigns a value too large for its length, `codeword` truncates that value.
The C writer passes the full code to `bsW` (`compress.c:562-566`, `compress.c:583-587`), which
does not mask it to the stated length (`compress.c:73-77`); `codeword` does not model that writer
on such tables.

## Decoding (`huffman.c:170-200`; `decompress.c:74-102`)

The decoder checks the length range but not whether the code is complete or feasible
(`decompress.c:323-352`). It builds from the table alone `perm` (symbols by increasing length
then index), `limit[n]` and `base[n]`
(for `minLen ≤ n ≤ maxLen`, `limit[n]` is the last code value of length `n` *as the decoder
counts it*, `base[n]` the offset into `perm`), and reads: `zn = minLen` bits as `zvec`, then,
while `zvec > limit[zn]`, one more bit (`zn++`, `zvec = 2·zvec + bit`). `limit` is 0 outside
`minLen .. maxLen` (`huffman.c:180-199`). The symbol is `perm[zvec - base[zn]]`
(`decompress.c:88-101`). The decoder tables and locals use `Int32` in C
(`bzlib_private.h:406-409`, `decompress.c:130-137`); for stream
lengths the table arithmetic stays below `258 · 2^20`, so `Int` models it. Bits are taken MSB
first (`decompress.c:43-51`).

Outcomes of `decodeSym`, including incomplete and over-subscribed stream tables:

* `sym s rest`: the symbol and the remaining bits.
* `dataError` (`BZ_DATA_ERROR`) when
  1. `zn > 20` is reached: the check is made at the top of the loop, i.e. after the 21st bit
     has been read (`decompress.c:88-96`). If the input ends right at 20 bits after an unmatched
     prefix, the outcome is `needMoreInput`;
  2. `zvec - base[zn]` is negative or `≥ 258`. For `zn ≤ maxLen` this cannot happen (by
     induction, `base[zn] ≤ zvec ≤ limit[zn]` gives an index below the number of symbols
     with length `≤ zn`; this is an argument made here, not a mechanised proof); for
     `maxLen < zn ≤ 20` we have `limit[zn] = 0` and `base[zn] = alphaSize`, so the loop breaks only
     with `zvec = 0` and the index is `-alphaSize < 0`: an error. (Reaching `zn > maxLen` with
     `zvec = 0` needs `zvec = 0` already at `minLen`, which matches `limit[minLen] ≥ 0`, so in
     practice an incomplete table ends in case 1 or `needMoreInput`; also argued, not proven.)
* `needMoreInput`: the bits run out before a symbol is complete (`GET_BITS` saves the state and
  returns `BZ_OK`; `decompress.c:43-65`).
* `staleEntry`: the index is in `[alphaSize, 258)` and C would read a `perm` entry the
  table did not set (`huffman.c:180-183`, `decompress.c:98-101`). By the argument in 2 this does
  not occur for stream tables.

Over-subscribed tables (Kraft sum > 1) are accepted by the decoder: at some length `limit[n]`
exceeds the codes that fit in `n` bits, so some assigned codes are never decoded. Incomplete
tables (Kraft sum < 1) decode the assigned codewords correctly and need more input or fail with
`BZ_DATA_ERROR` on unassigned prefixes as above. Out of scope here: selectors and group
switching (`groupPos`/`groupNo`), which belong to the stream format.
-/

namespace Bzip2.Spec

namespace Huffman

/-- A code length table: `lens[i]` is the length of symbol `i`. -/
abbrev Lens := List Nat

/-- Smallest length (`minLen`; 32 on the empty table). -/
def minLen (lens : Lens) : Nat := lens.foldl min 32
/-- Greatest length (`maxLen`; 0 on the empty table). -/
def maxLen (lens : Lens) : Nat := lens.foldl max 0
/-- Number of symbols of length `n`. -/
def cnt (lens : Lens) (n : Nat) : Nat := lens.count n

/-! ### The assigned code -/

/-- Value of `vec` on entering length `minLen + k` in `BZ2_hbAssignCodes`. -/
def startAt (lens : Lens) : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * (startAt lens k + cnt lens (minLen lens + k))

/-- `code[i]`: the first value of its length, plus the number of earlier symbols of that length. -/
def code (lens : Lens) (i : Nat) : Nat :=
  let l := lens.getD i 0
  startAt lens (l - minLen lens) + ((lens.take i).count l)

/-- The low `lens[i]` bits of the assigned code, most significant first. -/
def codeword (lens : Lens) (i : Nat) : List Bool :=
  (List.range (lens.getD i 0)).reverse.map (fun k => (code lens i).testBit k)

/-! ### The decoder tables -/

/-- `perm`: symbols ordered by length, then index. -/
def perm (lens : Lens) : List Nat :=
  (List.range' (minLen lens) (maxLen lens + 1 - minLen lens)).flatMap fun l =>
    (List.range lens.length).filter fun j => lens.getD j 0 == l

/-- `vec` after adding the symbols of length `minLen + k` (`limit = vec - 1`). -/
def vecAt (lens : Lens) : Nat → Nat
  | 0 => cnt lens (minLen lens)
  | k + 1 => 2 * vecAt lens k + cnt lens (minLen lens + k + 1)

/-- `limit[n]`. -/
def limit (lens : Lens) (n : Nat) : Int :=
  if minLen lens ≤ n ∧ n ≤ maxLen lens then (vecAt lens (n - minLen lens) : Int) - 1 else 0

/-- `base[n]` (`n < 23`): `#{lengths < n}` before the fix-up, which `minLen < n ≤ maxLen`
replaces by `2 (limit[n-1] + 1) - #{lengths < n}`. -/
def base (lens : Lens) (n : Nat) : Int :=
  let below : Int := (lens.countP (· < n) : Nat)
  if minLen lens < n ∧ n ≤ maxLen lens then 2 * (limit lens (n - 1) + 1) - below else below

/-! ### Decoding -/

/-- Result of reading one symbol. -/
inductive Result where
  | sym (s : Nat) (rest : List Bool)
  | dataError
  | needMoreInput
  | staleEntry
  deriving DecidableEq, Repr

/-- The loop of `GET_MTF_VAL` from `zn`, `zvec`; `fuel` bounds the iterations. -/
def loop (lens : Lens) : Nat → Nat → Nat → List Bool → Result
  | 0, _, _, _ => .dataError
  | fuel + 1, zn, zvec, bits =>
    if zn > 20 then .dataError
    else if (zvec : Int) ≤ limit lens zn then
      let idx := (zvec : Int) - base lens zn
      if idx < 0 ∨ idx ≥ 258 then .dataError
      else match (perm lens)[idx.toNat]? with
        | some s => .sym s bits
        | none => .staleEntry
    else match bits with
      | [] => .needMoreInput
      | b :: r => loop lens fuel (zn + 1) (2 * zvec + if b then 1 else 0) r

/-- Decode one symbol from the head of `bits`, as `GET_MTF_VAL` does with the tables
`BZ2_hbCreateDecodeTables` builds from `lens`. -/
def decodeSym (lens : Lens) (bits : List Bool) : Result :=
  let zn := minLen lens
  if bits.length < zn then .needMoreInput
  else
    let zvec := (bits.take zn).foldl (fun a b => 2 * a + if b then 1 else 0) 0
    loop lens 23 zn zvec (bits.drop zn)

/-! ### Correctness for complete tables -/

/-- Lengths are legal in a stream: `1 .. 20`. -/
def Legal (lens : Lens) : Prop := ∀ l ∈ lens, 1 ≤ l ∧ l ≤ 20

/-- Complete (Kraft sum exactly 1; for legal lengths this makes the code prefix-free and
leaves no unassigned bit string). -/
def Complete (lens : Lens) : Prop :=
  (lens.map fun l => 2 ^ (20 - l)).sum = 2 ^ 20

instance (lens : Lens) : Decidable (Complete lens) := by unfold Complete; infer_instance

/-- The statement for `bzip2/proofs/huffman`: on a legal, complete stream-sized table, decoding
the assigned codeword of any symbol, followed by anything, yields that symbol and leaves the
rest. The alphabet bound is necessary because `GET_MTF_VAL` rejects indices at least 258
(`decompress.c:98-100`), even for a complete table with more symbols. -/
def DecodeAssigned (lens : Lens) : Prop :=
  Legal lens → lens.length ≤ 258 → Complete lens → ∀ i < lens.length, ∀ rest : List Bool,
    decodeSym lens (codeword lens i ++ rest) = .sym i rest

/-! ### Examples -/

/-- Complete: lengths `1, 2, 3, 3` give codes `0, 10, 110, 111`. -/
example : (List.range 4).map (codeword [1, 2, 3, 3]) =
    [[false], [true, false], [true, true, false], [true, true, true]] := by decide
example : Complete [1, 2, 3, 3] := by decide
example : decodeSym [1, 2, 3, 3] [true, true, false, true] = .sym 2 [true] := by decide
example : decodeSym [1, 2, 3, 3] [true, true] = .needMoreInput := by decide
example : (List.range 4).all fun i => [[], [true], [false, true]].all fun rest =>
    decodeSym [1, 2, 3, 3] (codeword [1, 2, 3, 3] i ++ rest) == .sym i rest := by decide

/-- Incomplete (Kraft sum 3/4): lengths `2, 2, 2` give codes `00, 01, 10`; `11` is unassigned. -/
example : (List.range 3).map (codeword [2, 2, 2]) =
    [[false, false], [false, true], [true, false]] := by decide
example : ¬ Complete [2, 2, 2] := by decide
example : decodeSym [2, 2, 2] [true, false, true] = .sym 2 [true] := by decide
/-- `11` matches nothing: the decoder keeps reading and needs more input … -/
example : decodeSym [2, 2, 2] [true, true] = .needMoreInput := by decide
/-- … until `zn > 20` after the 21st bit (all ones never fit) … -/
example : decodeSym [2, 2, 2] (List.replicate 20 true) = .needMoreInput := by decide
example : decodeSym [2, 2, 2] (List.replicate 21 true) = .dataError := by decide
/-- A third bit: `110` still matches nothing at length 3 (`limit[3] = 0`, `zvec = 6`). -/
example : decodeSym [2, 2, 2] [true, true, false] = .needMoreInput := by decide

/-- Over-subscribed (Kraft sum 3/2): lengths `1, 1, 1`. The decoder accepts the table; with
`limit[1] = 2` every single bit stops at length 1, so symbol 2 (code value 2, which does not fit
in one bit) is never decoded and `codeword` for it is the low bit `0`, the same as symbol 0's. -/
example : ¬ Complete [1, 1, 1] := by decide
example : (List.range 3).map (codeword [1, 1, 1]) = [[false], [true], [false]] := by decide
example : decodeSym [1, 1, 1] [false, true] = .sym 0 [true] := by decide
example : decodeSym [1, 1, 1] [true, false] = .sym 1 [false] := by decide
example : codeword [1, 1, 1] 2 = codeword [1, 1, 1] 0 := by decide

end Huffman

end Bzip2.Spec
