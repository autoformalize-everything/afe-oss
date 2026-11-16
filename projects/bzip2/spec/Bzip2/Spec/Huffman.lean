import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# bzip2: Huffman code lengths, the assigned code, decoding

A table is one code length per symbol of the alphabet (`lens : List Nat`, `lens[i]` the length of
symbol `i`). In a stream every length is in `1 .. 20` (`decompress.c` lines 337-347 reject any
`curr` outside that while reading the delta-coded lengths: `RETURN(BZ_DATA_ERROR)`), and the
alphabet has `alphaSize = nInUse + 2` symbols, at most `BZ_MAX_ALPHA_SIZE = 258`. This module
does not assume either; the definitions are total on every `List Nat`, and the properties below
that need `1 ≤ len ≤ 20` say so.

## The assigned code (`BZ2_hbAssignCodes`, `upstream/huffman.c` lines 152-163)

`minLen`/`maxLen` are the least and greatest length (C: initial 32 and 0, so on an empty table
`32` and `0`, `decompress.c` lines 359-364). Codes are handed out by increasing length, within a
length by increasing symbol index, `vec` incrementing per symbol and doubling between lengths.
`code lens i` is the number `code[i]`; `codeword lens i` is its `lens[i]` low bits, most
significant bit first, i.e. the bits the encoder sends (`BZ2_hbAssignCodes` feeds `bsW(s, len,
code)` in `compress.c`). On an over-subscribed table `code` can need more than `lens[i]` bits;
`codeword` then keeps only the low ones, as `bsW` does.

## Decoding (`BZ2_hbCreateDecodeTables`, huffman.c 170-203; `GET_MTF_VAL`, decompress.c 74-102)

The decoder never checks that the lengths form a complete or even a feasible code. It builds,
from the table alone, `perm` (symbols by increasing length then index), `limit[n]` and `base[n]`
(for `minLen ≤ n ≤ maxLen`, `limit[n]` is the last code value of length `n` *as the decoder
counts it*, `base[n]` the offset into `perm`), and reads: `zn = minLen` bits as `zvec`, then,
while `zvec > limit[zn]`, one more bit (`zn++`, `zvec = 2·zvec + bit`). `limit` is 0 outside
`minLen .. maxLen`. The symbol is `perm[zvec - base[zn]]`. All of this is `Int32` in C; the values
stay far below overflow (at most `258 · 2^20`), so `Int` models it. Bits are taken MSB first
(`GET_BITS` in `decompress.c`).

Outcomes of `decodeSym`, for **every** table:

* `sym s rest`: the symbol and the remaining bits.
* `dataError` (`BZ_DATA_ERROR`) when
  1. `zn > 20` is reached: the check is made at the top of the loop, i.e. after the 21st bit
     has been read, so if the input ends right at 20 bits the outcome is `needMoreInput`, not an
     error (this happens on incomplete tables whose prefix matches no code);
  2. `zvec - base[zn]` is negative or `≥ 258`. For `zn ≤ maxLen` this cannot happen (by
     induction, `base[zn] ≤ zvec ≤ limit[zn]` gives an index below the number of symbols
     with length `≤ zn`; this is an argument made here, not a mechanised proof); for
     `maxLen < zn ≤ 20` we have `limit[zn] = 0` and `base[zn] = alphaSize`, so the loop breaks only
     with `zvec = 0` and the index is `-alphaSize < 0`: an error. (Reaching `zn > maxLen` with
     `zvec = 0` needs `zvec = 0` already at `minLen`, which matches `limit[minLen] ≥ 0`, so in
     practice an incomplete table ends in case 1 or `needMoreInput`; also argued, not proven.)
* `needMoreInput`: the bits run out before a symbol is complete (`GET_BITS` returns `BZ_OK`
  with the state saved, `decompress.c` 43-65).
* `staleEntry`: the index is in `[alphaSize, 258)` and C would read a `perm` entry the
  table did not set (stale memory). By the argument in 2 this does not occur.

Over-subscribed tables (Kraft sum > 1) are accepted by the decoder: `limit[n]` then exceeds the
codes that fit in `n` bits, so some symbols (the later ones of the longest lengths) are never
decoded and the shorter ones capture the bits instead. Incomplete tables (Kraft sum < 1) decode
the assigned codewords correctly, and fail on the unassigned bit strings as above. Out of scope
here: selectors and group switching (`groupPos`/`groupNo`), which belong to the stream format.
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

/-- The bits sent for symbol `i`: the low `lens[i]` bits of `code`, most significant first. -/
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

/-- The statement for `bzip2/proofs/huffman`: on a legal, complete table decoding the assigned
codeword of any symbol, followed by anything, yields that symbol and leaves the rest. -/
def DecodeAssigned (lens : Lens) : Prop :=
  Legal lens → Complete lens → ∀ i < lens.length, ∀ rest : List Bool,
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
