import Mathlib.Data.List.Basic

/-!
# bzip2: symbol map, move-to-front, RUNA/RUNB

The steps between the BWT output (the last column of the sorted rotations, a list of bytes) and
the symbols that are Huffman coded. Encoding follows `generateMTFValues` (and `makeMaps_e`) in
`upstream/compress.c` (lines 106-115, 120-231); decoding follows the "Now the MTF values" part of
`BZ2_decompress` in `upstream/decompress.c` (lines 355-493, the code the task calls
`getAndMoveToFrontDecode`).

## Alphabet

With `nInUse` the number of distinct byte values in the block, the symbols are `0 .. nInUse + 1`:

* `RUNA = 0` and `RUNB = 1` (`BZ_RUNA`, `BZ_RUNB`): digits 1 and 2 of a zero run;
* `i + 1` for `2 ≤ i + 1 ≤ nInUse`: the MTF index `i` (`1 ≤ i ≤ nInUse - 1`);
* `EOB = nInUse + 1`: end of block.

MTF index 0 never appears as a symbol: a repeat of the byte at the front is a zero run.

## Decoding failures

`decode` returns `none` exactly where the C code returns `BZ_DATA_ERROR` in this part
(`decompress.c`), and in one more case that is not a data error in C:

1. `nInUse = 0` (line 283): `used = []`.
2. A run digit (RUNA/RUNB) is read when `N ≥ 2 * 1024 * 1024`, `N` being the place value
   `2^k` of that digit, i.e. the run has more than 21 digits (line 392). The check is made
   before the digit is used, so it also rejects a 22-digit run that would otherwise end.
3. A run would push the block length beyond `nblockMAX = 100000 * level` (lines 410, 417; C
   checks each byte, which is the same as checking `length + run > nblockMAX`).
4. An MTF symbol is read when the block already has `nblockMAX` bytes (line 427).

Not modelled here, because they concern other parts: `origPtr` outside `0 .. nblock - 1`
(line 495, in `Bzip2.Spec.Bwt`/`Format`), Huffman decoding errors, running out of selectors.
The symbol list is what Huffman decoding yields, whose alphabet is `0 .. nInUse + 1`, so a
symbol `> EOB` cannot occur in C; `decode` returns `none` on it (unreachable case).
If the list has no `EOB`, C would be reading past the end of the input
(`BZ_UNEXPECTED_EOF`, not `BZ_DATA_ERROR`); `decode` returns `none` there too. Symbols after
the first `EOB` are ignored, as the decoder stops at `EOB`.
-/

namespace Bzip2.Spec

namespace MtfRle2

/-- `BZ_RUNA`. -/
def RUNA : Nat := 0
/-- `BZ_RUNB`. -/
def RUNB : Nat := 1

/-! ### Symbol map -/

/-- The byte values used in the block (`inUse` in the stream header, `s->inUse` in C). -/
def inUse (block : List UInt8) (b : UInt8) : Bool := decide (b ∈ block)

/-- The used byte values in increasing order: the initial MTF list (`makeMaps_e`,
`seqToUnseq`). -/
def used (block : List UInt8) : List UInt8 :=
  ((List.range 256).map UInt8.ofNat).filter (inUse block)

/-- `nInUse`. -/
def nInUse (block : List UInt8) : Nat := (used block).length

/-- The Huffman alphabet size, `nInUse + 2`. -/
def alphaSize (block : List UInt8) : Nat := nInUse block + 2

/-- `EOB = nInUse + 1`. -/
def eob (block : List UInt8) : Nat := nInUse block + 1

/-! ### Move-to-front -/

/-- MTF indices of `bs`, given the current list `order` (which must contain every byte of
`bs`): the position of the byte, which then moves to the front. -/
def mtfIndices (order : List UInt8) : List UInt8 → List Nat
  | [] => []
  | b :: bs => order.idxOf b :: mtfIndices (b :: order.erase b) bs

/-! ### The zero-run code -/

/-- A run of `n` zeros as `n` in bijective base 2, least significant digit first, RUNA = digit 1
and RUNB = digit 2 (`n = 0` gives no digits). The loop in `generateMTFValues`. -/
def runDigits (n : Nat) : List Nat :=
  if h : n = 0 then []
  else if n % 2 = 1 then RUNA :: runDigits ((n - 1) / 2)
  else RUNB :: runDigits ((n - 2) / 2)
termination_by n
decreasing_by all_goals omega

/-- Replace MTF indices by symbols, with `z` pending zeros (`zPend`). Index `i ≥ 1` becomes
the symbol `i + 1`. -/
def rle2Aux : Nat → List Nat → List Nat
  | z, [] => runDigits z
  | z, 0 :: is => rle2Aux (z + 1) is
  | z, (i + 1) :: is => runDigits z ++ (i + 2) :: rle2Aux 0 is

/-- The symbols of a block, `EOB` included (`generateMTFValues`). -/
def encode (block : List UInt8) : List Nat :=
  rle2Aux 0 (mtfIndices (used block) block) ++ [eob block]

/-! ### Decoding -/

/-- `nblockMAX`, the longest block for block size `level` (`100000 * s->blockSize100k`). -/
def maxBlock (level : Nat) : Nat := 100000 * level

/-- Place values of run digits must stay below this (`2*1024*1024`, decompress.c:392). -/
def runLimit : Nat := 2 * 1024 * 1024

/-- Append `es` copies of the front of `order` (`none` if that exceeds `limit`). -/
def flushRun (limit : Nat) (order : List UInt8) (acc : List UInt8) (es : Nat) :
    Option (List UInt8) :=
  if es = 0 then some acc
  else match order with
    | [] => none
    | u :: _ => if acc.length + es ≤ limit then some (acc ++ List.replicate es u) else none

/-- The decoding loop. `acc` is the block so far, `es`/`N` the value and next place value of
the run being read (`es = 0`, `N = 1` when none). `eobSym` is `EOB`. -/
def decodeAux (limit eobSym : Nat) (order : List UInt8) (acc : List UInt8) (es N : Nat) :
    List Nat → Option (List UInt8)
  | [] => none
  | s :: ss =>
    if s = RUNA ∨ s = RUNB then
      if N ≥ runLimit then none
      else decodeAux limit eobSym order acc (es + (s + 1) * N) (2 * N) ss
    else do
      let acc ← flushRun limit order acc es
      if s = eobSym then some acc
      else if limit ≤ acc.length then none
      else if h : s - 1 < order.length then
        let b := order[s - 1]
        decodeAux limit eobSym (b :: order.eraseIdx (s - 1)) (acc ++ [b]) 0 1 ss
      else none

/-- Decode symbols (up to `EOB`) to the block, for the used bytes `used` (increasing) and block
size `level`; `none` where the C library gives `BZ_DATA_ERROR` (see the module doc). -/
def decode (level : Nat) (used : List UInt8) (syms : List Nat) : Option (List UInt8) :=
  if used = [] then none
  else decodeAux (maxBlock level) (used.length + 1) used [] 0 1 syms

/-! ### Examples -/

/-- The symbols of a block of `n` copies of the byte `7` (one used byte, so `EOB = 2`;
the byte is first in the MTF list, so it is all zeros). -/
example : encode (List.replicate 1 7) = [0, 2] := by decide +kernel
example : encode (List.replicate 2 7) = [1, 2] := by decide +kernel
example : encode (List.replicate 3 7) = [0, 0, 2] := by decide +kernel
example : encode (List.replicate 4 7) = [1, 0, 2] := by decide +kernel
example : encode (List.replicate 5 7) = [0, 1, 2] := by decide +kernel
example : encode (List.replicate 6 7) = [1, 1, 2] := by decide +kernel

example : runDigits 1 = [RUNA] := by decide +kernel
example : runDigits 2 = [RUNB] := by decide +kernel
example : runDigits 3 = [RUNA, RUNA] := by decide +kernel
example : runDigits 4 = [RUNB, RUNA] := by decide +kernel
example : runDigits 5 = [RUNA, RUNB] := by decide +kernel
example : runDigits 6 = [RUNB, RUNB] := by decide +kernel

/-- Runs of 1 to 6 zeros decode back (one used byte, level 1). -/
example : ∀ n ∈ [1, 2, 3, 4, 5, 6],
    decode 1 [7] (runDigits n ++ [2]) = some (List.replicate n 7) := by decide +kernel

/-- "banana": used bytes a, b, n (alphabet 5, `EOB = 4`). MTF list starts `a b n`:
b → 1, a → 1, n → 2, a → 1, n → 1, a → 1; symbols are the indices plus one. -/
example : encode "banana".toUTF8.toList = [2, 2, 3, 2, 2, 2, 4] := by decide +kernel
example : decode 1 [97, 98, 110] [2, 2, 3, 2, 2, 2, 4] = some "banana".toUTF8.toList := by
  decide +kernel

/-- Failures: no used byte, no `EOB`, a 22-digit run, a run longer than the block. -/
example : decode 1 [] [1] = none := by decide +kernel
example : decode 1 [7] [0] = none := by decide +kernel
example : decode 1 [7] (List.replicate 22 RUNA ++ [2]) = none := by decide +kernel
example : decode 1 [7] (List.replicate 17 RUNB ++ [2]) = none := by decide +kernel

end MtfRle2

end Bzip2.Spec
