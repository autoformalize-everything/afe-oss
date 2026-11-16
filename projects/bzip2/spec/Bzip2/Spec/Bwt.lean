import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort

/-!
# The Burrows–Wheeler transform of a block

bzip2 applies this to each block after RLE1 (`BZ2_blockSort` in `upstream/blocksort.c`,
inverse in `decompress.c`, `BZ_GET_FAST` in `bzlib_private.h`).

## Forward

The `n` cyclic rotations of the block `b` are sorted lexicographically as byte strings
(unsigned bytes), and the transform `bwt b` is the last column. `origPtr` is a position in
the sorted list at which the original block (rotation 0) sits. The C code finds it by scanning
the sorted suffix array for the entry `ptr[i] == 0` (`blocksort.c:1083-1088`), and the 24-bit
`origPtr` is written to the block header (`compress.c:650`).

## What is and is not determined

* The sorted *list of rotations* (as byte strings), and therefore `bwt b`, is fully determined,
  even when rotations are equal.
* If `b` is periodic (`b = u ^ k`, `k ≥ 2`), several rotations equal `b`, they are adjacent in
  the sorted list, and *every* position among them satisfies `IsOrigPtr b p`. The definition
  does not say which one bzip2's compressor picks. In C, the suffix sort breaks ties between equal
  rotations by an order that is an artifact of the algorithm (`blocksort.c`'s fallback/main
  sorts, with the block doubled and a work budget), and the first `i` with `ptr[i] == 0` is
  chosen. That exact choice is `oracle/compress/byte-exact`'s concern, not the spec's.
* Decoding is correct for every such position (`InverseCorrect`), because rotations at those
  positions are equal strings, and `decodeBwt` never inspects which one it was given beyond that.
* Note the decoder's `origPtr` check is only `0 ≤ origPtr < nblock` (`decompress.c:497`); a pair
  `(last column, origPtr)` that is not the transform of any block still decodes to *some* block
  (`decodeBwt` is total on valid inputs), it just does not satisfy `IsBwtPair`.

## Inverse

`decodeBwt` follows the decoder: `cftab` counts bytes smaller than `c`; `tt[cftab[L[i]]++] |= i<<8`
gives the vector `next` (the high 24 bits of `tt`), and the decoder walks
`tPos := tt[origPtr] >> 8`, then repeatedly outputs `tt[tPos] & 0xff = L[tPos]` and moves to
`tPos := tt[tPos] >> 8` (`decompress.c:565-572`, `BZ_GET_FAST`). The same inverse is also
specified declaratively as the block whose transform it is (`IsInverse`).
-/

namespace Bzip2.Spec.Bwt

/-- Lexicographic order on equal-or-different-length byte strings, unsigned bytes. -/
def key (l : List UInt8) : List ℕ := l.map UInt8.toNat

/-- `x ≤ y` lexicographically. Decidable. -/
def le (x y : List UInt8) : Prop := ¬ key y < key x

instance (x y : List UInt8) : Decidable (le x y) := by unfold le; infer_instance

/-- The `i`-th cyclic rotation: starts at byte `i`. -/
def rotation (b : List UInt8) (i : ℕ) : List UInt8 := b.rotate i

/-- The rotations of `b`, sorted lexicographically (equal rotations adjacent; their relative
order is immaterial since they are equal lists). -/
def sortedRotations (b : List UInt8) : List (List UInt8) :=
  ((List.range b.length).map (rotation b)).insertionSort le

/-- The transform: the last column of the sorted rotations. -/
def bwt (b : List UInt8) : List UInt8 :=
  (sortedRotations b).map fun r => r.getLastD 0

/-- `p` is a valid `origPtr` for `b`: the original block sits at position `p`.
For periodic blocks several `p` qualify. -/
def IsOrigPtr (b : List UInt8) (p : ℕ) : Prop :=
  p < b.length ∧ (sortedRotations b)[p]? = some b

instance (b : List UInt8) (p : ℕ) : Decidable (IsOrigPtr b p) := by
  unfold IsOrigPtr; infer_instance

/-! ### The inverse as the decoder computes it -/

/-- `cftab L c`: the number of bytes of `L` smaller than `c` (`decompress.c:507-509`). -/
def cftab (L : List UInt8) (c : UInt8) : ℕ := (L.filter (· < c)).length

/-- The slot that index `i` of the last column fills in `tt`:
`cftab[L[i]]` plus the number of earlier equal bytes (`decompress.c:566-569`). -/
def slot (L : List UInt8) (i : ℕ) : ℕ :=
  cftab L (L.getD i 0) + ((L.take i).filter (· == L.getD i 0)).length

/-- The high bits of `tt[r]`: the index `i` with `slot i = r`. -/
def next (L : List UInt8) (r : ℕ) : ℕ :=
  ((List.range L.length).find? (fun i => slot L i == r)).getD 0

/-- `n` steps of the walk of `BZ_GET_FAST`, starting from `tPos = t`. -/
def walk (L : List UInt8) : ℕ → ℕ → List UInt8
  | 0, _ => []
  | k + 1, t => L.getD t 0 :: walk L k (next L t)

/-- The decoder's inverse: start at `tPos = tt[origPtr] >> 8 = next origPtr`, produce `n` bytes. -/
def decodeBwt (L : List UInt8) (p : ℕ) : List UInt8 :=
  walk L L.length (next L p)

/-- The decoder's acceptance check on `origPtr` (`decompress.c:497`). -/
def ValidInput (L : List UInt8) (p : ℕ) : Prop := p < L.length

/-! ### The inverse as "the block whose transform this is" -/

/-- `b` is a block whose transform is `L` with `origPtr = p`. -/
def IsInverse (L : List UInt8) (p : ℕ) (b : List UInt8) : Prop :=
  bwt b = L ∧ IsOrigPtr b p

instance (L : List UInt8) (p : ℕ) (b : List UInt8) : Decidable (IsInverse L p b) := by
  unfold IsInverse; infer_instance

/-- `(L, p)` is the transform of some block. -/
def IsBwtPair (L : List UInt8) (p : ℕ) : Prop := ∃ b, IsInverse L p b

/-- The declarative inverse is unique (statement; proved in `bzip2/proofs/bwt`). -/
def InverseUnique : Prop :=
  ∀ L p b b', IsInverse L p b → IsInverse L p b' → b = b'

/-- The decoder undoes the forward transform for every `origPtr` that points at the block
(statement; proved in `bzip2/proofs/bwt`). -/
def InverseCorrect : Prop :=
  ∀ b p, IsOrigPtr b p → ValidInput (bwt b) p ∧ decodeBwt (bwt b) p = b

/-! ### Examples -/

private def s (x : String) : List UInt8 := x.toUTF8.toList

example : (sortedRotations (s "banana")).map (fun r => String.fromUTF8! ⟨r.toArray⟩) =
    ["abanan", "anaban", "ananab", "banana", "nabana", "nanaba"] := by decide +kernel

example : bwt (s "banana") = s "nnbaaa" := by decide +kernel
example : IsOrigPtr (s "banana") 3 := by decide +kernel
example : ¬ IsOrigPtr (s "banana") 2 := by decide +kernel
example : decodeBwt (s "nnbaaa") 3 = s "banana" := by decide +kernel

/-- Periodic block: `abab` has rotations `abab, baba, abab, baba`; sorted
`abab, abab, baba, baba`, so both 0 and 1 are valid `origPtr`s, and both decode correctly. -/
example : bwt (s "abab") = s "bbaa" := by decide +kernel
example : IsOrigPtr (s "abab") 0 ∧ IsOrigPtr (s "abab") 1 := by decide +kernel
example : ¬ IsOrigPtr (s "abab") 2 := by decide +kernel
example : decodeBwt (s "bbaa") 0 = s "abab" ∧ decodeBwt (s "bbaa") 1 = s "abab" := by
  decide +kernel
example : IsInverse (s "bbaa") 1 (s "abab") := by decide +kernel

end Bzip2.Spec.Bwt
