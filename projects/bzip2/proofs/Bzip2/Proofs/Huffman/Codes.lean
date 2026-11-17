import Bzip2.Oracle.Compress.Huffman
import Bzip2.Spec.Huffman
import Bzip2.Proofs.Huffman.Loops
import Bzip2.Proofs.Huffman.DecodeTables
import Bzip2.Proofs.Huffman.Canonical

/-!
# Huffman proofs: the compressor assigns the spec's codes

`Oracle.Compress.Huffman.assignCodes` is `BZ2_hbAssignCodes` (`huffman.c:152-166`): codes by
increasing length, within a length by increasing symbol, `vec` incremented per symbol and doubled
between lengths. `assignCodes_eq_spec` says it computes `Spec.Huffman.code` of the lengths when it
is given the least and greatest length, as `sendMTFValues` gives it (`compress.c:488-492`), so
the codes the compressor writes (`compress.c:562-566`) are the spec's `codeword`s.

The loops are folds over `List.range'` (`Loops`); the invariant after the first `k` lengths is that
`vec` is the spec's `startAt k` and the codes of the symbols of those lengths are set.
-/

namespace Bzip2.Proofs.Huffman.Codes

open Bzip2.Oracle.Compress.Huffman Bzip2.Proofs.Huffman.Loops Bzip2.Proofs.Huffman.Canonical
  Bzip2.Proofs.Huffman.DecodeTables

/-- One symbol of the inner loop of `assignCodes` for length `n`. -/
def assignStep (length : Array Nat) (n : Nat) (b : Array Nat × Nat) (i : Nat) :
    Array Nat × Nat :=
  if (length[i]! == n) = true then (b.1.set! i b.2, b.2 + 1) else b

/-- The loops of `assignCodes`: the codes and `vec` after the lengths `minLen .. maxLen`. -/
def assignLoop (length : Array Nat) (minLen maxLen : Nat) : Array Nat × Nat :=
  (List.range' minLen (maxLen + 1 - minLen)).foldl (fun b n =>
    let r := (List.range' 0 length.size).foldl (assignStep length n) b
    (r.1, r.2 <<< 1)) (Array.replicate length.size 0, 0)

theorem assignCodes_eq_loop (length : Array Nat) (minLen maxLen : Nat) :
    assignCodes length minLen maxLen = (assignLoop length minLen maxLen).1 := by
  unfold assignCodes
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

/-- The inner loop over the symbols below `J`, for length `n`: `vec` counts the symbols of length
`n` seen, and each of them has its code set. -/
theorem assignInner (length : Array Nat) (n : Nat) (code₀ : Array Nat) (vec₀ : Nat)
    (hsz : code₀.size = length.size) :
    ∀ J, J ≤ length.size →
      ((List.range' 0 J).foldl (assignStep length n) (code₀, vec₀)).1.size = length.size ∧
      ((List.range' 0 J).foldl (assignStep length n) (code₀, vec₀)).2 =
        vec₀ + ((List.range J).filter (fun j => length[j]! == n)).length ∧
      ∀ i, ((List.range' 0 J).foldl (assignStep length n) (code₀, vec₀)).1[i]! =
        if i < J ∧ length[i]! = n then
          vec₀ + ((List.range i).filter (fun j => length[j]! == n)).length
        else code₀[i]! := by
  intro J
  induction J with
  | zero =>
    intro _
    refine ⟨hsz, by simp, fun i => ?_⟩
    simp
  | succ J ih =>
    intro hJ
    obtain ⟨hsz', hvec, hget⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, List.range_succ,
      List.filter_append, List.length_append]
    set b := (List.range' 0 J).foldl (assignStep length n) (code₀, vec₀) with hb
    have hJ0 : 0 + 1 * J = J := by omega
    rw [hJ0]
    unfold assignStep
    by_cases hj : (length[J]! == n) = true
    · have hj' : length[J]! = n := by simpa using hj
      simp only [hj, ↓reduceIte, List.filter_cons_of_pos, List.filter_nil, List.length_singleton]
      refine ⟨by rw [Array.size_set!, hsz'], by rw [hvec]; omega, fun i => ?_⟩
      rw [getElem!_set!, hsz']
      by_cases hi : J = i
      · subst hi
        rw [ite_of_true ⟨rfl, by omega⟩, ite_of_true ⟨by omega, hj'⟩, hvec]
      · rw [ite_of_false (fun h => hi h.1), hget i]
        by_cases h : i < J ∧ length[i]! = n
        · rw [ite_of_true h, ite_of_true ⟨by omega, h.2⟩]
        · have h' : ¬ (i < J + 1 ∧ length[i]! = n) := by
            rintro ⟨h1, h2⟩
            exact h ⟨by omega, h2⟩
          rw [ite_of_false h, ite_of_false h']
    · have hj' : ¬ length[J]! = n := by simpa using hj
      have hf : (List.filter (fun j => length[j]! == n) [J]) = [] := by
        simp only [List.filter_cons, hj, Bool.false_eq_true, ↓reduceIte, List.filter_nil]
      simp only [hj, Bool.false_eq_true, ↓reduceIte, hf, List.length_nil, Nat.add_zero]
      refine ⟨hsz', hvec, fun i => ?_⟩
      rw [hget i]
      by_cases h : i < J ∧ length[i]! = n
      · rw [ite_of_true h, ite_of_true ⟨by omega, h.2⟩]
      · have h' : ¬ (i < J + 1 ∧ length[i]! = n) := by
          rintro ⟨h1, h2⟩
          have : i = J ∨ i < J := by omega
          rcases this with rfl | h3
          · exact hj' h2
          · exact h ⟨h3, h2⟩
        rw [ite_of_false h, ite_of_false h']

theorem getElem!_eq_getD (length : Array Nat) (j : Nat) :
    length[j]! = length.toList.getD j 0 := by
  by_cases h : j < length.size
  · rw [getElem!_pos length j h]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [getElem!_neg length j h]
    simp [List.getD_eq_getElem?_getD, h]

/-- After the first `k` lengths from `minLen` on, `vec` is `startAt k`, and the symbols of those
lengths have the spec's codes (`huffman.c:160-165`). -/
theorem assignOuter (length : Array Nat) (k : Nat) :
    ((List.range' (Spec.Huffman.minLen length.toList) k).foldl (fun b n =>
      let r := (List.range' 0 length.size).foldl (assignStep length n) b
      (r.1, r.2 <<< 1)) (Array.replicate length.size 0, 0)).1.size = length.size ∧
    ((List.range' (Spec.Huffman.minLen length.toList) k).foldl (fun b n =>
      let r := (List.range' 0 length.size).foldl (assignStep length n) b
      (r.1, r.2 <<< 1)) (Array.replicate length.size 0, 0)).2 =
        Spec.Huffman.startAt length.toList k ∧
    ∀ i, ((List.range' (Spec.Huffman.minLen length.toList) k).foldl (fun b n =>
      let r := (List.range' 0 length.size).foldl (assignStep length n) b
      (r.1, r.2 <<< 1)) (Array.replicate length.size 0, 0)).1[i]! =
        if i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
            length[i]! < Spec.Huffman.minLen length.toList + k then
          Spec.Huffman.code length.toList i else 0 := by
  induction k with
  | zero =>
    refine ⟨by simp, by simp [Spec.Huffman.startAt], fun i => ?_⟩
    have hnot : ¬ (i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
        length[i]! < Spec.Huffman.minLen length.toList + 0) := by omega
    simp only [List.range'_zero, List.foldl_nil, getElem!_replicate, hnot, ↓reduceIte]
    by_cases h : i < length.size <;> simp [h]
  | succ k ih =>
    obtain ⟨hsz, hvec, hget⟩ := ih
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set b := (List.range' (Spec.Huffman.minLen length.toList) k).foldl (fun b n =>
      let r := (List.range' 0 length.size).foldl (assignStep length n) b
      (r.1, r.2 <<< 1)) (Array.replicate length.size 0, 0) with hb
    rw [Nat.one_mul]
    obtain ⟨isz, ivec, iget⟩ := assignInner length (Spec.Huffman.minLen length.toList + k)
      b.1 b.2 hsz length.size (Nat.le_refl _)
    set inner := (List.range' 0 length.size).foldl
      (assignStep length (Spec.Huffman.minLen length.toList + k)) b with hinner
    have hcount : ((List.range length.size).filter
        (fun j => length[j]! == Spec.Huffman.minLen length.toList + k)).length =
          length.toList.count (Spec.Huffman.minLen length.toList + k) := by
      have := length_filter_range_getD length.toList (Spec.Huffman.minLen length.toList + k)
        length.toList.length (Nat.le_refl _)
      rw [List.take_length, Array.length_toList] at this
      simp only [getElem!_eq_getD]
      exact this
    refine ⟨isz, ?_, fun i => ?_⟩
    · show inner.2 <<< 1 = Spec.Huffman.startAt length.toList (k + 1)
      rw [ivec, hvec, hcount, Nat.shiftLeft_eq, Nat.pow_one, Spec.Huffman.startAt,
        Spec.Huffman.cnt]
      omega
    · show inner.1[i]! = _
      rw [iget i, hget i]
      by_cases h : i < length.size ∧ length[i]! = Spec.Huffman.minLen length.toList + k
      · obtain ⟨hi1, hi2⟩ := h
        rw [ite_of_true ⟨hi1, hi2⟩,
          ite_of_true ⟨hi1, by omega, by omega⟩, hvec]
        unfold Spec.Huffman.code
        have hg : length.toList.getD i 0 = length[i]! := (getElem!_eq_getD length i).symm
        rw [hg, hi2]
        have hcnt := length_filter_range_getD length.toList
          (Spec.Huffman.minLen length.toList + k) i (by rw [Array.length_toList]; omega)
        simp only [getElem!_eq_getD] at hcnt ⊢
        rw [hcnt]
        congr 2
        omega
      · have h' : ¬ (i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
            length[i]! < Spec.Huffman.minLen length.toList + (k + 1)) ∨
            (i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
              length[i]! < Spec.Huffman.minLen length.toList + k) := by
          by_cases h2 : i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
              length[i]! < Spec.Huffman.minLen length.toList + k
          · exact Or.inr h2
          · left
            rintro ⟨h1, h3, h4⟩
            exact h ⟨h1, by omega⟩
        rw [ite_of_false h]
        by_cases h2 : i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
            length[i]! < Spec.Huffman.minLen length.toList + k
        · rw [ite_of_true h2, ite_of_true ⟨h2.1, h2.2.1, by omega⟩]
        · have h3 : ¬ (i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
              length[i]! < Spec.Huffman.minLen length.toList + (k + 1)) := by
            rintro ⟨h1, h4, h5⟩
            exact h2 ⟨h1, h4, by omega⟩
          rw [ite_of_false h2, ite_of_false h3]

/-- The codes `assignCodes` computes from the lengths, with the least and greatest length as
`sendMTFValues` passes them (`compress.c:488-492`), are the spec's `code`s. -/
theorem assignCodes_eq_spec (length : Array Nat) :
    (assignCodes length (length.foldl min 32) (length.foldl max 0)).toList =
      (List.range length.size).map (Spec.Huffman.code length.toList) := by
  have hmin : length.foldl min 32 = Spec.Huffman.minLen length.toList := by
    unfold Spec.Huffman.minLen
    rw [Array.foldl_toList]
  have hmax : length.foldl max 0 = Spec.Huffman.maxLen length.toList := by
    unfold Spec.Huffman.maxLen
    rw [Array.foldl_toList]
  rw [assignCodes_eq_loop, hmin, hmax]
  unfold assignLoop
  obtain ⟨hsz, _, hget⟩ := assignOuter length
    (Spec.Huffman.maxLen length.toList + 1 - Spec.Huffman.minLen length.toList)
  apply List.ext_getElem
  · simp [hsz]
  · intro i h1 h2
    have hi : i < length.size := by simpa using h2
    have hmem : length.toList.getD i 0 ∈ length.toList := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
      exact List.getElem_mem _
    have hlo := (foldl_min_le length.toList 32).2.1 _ hmem
    have hhi := (le_foldl_max length.toList 0).2.1 _ hmem
    have hg := getElem!_eq_getD length i
    have hmin' : Spec.Huffman.minLen length.toList = length.toList.foldl min 32 := rfl
    have hmax' : Spec.Huffman.maxLen length.toList = length.toList.foldl max 0 := rfl
    have hcond : i < length.size ∧ Spec.Huffman.minLen length.toList ≤ length[i]! ∧
        length[i]! < Spec.Huffman.minLen length.toList +
          (Spec.Huffman.maxLen length.toList + 1 - Spec.Huffman.minLen length.toList) := by
      refine ⟨hi, ?_, ?_⟩
      · rw [hg, hmin']; exact hlo
      · rw [hg]
        have := hlo
        have := hhi
        rw [hmin'] at *
        rw [hmax'] at *
        omega
    rw [List.getElem_map, List.getElem_range]
    have := hget i
    rw [ite_of_true hcond, getElem!_pos _ i (by rw [hsz]; exact hi)] at this
    simpa using this

end Bzip2.Proofs.Huffman.Codes
