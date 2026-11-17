import Bzip2.Spec.Huffman
import Bzip2.Proofs.Huffman.DecodeTables

/-!
# Huffman proofs: where the decoder's loop can stop

On a legal table the decoder (`decompress.c:88-101`; `Spec.Huffman.loop`) reads one bit at a time
while `zvec > limit[zn]`. `Stop.index_lt` is the argument that the spec's doc sketches and does not
prove: whenever it stops, `minLen ≤ zn ≤ maxLen` and the index `zvec - base[zn]` is a position
inside `perm`, so the checks `idx < 0` and `idx ≥ 258` (`decompress.c:98-100`) never fire and
`perm` is never read where the tables did not set it (`Result.staleEntry` does not occur).

The only fact about `zvec` that the argument needs is `Inv`: it is a first read of `minLen` bits,
or at least `2 * (limit[zn - 1] + 1)`, which is what failing the test one bit shorter gives.
-/

namespace Bzip2.Proofs.Huffman.Stop

open Bzip2.Proofs.Huffman.DecodeTables Bzip2.Proofs.Huffman.Loops

/-- What the loop knows about the value `zvec` it has read after `zn` bits. -/
def Inv (lens : List Nat) (zn zvec : Nat) : Prop :=
  Spec.Huffman.minLen lens ≤ zn ∧
    (zn = Spec.Huffman.minLen lens ∨
      2 * (Spec.Huffman.limit lens (zn - 1) + 1) ≤ (zvec : Int))

/-- A bit read after failing the test keeps the invariant. -/
theorem Inv.step {lens : List Nat} {zn zvec : Nat} (h : Inv lens zn zvec)
    (hfail : ¬ (zvec : Int) ≤ Spec.Huffman.limit lens zn) (b : Bool) :
    Inv lens (zn + 1) (2 * zvec + if b then 1 else 0) := by
  refine ⟨by have := h.1; omega, Or.inr ?_⟩
  simp only [Nat.add_sub_cancel]
  cases b <;> simp <;> omega

theorem vecAt_pos (lens : List Nat) (hm : 1 ≤ Spec.Huffman.cnt lens (Spec.Huffman.minLen lens))
    (k : Nat) : 1 ≤ Spec.Huffman.vecAt lens k := by
  induction k with
  | zero => simpa [Spec.Huffman.vecAt] using hm
  | succ k ih => simp only [Spec.Huffman.vecAt]; omega

theorem countP_lt_min (lens : List Nat) (hall : ∀ x ∈ lens, Spec.Huffman.minLen lens ≤ x) :
    lens.countP (· < Spec.Huffman.minLen lens) = 0 := by
  rw [List.countP_eq_zero]
  intro x hx
  have := hall x hx
  simpa using this

theorem limit_of_mem (lens : List Nat) (n : Nat) (h1 : Spec.Huffman.minLen lens ≤ n)
    (h2 : n ≤ Spec.Huffman.maxLen lens) :
    Spec.Huffman.limit lens n =
      (Spec.Huffman.vecAt lens (n - Spec.Huffman.minLen lens) : Int) - 1 := by
  unfold Spec.Huffman.limit
  rw [ite_of_true ⟨h1, h2⟩]

theorem limit_of_not_mem (lens : List Nat) (n : Nat)
    (h : ¬ (Spec.Huffman.minLen lens ≤ n ∧ n ≤ Spec.Huffman.maxLen lens)) :
    Spec.Huffman.limit lens n = 0 := by
  unfold Spec.Huffman.limit
  rw [ite_of_false h]

theorem min_mem (lens : List Nat) (hne : lens ≠ []) (hlegal : ∀ x ∈ lens, 1 ≤ x ∧ x ≤ 20) :
    Spec.Huffman.minLen lens ∈ lens := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil lens hne
  obtain ⟨_, _, h3⟩ := foldl_min_le lens 32
  have hmin : Spec.Huffman.minLen lens = lens.foldl min 32 := rfl
  rw [hmin]
  rcases h3 with h | h
  · have := (foldl_min_le lens 32).2.1 x hx
    have := (hlegal x hx).2
    omega
  · exact h

/-- When the loop stops (`zvec ≤ limit[zn]` with `zn ≤ 20`), the length `zn` is a length of the
table and `idx = zvec - base[zn]` is a position in `perm`. -/
theorem index_lt (lens : List Nat) (hne : lens ≠ []) (hlegal : ∀ x ∈ lens, 1 ≤ x ∧ x ≤ 20)
    (zn zvec : Nat) (hinv : Inv lens zn zvec)
    (hstop : (zvec : Int) ≤ Spec.Huffman.limit lens zn) :
    zn ≤ Spec.Huffman.maxLen lens ∧
    0 ≤ (zvec : Int) - Spec.Huffman.base lens zn ∧
      (zvec : Int) - Spec.Huffman.base lens zn < (lens.length : Int) := by
  obtain ⟨hm1, hmM, hM20, hbounds⟩ := minLen_maxLen lens hne hlegal
  have hcnt : 1 ≤ Spec.Huffman.cnt lens (Spec.Huffman.minLen lens) :=
    List.count_pos_iff.mpr (min_mem lens hne hlegal)
  obtain ⟨hmzn, hcase⟩ := hinv
  have hznM : zn ≤ Spec.Huffman.maxLen lens := by
    by_contra hgt
    have hne' : zn ≠ Spec.Huffman.minLen lens := by omega
    have h2 := hcase.resolve_left hne'
    have hlim0 := limit_of_not_mem lens zn (by omega)
    have h3 : 1 ≤ Spec.Huffman.limit lens (zn - 1) + 1 := by
      by_cases h : Spec.Huffman.minLen lens ≤ zn - 1 ∧ zn - 1 ≤ Spec.Huffman.maxLen lens
      · rw [limit_of_mem lens (zn - 1) h.1 h.2]
        have := vecAt_pos lens hcnt (zn - 1 - Spec.Huffman.minLen lens)
        omega
      · rw [limit_of_not_mem lens (zn - 1) h]
        omega
    omega
  refine ⟨hznM, ?_⟩
  have hbelow := countP_lt_succ lens zn
  have hle : lens.countP (· < zn + 1) ≤ lens.length := List.countP_le_length
  by_cases hzm : zn = Spec.Huffman.minLen lens
  · -- the first read: `base[minLen]` counts the shorter symbols, of which there are none
    have h0 := countP_lt_min lens (fun x hx => (hbounds x hx).1)
    have hb : Spec.Huffman.base lens zn = 0 := by
      unfold Spec.Huffman.base
      rw [ite_of_false (by omega)]
      rw [hzm]
      simp [h0]
    have hl := limit_of_mem lens zn hmzn hznM
    have hv : Spec.Huffman.vecAt lens (zn - Spec.Huffman.minLen lens) =
        Spec.Huffman.cnt lens (Spec.Huffman.minLen lens) := by
      rw [hzm, Nat.sub_self]; rfl
    rw [hb]
    have hc : Spec.Huffman.cnt lens (Spec.Huffman.minLen lens) ≤ lens.length :=
      List.count_le_length
    omega
  · have h2 := hcase.resolve_left hzm
    have hlt : Spec.Huffman.minLen lens < zn := by omega
    have hb : Spec.Huffman.base lens zn =
        2 * (Spec.Huffman.limit lens (zn - 1) + 1) - ((lens.countP (· < zn) : Nat) : Int) := by
      unfold Spec.Huffman.base
      rw [ite_of_true ⟨hlt, hznM⟩]
    have hl1 := limit_of_mem lens (zn - 1) (by omega) (by omega)
    have hl := limit_of_mem lens zn hmzn hznM
    have hv : Spec.Huffman.vecAt lens (zn - Spec.Huffman.minLen lens) =
        2 * Spec.Huffman.vecAt lens (zn - 1 - Spec.Huffman.minLen lens) + lens.count zn := by
      have hk : zn - Spec.Huffman.minLen lens = (zn - 1 - Spec.Huffman.minLen lens) + 1 := by
        omega
      rw [hk]
      simp only [Spec.Huffman.vecAt, Spec.Huffman.cnt]
      have : Spec.Huffman.minLen lens + (zn - 1 - Spec.Huffman.minLen lens) + 1 = zn := by omega
      rw [this]
    rw [hb]
    omega

end Bzip2.Proofs.Huffman.Stop
