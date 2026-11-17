import Bzip2.Oracle.Decompress.Huffman
import Bzip2.Spec.Huffman
import Bzip2.Proofs.Huffman.Loops

/-!
# Huffman proofs: the oracle's decoding tables are the spec's

`BZ2_hbCreateDecodeTables` (`huffman.c:170-200`) is `createDecodeTables`; the spec describes its
`perm`, `limit` and `base` as functions of the list of code lengths (`Spec.Huffman.perm`,
`limit`, `base`). This module shows them equal on every table of a stream: between 1 and 258
lengths, each in `1 .. 20`.

The oracle's `for` loops are folds over `List.range'` (`Loops`), each proved by induction with the
invariant that says what the array holds after the first `k` passes: `perm` the first symbols of
`Spec.Huffman.perm`, the count array the number of symbols of each length (`huffman.c:185-186`),
the prefix sums the number of shorter symbols (`huffman.c:187-188`), `limit` the last code of each
length (`huffman.c:190-197`), `base` the fix-up of the prefix sums (`huffman.c:198-199`).
-/

namespace Bzip2.Proofs.Huffman.DecodeTables

open Bzip2.Oracle.Decompress.Huffman Bzip2.Proofs.Huffman.Loops Bzip2

/-! ### The loops of `createDecodeTables` as folds -/

/-- The loop filling `perm` (`huffman.c:180-183`): the array and the number of entries set. -/
def permLoop (length : Array UInt8) (minLen maxLen : Nat) : Array Nat × Nat :=
  (List.range' minLen (maxLen + 1 - minLen)).foldl (fun b i =>
    (List.range' 0 length.size).foldl (fun b j =>
      if (length[j]!.toNat == i) = true then (b.1.set! b.2 j, b.2 + 1) else b) b)
    (Array.replicate maxAlphaSize 0, 0)

/-- The loop counting the symbols of each length in `base[length + 1]` (`huffman.c:185-186`). -/
def countLoop (length : Array UInt8) : Array Int :=
  (List.range' 0 length.size).foldl (fun b a => b.modify (length[a]!.toNat + 1) fun x => x + 1)
    (Array.replicate maxCodeLen 0)

/-- The prefix sums of `huffman.c:187-188`. -/
def sumLoop (b : Array Int) : Array Int :=
  (List.range' 1 (maxCodeLen - 1)).foldl (fun b a => b.set! a (b[a]! + b[a - 1]!)) b

/-- The loop computing `limit` (`huffman.c:190-197`) from the prefix sums `base`: the array
and `vec`. -/
def limitLoop (base : Array Int) (minLen maxLen : Nat) : Array Int × Int :=
  (List.range' minLen (maxLen + 1 - minLen)).foldl
    (fun b a => (b.1.set! a (b.2 + (base[a + 1]! - base[a]!) - 1),
      (b.2 + (base[a + 1]! - base[a]!)) * 2))
    (Array.replicate maxCodeLen 0, 0)

/-- The fix-up of `base` (`huffman.c:198-199`). -/
def fixLoop (limit base : Array Int) (minLen maxLen : Nat) : Array Int :=
  (List.range' (minLen + 1) (maxLen + 1 - (minLen + 1))).foldl
    (fun b a => b.set! a ((limit[a - 1]! + 1) * 2 - b[a]!)) base

theorem createDecodeTables_eq (length : Array UInt8) (minLen maxLen : Nat) :
    createDecodeTables length minLen maxLen =
      let base₁ := sumLoop (countLoop length)
      let limit := (limitLoop base₁ minLen maxLen).1
      { limit, base := fixLoop limit base₁ minLen maxLen,
        perm := (permLoop length minLen maxLen).1, minLen } := by
  unfold createDecodeTables
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

/-! ### The lengths as the spec's list -/

/-- The code lengths of a table, as the spec's list. -/
def lensOf (length : Array UInt8) : List Nat := length.toList.map UInt8.toNat

theorem lensOf_length (length : Array UInt8) : (lensOf length).length = length.size := by
  simp [lensOf]

theorem symLen_eq (length : Array UInt8) (j : Nat) :
    length[j]!.toNat = (lensOf length).getD j 0 := by
  by_cases h : j < length.size
  · rw [getElem!_pos length j h]
    simp [lensOf, List.getD_eq_getElem?_getD, h]
  · rw [getElem!_neg length j h]
    simp [lensOf, List.getD_eq_getElem?_getD, h]
    rfl

/-- A fold over the indices of a list that reads the entries with `getD` is a fold over the
list. -/
theorem foldl_range_getD {β : Type} (l : List Nat) (g : β → Nat → β) (init : β) :
    (List.range' 0 l.length).foldl (fun b a => g b (l.getD a 0)) init = l.foldl g init := by
  induction l generalizing init with
  | nil => simp
  | cons x t ih =>
    rw [List.length_cons, ← List.range_eq_range', List.range_succ_eq_map, List.foldl_cons,
      List.foldl_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [List.range_eq_range'] at *
    exact ih (g init x)

/-! ### The count array and the prefix sums -/

theorem count_fold (l : List Nat) (a : Array Int) (hx : ∀ x ∈ l, x + 1 < a.size) (n : Nat) :
    (l.foldl (fun b x => b.modify (x + 1) fun y => y + 1) a)[n]! =
      a[n]! + ((l.filter (fun x => x + 1 == n)).length : Int) := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
    have hx' : ∀ y ∈ t, y + 1 < (a.modify (x + 1) fun y => y + 1).size := by
      intro y hy; simpa using hx y (List.mem_cons_of_mem _ hy)
    rw [List.foldl_cons, ih _ hx', getElem!_modify, List.filter_cons]
    have hxs : x + 1 < a.size := hx x (List.mem_cons_self ..)
    by_cases h : x + 1 = n
    · subst h; simp [hxs]; omega
    · simp [h, hxs]

theorem filter_succ_length (l : List Nat) (n : Nat) :
    (l.filter (fun x => x + 1 == n)).length = if n = 0 then 0 else l.count (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    simp only [ite_true]
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x _; simp
  · simp only [hn, ite_false]
    rw [List.count_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro x _
    by_cases h : x + 1 = n
    · subst h; simp
    · have : x ≠ n - 1 := by omega
      simp [h, this]

/-- After the counting loop, entry `n` holds the number of symbols of length `n - 1`
(`huffman.c:185-186`). -/
theorem countLoop_get (length : Array UInt8) (hlens : ∀ x ∈ lensOf length, x + 1 < maxCodeLen)
    (n : Nat) :
    (countLoop length)[n]! = if n = 0 then 0 else ((lensOf length).count (n - 1) : Int) := by
  have h1 : countLoop length = (lensOf length).foldl (fun b x => b.modify (x + 1) fun y => y + 1)
      (Array.replicate maxCodeLen 0) := by
    unfold countLoop
    simp only [symLen_eq]
    have := foldl_range_getD (lensOf length)
      (fun (b : Array Int) x => b.modify (x + 1) fun y => y + 1) (Array.replicate maxCodeLen 0)
    rw [lensOf_length] at this
    exact this
  rw [h1, count_fold _ _ (by simpa using hlens), filter_succ_length, getElem!_replicate]
  by_cases hn : n = 0 <;> simp [hn]

theorem countP_lt_succ (l : List Nat) (n : Nat) :
    l.countP (· < n + 1) = l.countP (· < n) + l.count n := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.countP_cons, List.count_cons, ih]
    rcases Nat.lt_trichotomy x n with h | h | h
    · simp [h, show x < n + 1 by omega, show x ≠ n by omega]
      omega
    · subst h; simp
      omega
    · simp [show ¬ x < n by omega, show ¬ x < n + 1 by omega, show x ≠ n by omega]

/-- The prefix-sum loop turns counts `c[a]` (`a ≥ 1`) into `P a`, if `P a = c[a] + P (a - 1)`
and `P 0 = c[0]`: after `k` passes entries `0 .. k` hold `P`. -/
theorem sumLoop_inv (c : Array Int) (hc : c.size = maxCodeLen) (P : Nat → Int)
    (h0 : c[0]! = P 0) (hP : ∀ a, 1 ≤ a → a < maxCodeLen → c[a]! + P (a - 1) = P a) :
    ∀ k, k + 1 ≤ maxCodeLen →
      ((List.range' 1 k).foldl (fun b a => b.set! a (b[a]! + b[a - 1]!)) c).size = maxCodeLen ∧
      ∀ n, ((List.range' 1 k).foldl (fun b a => b.set! a (b[a]! + b[a - 1]!)) c)[n]! =
        if n ≤ k then P n else c[n]! := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨hc, fun n => ?_⟩
    simp only [List.range'_zero, List.foldl_nil]
    by_cases hn : n = 0
    · subst hn; simpa using h0
    · simp [hn]
  | succ k ih =>
    intro hk
    obtain ⟨hsz, hget⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set b := (List.range' 1 k).foldl (fun b a => b.set! a (b[a]! + b[a - 1]!)) c with hb
    have hk1 : 1 + 1 * k = k + 1 := by omega
    rw [hk1]
    refine ⟨by rw [Array.size_set!, hsz], fun n => ?_⟩
    rw [getElem!_set!, hsz]
    have hv : b[k + 1]! + b[k + 1 - 1]! = P (k + 1) := by
      rw [hget (k + 1), hget (k + 1 - 1)]
      simp only [Nat.add_sub_cancel, Nat.le_refl, ite_true, show ¬ (k + 1 ≤ k) by omega, ite_false]
      exact hP (k + 1) (by omega) (by omega)
    by_cases hn : k + 1 = n
    · subst hn
      have h1 : k + 1 = k + 1 ∧ k + 1 < maxCodeLen := ⟨rfl, by omega⟩
      rw [ite_of_true h1, ite_of_true (Nat.le_refl _)]
      exact hv
    · have h1 : ¬ (k + 1 = n ∧ k + 1 < maxCodeLen) := fun h => hn h.1
      simp only [h1, ite_false, hget n]
      by_cases h2 : n ≤ k
      · simp [h2, show n ≤ k + 1 by omega]
      · simp [h2, show ¬ n ≤ k + 1 by omega]

/-- The loop computing `limit` (`huffman.c:190-197`): with `S k` the value of `vec` on entering
length `m + k`, after `k` passes entry `m + j` holds `W j`. -/
theorem limitLoop_inv (base : Array Int) (m : Nat) (D S W : Nat → Int)
    (hD : ∀ a, a + 1 < maxCodeLen → base[a + 1]! - base[a]! = D a)
    (hS0 : S 0 = 0) (hS : ∀ k, S (k + 1) = (S k + D (m + k)) * 2)
    (hW : ∀ k, W k = S k + D (m + k) - 1) :
    ∀ k, m + k < maxCodeLen →
      let b := (List.range' m k).foldl
        (fun b a => (b.1.set! a (b.2 + (base[a + 1]! - base[a]!) - 1),
          (b.2 + (base[a + 1]! - base[a]!)) * 2))
        (Array.replicate maxCodeLen (0 : Int), (0 : Int))
      b.1.size = maxCodeLen ∧ b.2 = S k ∧
      ∀ n, b.1[n]! = if m ≤ n ∧ n < m + k then W (n - m) else 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp, by simpa using hS0.symm, fun n => ?_⟩
    simp only [List.range'_zero, List.foldl_nil, getElem!_replicate]
    have hnot : ¬ (m ≤ n ∧ n < m + 0) := by omega
    simp only [hnot, ↓reduceIte]
    by_cases hn : n < maxCodeLen <;> simp [hn]
  | succ k ih =>
    intro hk
    obtain ⟨hsz, hvec, hget⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set b := (List.range' m k).foldl
      (fun b a => (b.1.set! a (b.2 + (base[a + 1]! - base[a]!) - 1),
        (b.2 + (base[a + 1]! - base[a]!)) * 2))
      (Array.replicate maxCodeLen (0 : Int), (0 : Int)) with hb
    have hk1 : m + 1 * k = m + k := by omega
    rw [hk1]
    have hd := hD (m + k) (by omega)
    simp only [hd, hvec]
    refine ⟨by rw [Array.size_set!, hsz], ?_, fun n => ?_⟩
    · rw [hS k]
    · rw [getElem!_set!, hsz]
      by_cases hn : m + k = n
      · subst hn
        have h1 : m + k = m + k ∧ m + k < maxCodeLen := ⟨rfl, by omega⟩
        have h2 : m ≤ m + k ∧ m + k < m + (k + 1) := ⟨by omega, by omega⟩
        simp only [h1, h2, and_self, ↓reduceIte]
        rw [Nat.add_sub_cancel_left, hW k]
      · have h1 : ¬ (m + k = n ∧ m + k < maxCodeLen) := fun h => hn h.1
        simp only [h1, ↓reduceIte, hget n]
        by_cases h2 : m ≤ n ∧ n < m + k
        · simp [h2, show m ≤ n ∧ n < m + (k+1) by omega]
        · have : ¬ (m ≤ n ∧ n < m + (k + 1)) := by omega
          simp [h2, this]

/-- The fix-up of `base` (`huffman.c:198-199`): after `k` passes entries `m + 1 ..< m + 1 + k`
hold `(limit[n - 1] + 1) * 2 - base[n]`. -/
theorem fixLoop_inv (limit base : Array Int) (m : Nat) :
    ∀ k, m + 1 + k ≤ base.size →
      let b := (List.range' (m + 1) k).foldl
        (fun b a => b.set! a ((limit[a - 1]! + 1) * 2 - b[a]!)) base
      b.size = base.size ∧ ∀ n, b[n]! =
        if m + 1 ≤ n ∧ n < m + 1 + k then (limit[n - 1]! + 1) * 2 - base[n]! else base[n]! := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, fun n => ?_⟩
    have hnot : ¬ (m + 1 ≤ n ∧ n < m + 1 + 0) := by omega
    simp only [List.range'_zero, List.foldl_nil, hnot, ↓reduceIte]
  | succ k ih =>
    intro hk
    obtain ⟨hsz, hget⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set b := (List.range' (m + 1) k).foldl
      (fun b a => b.set! a ((limit[a - 1]! + 1) * 2 - b[a]!)) base with hb
    have hk1 : m + 1 + 1 * k = m + 1 + k := by omega
    rw [hk1]
    refine ⟨by rw [Array.size_set!, hsz], fun n => ?_⟩
    rw [getElem!_set!, hsz]
    have hbk : b[m + 1 + k]! = base[m + 1 + k]! := by
      rw [hget]; simp
    by_cases hn : m + 1 + k = n
    · subst hn
      have h1 : m + 1 + k = m + 1 + k ∧ m + 1 + k < base.size := ⟨rfl, by omega⟩
      have h2 : m + 1 ≤ m + 1 + k ∧ m + 1 + k < m + 1 + (k + 1) := ⟨by omega, by omega⟩
      simp only [h1, h2, and_self, ↓reduceIte, hbk]
    · have h1 : ¬ (m + 1 + k = n ∧ m + 1 + k < base.size) := fun h => hn h.1
      simp only [h1, ↓reduceIte, hget n]
      by_cases h2 : m + 1 ≤ n ∧ n < m + 1 + k
      · simp [h2, show m + 1 ≤ n ∧ n < m + 1 + (k + 1) by omega]
      · have : ¬ (m + 1 ≤ n ∧ n < m + 1 + (k + 1)) := by omega
        simp [h2, this]

/-! ### `perm` -/

/-- What the loop that fills `perm` has done: it holds `acc`'s entries first, the number of entries
set is `acc.length`. -/
def PermInv (b : Array Nat × Nat) (acc : List Nat) : Prop :=
  b.1.size = maxAlphaSize ∧ b.2 = acc.length ∧ ∀ k < acc.length, b.1[k]! = acc.getD k 0

theorem permInv_push (b : Array Nat × Nat) (acc : List Nat) (j : Nat) (h : PermInv b acc)
    (hlt : acc.length < maxAlphaSize) :
    PermInv (b.1.set! b.2 j, b.2 + 1) (acc ++ [j]) := by
  obtain ⟨hsz, hpp, hget⟩ := h
  refine ⟨by simpa using hsz, by simp [hpp], fun k hk => ?_⟩
  simp only [List.length_append, List.length_singleton] at hk
  rw [getElem!_set!, hsz, hpp]
  by_cases hkk : acc.length = k
  · have h1 : acc.length = k ∧ acc.length < maxAlphaSize := ⟨hkk, hlt⟩
    rw [ite_of_true h1]
    subst hkk
    simp
  · have h1 : ¬ (acc.length = k ∧ acc.length < maxAlphaSize) := fun h => hkk h.1
    have hk' : k < acc.length := by omega
    rw [ite_of_false h1, hget k hk', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hk']

theorem perm_inner (length : Array UInt8) (i : Nat) (js : List Nat) :
    ∀ (b : Array Nat × Nat) (acc : List Nat), PermInv b acc →
      acc.length + (js.filter (fun j => length[j]!.toNat == i)).length ≤ maxAlphaSize →
      PermInv (js.foldl (fun b j =>
        if (length[j]!.toNat == i) = true then (b.1.set! b.2 j, b.2 + 1) else b) b)
        (acc ++ js.filter (fun j => length[j]!.toNat == i)) := by
  induction js with
  | nil => intro b acc h _; simpa using h
  | cons j t ih =>
    intro b acc h hle
    rw [List.foldl_cons, List.filter_cons]
    by_cases hj : (length[j]!.toNat == i) = true
    · simp only [hj, ↓reduceIte]
      rw [List.filter_cons] at hle
      simp only [hj, ↓reduceIte, List.length_cons] at hle
      have := ih _ (acc ++ [j]) (permInv_push b acc j h (by omega)) (by
        simp only [List.length_append, List.length_singleton]; omega)
      simpa using this
    · simp only [hj, Bool.false_eq_true, ↓reduceIte]
      rw [List.filter_cons] at hle
      simp only [hj, Bool.false_eq_true, ↓reduceIte] at hle
      exact ih b acc h hle

theorem perm_outer (length : Array UInt8) (ls : List Nat) :
    ∀ (b : Array Nat × Nat) (acc : List Nat), PermInv b acc →
      acc.length + (ls.flatMap fun i =>
        (List.range' 0 length.size).filter (fun j => length[j]!.toNat == i)).length
          ≤ maxAlphaSize →
      PermInv (ls.foldl (fun b i => (List.range' 0 length.size).foldl (fun b j =>
        if (length[j]!.toNat == i) = true then (b.1.set! b.2 j, b.2 + 1) else b) b) b)
        (acc ++ ls.flatMap fun i =>
          (List.range' 0 length.size).filter (fun j => length[j]!.toNat == i)) := by
  induction ls with
  | nil => intro b acc h _; simpa using h
  | cons i t ih =>
    intro b acc h hle
    rw [List.foldl_cons, List.flatMap_cons]
    rw [List.flatMap_cons, List.length_append, ← Nat.add_assoc] at hle
    have h1 := perm_inner length i (List.range' 0 length.size) b acc h
      (by omega)
    have h2 := ih _ _ h1 (by rw [List.length_append]; omega)
    simpa [List.append_assoc] using h2

/-! ### Facts about the spec's definitions -/

theorem vecAt_eq (lens : List Nat) (k : Nat) :
    Spec.Huffman.vecAt lens k =
      Spec.Huffman.startAt lens k + Spec.Huffman.cnt lens (Spec.Huffman.minLen lens + k) := by
  induction k with
  | zero => simp [Spec.Huffman.vecAt, Spec.Huffman.startAt]
  | succ k ih =>
    simp only [Spec.Huffman.vecAt, Spec.Huffman.startAt, ih]
    rw [Nat.add_assoc (Spec.Huffman.minLen lens) k 1]

theorem foldl_min_le (l : List Nat) (a : Nat) :
    l.foldl min a ≤ a ∧ (∀ x ∈ l, l.foldl min a ≤ x) ∧
      (l.foldl min a = a ∨ l.foldl min a ∈ l) := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
    obtain ⟨h1, h2, h3⟩ := ih (min a x)
    rw [List.foldl_cons]
    refine ⟨by omega, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact h2 y hy
    · rcases h3 with h3 | h3
      · rcases Nat.le_total a x with h | h
        · left; omega
        · right; rw [h3]; rw [Nat.min_eq_right h]; exact List.mem_cons_self ..
      · right; exact List.mem_cons_of_mem _ h3

theorem le_foldl_max (l : List Nat) (a : Nat) :
    a ≤ l.foldl max a ∧ (∀ x ∈ l, x ≤ l.foldl max a) ∧
      (l.foldl max a = a ∨ l.foldl max a ∈ l) := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
    obtain ⟨h1, h2, h3⟩ := ih (max a x)
    rw [List.foldl_cons]
    refine ⟨by omega, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact h2 y hy
    · rcases h3 with h3 | h3
      · rcases Nat.le_total a x with h | h
        · right; rw [h3]; rw [Nat.max_eq_right h]; exact List.mem_cons_self ..
        · left; omega
      · right; exact List.mem_cons_of_mem _ h3

/-- A legal, nonempty table: its least and greatest lengths lie in `1 .. 20` and bound every
length. -/
theorem minLen_maxLen (lens : List Nat) (hne : lens ≠ []) (hlegal : ∀ x ∈ lens, 1 ≤ x ∧ x ≤ 20) :
    1 ≤ Spec.Huffman.minLen lens ∧ Spec.Huffman.minLen lens ≤ Spec.Huffman.maxLen lens ∧
      Spec.Huffman.maxLen lens ≤ 20 ∧
      ∀ x ∈ lens, Spec.Huffman.minLen lens ≤ x ∧ x ≤ Spec.Huffman.maxLen lens := by
  obtain ⟨a1, a2, a3⟩ := foldl_min_le lens 32
  obtain ⟨b1, b2, b3⟩ := le_foldl_max lens 0
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil lens hne
  have hmin : Spec.Huffman.minLen lens = lens.foldl min 32 := rfl
  have hmax : Spec.Huffman.maxLen lens = lens.foldl max 0 := rfl
  rw [hmin, hmax]
  have hx1 := a2 x hx
  have hx2 := b2 x hx
  refine ⟨?_, by omega, ?_, fun y hy => ⟨a2 y hy, b2 y hy⟩⟩
  · rcases a3 with h | h
    · omega
    · exact (hlegal _ h).1
  · rcases b3 with h | h
    · omega
    · exact (hlegal _ h).2

theorem minLenOf_eq (length : Array UInt8) :
    length.foldl (fun m l => min m l.toNat) 32 = Spec.Huffman.minLen (lensOf length) := by
  unfold Spec.Huffman.minLen lensOf
  rw [List.foldl_map, Array.foldl_toList]

theorem maxLenOf_eq (length : Array UInt8) :
    length.foldl (fun m l => max m l.toNat) 0 = Spec.Huffman.maxLen (lensOf length) := by
  unfold Spec.Huffman.maxLen lensOf
  rw [List.foldl_map, Array.foldl_toList]

/-! ### `perm` has one entry per symbol -/

theorem countP_split (l : List Nat) (f : Nat → Nat) (m k : Nat) :
    l.countP (fun j => decide (m ≤ f j ∧ f j < m + (k + 1))) =
      l.countP (fun j => decide (m ≤ f j ∧ f j < m + k)) + l.countP (fun j => f j == m + k) := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.countP_cons, ih]
    by_cases h1 : m ≤ f x ∧ f x < m + k
    · have h2 : m ≤ f x ∧ f x < m + (k + 1) := ⟨h1.1, by omega⟩
      have e1 : (if decide (m ≤ f x ∧ f x < m + (k + 1)) = true then 1 else 0) = 1 := by
        simp [h2]
      have e2 : (if decide (m ≤ f x ∧ f x < m + k) = true then 1 else 0) = 1 := by simp [h1]
      have e3 : (if (f x == m + k) = true then 1 else 0) = 0 := by
        have : ¬ (f x = m + k) := by omega
        simp [this]
      omega
    · by_cases h3 : f x = m + k
      · have h2 : m ≤ f x ∧ f x < m + (k + 1) := ⟨by omega, by omega⟩
        have e1 : (if decide (m ≤ f x ∧ f x < m + (k + 1)) = true then 1 else 0) = 1 := by
          simp [h2]
        have e2 : (if decide (m ≤ f x ∧ f x < m + k) = true then 1 else 0) = 0 := by simp [h1]
        have e3 : (if (f x == m + k) = true then 1 else 0) = 1 := by simp [h3]
        omega
      · have h2 : ¬ (m ≤ f x ∧ f x < m + (k + 1)) := by omega
        have e1 : (if decide (m ≤ f x ∧ f x < m + (k + 1)) = true then 1 else 0) = 0 := by
          simp [h2]
        have e2 : (if decide (m ≤ f x ∧ f x < m + k) = true then 1 else 0) = 0 := by simp [h1]
        have e3 : (if (f x == m + k) = true then 1 else 0) = 0 := by simp [h3]
        omega

theorem flatMap_length (lens : List Nat) (n m k : Nat) :
    ((List.range' m k).flatMap fun l =>
      (List.range n).filter fun j => lens.getD j 0 == l).length =
      (List.range n).countP fun j => decide (m ≤ lens.getD j 0 ∧ lens.getD j 0 < m + k) := by
  induction k with
  | zero =>
    simp only [List.range'_zero, List.flatMap_nil, List.length_nil, Nat.add_zero]
    exact (List.countP_eq_zero.mpr fun a _ => by rw [decide_eq_true_eq]; omega).symm
  | succ k ih =>
    rw [List.range'_concat, List.flatMap_append, List.length_append, ih, countP_split]
    simp [List.countP_eq_length_filter]

/-- `perm` has an entry for each symbol. -/
theorem perm_length (lens : List Nat) (hne : lens ≠ []) (hlegal : ∀ x ∈ lens, 1 ≤ x ∧ x ≤ 20) :
    (Spec.Huffman.perm lens).length = lens.length := by
  obtain ⟨h1, h2, h3, h4⟩ := minLen_maxLen lens hne hlegal
  unfold Spec.Huffman.perm
  rw [flatMap_length, List.countP_eq_length.mpr, List.length_range]
  intro j hj
  have hj' : j < lens.length := List.mem_range.mp hj
  have hmem : lens.getD j 0 ∈ lens := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    exact List.getElem_mem hj'
  have := h4 _ hmem
  simp only [decide_eq_true_eq]
  omega

/-! ### The tables -/

theorem countLoop_size (length : Array UInt8) : (countLoop length).size = maxCodeLen := by
  unfold countLoop
  have h : ∀ (l : List Nat) (a : Array Int),
      (l.foldl (fun b x => b.modify (length[x]!.toNat + 1) fun y => y + 1) a).size = a.size := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x t ih => intro a; rw [List.foldl_cons, ih, Array.size_modify]
  rw [h]
  simp

/-- The prefix sums count the symbols shorter than `n`. -/
theorem sumLoop_get (length : Array UInt8) (hlegal : ∀ x ∈ lensOf length, 1 ≤ x ∧ x ≤ 20) :
    (sumLoop (countLoop length)).size = maxCodeLen ∧
    ∀ n < maxCodeLen, (sumLoop (countLoop length))[n]! =
      ((lensOf length).countP (· < n) : Nat) := by
  have h23 : maxCodeLen = 23 := rfl
  have hlens : ∀ x ∈ lensOf length, x + 1 < maxCodeLen := fun x hx => by
    have := (hlegal x hx).2; omega
  have h0 : (countLoop length)[0]! = (((lensOf length).countP (· < 0) : Nat) : Int) := by
    rw [countLoop_get length hlens]
    simp
  have hP : ∀ a, 1 ≤ a → a < maxCodeLen → (countLoop length)[a]! +
      (((lensOf length).countP (· < a - 1) : Nat) : Int) =
        (((lensOf length).countP (· < a) : Nat) : Int) := by
    intro a ha _
    rw [countLoop_get length hlens, ite_of_false (by omega)]
    have := countP_lt_succ (lensOf length) (a - 1)
    rw [Nat.sub_add_cancel ha] at this
    omega
  obtain ⟨hsz, hget⟩ := sumLoop_inv (countLoop length) (countLoop_size length)
    (fun n => (((lensOf length).countP (· < n) : Nat) : Int)) h0 hP (maxCodeLen - 1) (by omega)
  refine ⟨hsz, fun n hn => ?_⟩
  have := hget n
  rw [ite_of_true (by omega)] at this
  exact this

/-- `limit` is the spec's. -/
theorem limitLoop_get (length : Array UInt8) (hne : 0 < length.size)
    (hlegal : ∀ x ∈ lensOf length, 1 ≤ x ∧ x ≤ 20) (m M : Nat)
    (hm : m = Spec.Huffman.minLen (lensOf length)) (hM : M = Spec.Huffman.maxLen (lensOf length))
    (n : Nat) :
    ((limitLoop (sumLoop (countLoop length)) m M).1)[n]! =
      Spec.Huffman.limit (lensOf length) n := by
  have h23 : maxCodeLen = 23 := rfl
  have hne' : lensOf length ≠ [] := by
    intro h
    have := lensOf_length length
    rw [h] at this
    simp only [List.length_nil] at this
    omega
  obtain ⟨hm1, hmM, hM20, _⟩ := minLen_maxLen (lensOf length) hne' hlegal
  have hm1' : 1 ≤ m := by rw [hm]; exact hm1
  have hmM' : m ≤ M := by rw [hm, hM]; exact hmM
  have hM20' : M ≤ 20 := by rw [hM]; exact hM20
  obtain ⟨hsz, hbase⟩ := sumLoop_get length hlegal
  have hD : ∀ a, a + 1 < maxCodeLen →
      (sumLoop (countLoop length))[a + 1]! - (sumLoop (countLoop length))[a]! =
        (((lensOf length).count a : Nat) : Int) := by
    intro a ha
    rw [hbase (a + 1) ha, hbase a (by omega)]
    have := countP_lt_succ (lensOf length) a
    omega
  have hS : ∀ k, ((Spec.Huffman.startAt (lensOf length) (k + 1) : Nat) : Int) =
      (((Spec.Huffman.startAt (lensOf length) k : Nat) : Int) +
        (((lensOf length).count (m + k) : Nat) : Int)) * 2 := by
    intro k
    simp only [Spec.Huffman.startAt, Spec.Huffman.cnt, ← hm]
    omega
  have hW : ∀ k, ((Spec.Huffman.vecAt (lensOf length) k : Nat) : Int) - 1 =
      ((Spec.Huffman.startAt (lensOf length) k : Nat) : Int) +
        (((lensOf length).count (m + k) : Nat) : Int) - 1 := by
    intro k
    rw [vecAt_eq, ← hm]
    simp only [Spec.Huffman.cnt]
    omega
  obtain ⟨_, _, hget⟩ := limitLoop_inv (sumLoop (countLoop length)) m
    (fun a => (((lensOf length).count a : Nat) : Int))
    (fun k => ((Spec.Huffman.startAt (lensOf length) k : Nat) : Int))
    (fun k => ((Spec.Huffman.vecAt (lensOf length) k : Nat) : Int) - 1) hD
    (by simp [Spec.Huffman.startAt]) hS hW (M + 1 - m) (by omega)
  have := hget n
  unfold limitLoop
  rw [this, Spec.Huffman.limit, ← hm, ← hM]
  by_cases h : m ≤ n ∧ n ≤ M
  · rw [ite_of_true h, ite_of_true (by omega)]
  · rw [ite_of_false h, ite_of_false (by omega)]

end Bzip2.Proofs.Huffman.DecodeTables
