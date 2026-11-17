import Bzip2.Spec.Huffman
import Bzip2.Proofs.Huffman.DecodeTables
import Bzip2.Proofs.Huffman.Stop
import Bzip2.Proofs.Huffman.Bits

/-!
# Huffman proofs: the assigned code decodes

`Spec.Huffman.codeword lens i` is the canonical code of symbol `i` (`huffman.c:152-165`) and
`Spec.Huffman.decodeSym` reads a symbol as the C decoder does. This module proves that reading
what `codeword` writes gives the symbol back: `decodeSym_codeword`, for every legal table that is
not over-subscribed (`Kraft`: the lengths' Kraft sum is at most 1), complete or not. For an
over-subscribed table the assigned values do not fit their lengths, the decoder never stops at
some of them, and the statement is false (see the examples of `Spec.Huffman`).

The argument is the one the decoder is built for. With `m = minLen` and `startAt k` the first code
of length `m + k`: the codes of length `l` are `startAt (l - m)` up to `limit[l]`; the first code
of the next length is `2 * (limit[l] + 1)`, so a longer code, cut to `n < l` bits, is above
`limit[n]` and the decoder reads on; at `n = l` it is at most `limit[l]` and the decoder stops.
The index it computes, `code - base[l]`, is the position of the symbol in `perm`.
-/

namespace Bzip2.Proofs.Huffman.Canonical

open Bzip2.Proofs.Huffman.DecodeTables Bzip2.Proofs.Huffman.Stop Bzip2.Proofs.Huffman.Bits
  Bzip2.Proofs.Huffman.Loops

/-- The lengths are not over-subscribed: their Kraft sum `∑ 2 ^ (-len)` is at most 1 (scaled by
`2 ^ 20`, the longest length of a stream). -/
def Kraft (lens : List Nat) : Prop := (lens.map fun l => 2 ^ (20 - l)).sum ≤ 2 ^ 20

/-- A complete table is not over-subscribed. -/
theorem Kraft.of_complete {lens : List Nat} (h : Spec.Huffman.Complete lens) : Kraft lens := by
  unfold Spec.Huffman.Complete at h
  unfold Kraft
  omega

/-- The part of the Kraft sum contributed by lengths below `n`. -/
def kraftBelow (lens : List Nat) (n : Nat) : Nat :=
  (lens.map fun x => if x < n then 2 ^ (20 - x) else 0).sum

theorem kraftBelow_succ (lens : List Nat) (n : Nat) :
    kraftBelow lens (n + 1) = kraftBelow lens n + lens.count n * 2 ^ (20 - n) := by
  unfold kraftBelow
  induction lens with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, ih]
    rcases Nat.lt_trichotomy x n with h | h | h
    · have h1 : x < n + 1 := by omega
      have h2 : ¬ (x == n) = true := by simp only [beq_iff_eq]; omega
      simp only [h, h1, h2, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
      omega
    · subst h
      simp only [Nat.lt_irrefl, ↓reduceIte, Nat.zero_add, Nat.lt_succ_self, beq_self_eq_true,
        Nat.add_mul, Nat.one_mul]
      omega
    · have h1 : ¬ x < n + 1 := by omega
      have h2 : ¬ x < n := by omega
      have h3 : ¬ (x == n) = true := by simp only [beq_iff_eq]; omega
      simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, Nat.add_zero]
      omega

theorem kraftBelow_le (lens : List Nat) (n : Nat) :
    kraftBelow lens n ≤ (lens.map fun l => 2 ^ (20 - l)).sum := by
  unfold kraftBelow
  induction lens with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hp := Nat.two_pow_pos (20 - x)
    by_cases h : x < n
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]; omega

/-- The first code of length `m + k` times `2 ^ (20 - (m + k))` is the Kraft sum of the shorter
lengths (`huffman.c:160-164`: `vec` is that sum, doubled at every length). -/
theorem startAt_mul (lens : List Nat) (hall : ∀ x ∈ lens, Spec.Huffman.minLen lens ≤ x)
    (k : Nat) (hk : Spec.Huffman.minLen lens + k ≤ 20) :
    Spec.Huffman.startAt lens k * 2 ^ (20 - (Spec.Huffman.minLen lens + k)) =
      kraftBelow lens (Spec.Huffman.minLen lens + k) := by
  induction k with
  | zero =>
    simp only [Spec.Huffman.startAt, Nat.zero_mul, Nat.add_zero]
    unfold kraftBelow
    symm
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have := hall x hx
    rw [ite_of_false (by omega)]
  | succ k ih =>
    have ih := ih (by omega)
    have e : Spec.Huffman.minLen lens + (k + 1) = (Spec.Huffman.minLen lens + k) + 1 :=
      (Nat.add_assoc ..).symm
    rw [e, kraftBelow_succ, ← ih]
    have hp : 2 ^ (20 - (Spec.Huffman.minLen lens + k)) =
        2 * 2 ^ (20 - (Spec.Huffman.minLen lens + k + 1)) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    rw [hp]
    simp only [Spec.Huffman.startAt, Spec.Huffman.cnt]
    ring

/-- The first code of a longer length, `startAt j`, is at least `vecAt k * 2 ^ (j - k)`: one more
than the last code of length `m + k`, shifted to length `m + j` (`huffman.c:160-164`). -/
theorem vecAt_mul_le (lens : List Nat) (k d : Nat) :
    Spec.Huffman.vecAt lens k * 2 ^ (d + 1) ≤ Spec.Huffman.startAt lens (k + 1 + d) := by
  induction d with
  | zero =>
    simp only [Spec.Huffman.startAt]
    rw [vecAt_eq, Nat.zero_add, pow_one, Nat.mul_comm]
  | succ d ih =>
    have e : k + 1 + (d + 1) = (k + 1 + d) + 1 := by omega
    rw [e]
    simp only [Spec.Huffman.startAt]
    have h2 : Spec.Huffman.vecAt lens k * 2 ^ (d + 1 + 1) =
        2 * (Spec.Huffman.vecAt lens k * 2 ^ (d + 1)) := by
      rw [pow_succ 2 (d + 1)]
      ring
    omega

theorem base_eq (lens : List Nat) (hall : ∀ x ∈ lens, Spec.Huffman.minLen lens ≤ x) (l : Nat)
    (h1 : Spec.Huffman.minLen lens ≤ l) (h2 : l ≤ Spec.Huffman.maxLen lens) :
    Spec.Huffman.base lens l =
      (Spec.Huffman.startAt lens (l - Spec.Huffman.minLen lens) : Int) -
        ((lens.countP (· < l) : Nat) : Int) := by
  unfold Spec.Huffman.base
  by_cases hlm : l = Spec.Huffman.minLen lens
  · subst hlm
    rw [ite_of_false (by omega), Nat.sub_self]
    have := countP_lt_min lens hall
    simp [Spec.Huffman.startAt, this]
  · rw [ite_of_true ⟨by omega, h2⟩, limit_of_mem lens (l - 1) (by omega) (by omega)]
    have hk : l - Spec.Huffman.minLen lens = (l - 1 - Spec.Huffman.minLen lens) + 1 := by omega
    rw [hk]
    simp only [Spec.Huffman.startAt]
    have := vecAt_eq lens (l - 1 - Spec.Huffman.minLen lens)
    omega

/-- Earlier symbols of a length are fewer than all symbols of it. -/
theorem count_take_lt (lens : List Nat) (i : Nat) (hi : i < lens.length) :
    (lens.take i).count (lens.getD i 0) < lens.count (lens.getD i 0) := by
  have hd : lens.drop i = lens[i] :: lens.drop (i + 1) := List.drop_eq_getElem_cons hi
  have h1 : lens.getD i 0 = lens[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have hc : lens.count (lens.getD i 0) =
      (lens.take i).count (lens.getD i 0) + (lens.drop i).count (lens.getD i 0) := by
    rw [← List.count_append, List.take_append_drop]
  rw [hc, hd, List.count_cons, h1]
  simp

/-- If the lengths are not over-subscribed, the codes of length `l` fit in `l` bits. -/
theorem startAt_add_cnt_le (lens : List Nat) (hall : ∀ x ∈ lens, Spec.Huffman.minLen lens ≤ x)
    (hk : Kraft lens) (l : Nat) (h1 : Spec.Huffman.minLen lens ≤ l) (h2 : l ≤ 20) :
    Spec.Huffman.startAt lens (l - Spec.Huffman.minLen lens) + lens.count l ≤ 2 ^ l := by
  have h := startAt_mul lens hall (l - Spec.Huffman.minLen lens) (by omega)
  have e : Spec.Huffman.minLen lens + (l - Spec.Huffman.minLen lens) = l := by omega
  rw [e] at h
  have hs := kraftBelow_succ lens l
  have hle := kraftBelow_le lens (l + 1)
  unfold Kraft at hk
  have hp : 2 ^ l * 2 ^ (20 - l) = 2 ^ 20 := by rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (20 - l) := Nat.two_pow_pos _
  apply Nat.le_of_mul_le_mul_right _ hpos
  rw [Nat.add_mul, h, hp, ← hs]
  omega

/-- One more bit of a number's binary expansion. -/
theorem div_pow_succ (c e : Nat) : c / 2 ^ (e + 1) * 2 + c / 2 ^ e % 2 = c / 2 ^ e := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (c / 2 ^ e) 2
  omega

/-- The first `n` bits of the code of a value below `2 ^ l`, written in `l` bits, spell the value
shifted down by `l - n`. -/
theorem val_take_bits (c l n : Nat) (hc : c < 2 ^ l) (hn : n ≤ l) :
    val (((List.range l).reverse.map (fun k => c.testBit k)).take n) = c / 2 ^ (l - n) := by
  induction n with
  | zero =>
    simp only [List.take_zero, Nat.sub_zero]
    rw [Nat.div_eq_of_lt hc]; rfl
  | succ n ih =>
    have ih := ih (by omega)
    have hlen : n < ((List.range l).reverse.map (fun k => c.testBit k)).length := by simp; omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some, val_append, ih,
      List.length_singleton, pow_one]
    have hb : ((List.range l).reverse.map (fun k => c.testBit k))[n] = c.testBit (l - (n + 1)) := by
      simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
      congr 1
      omega
    rw [hb]
    have hl : l - n = (l - (n + 1)) + 1 := by omega
    rw [hl, Nat.testBit_eq_decide_div_mod_eq]
    have := div_pow_succ c (l - (n + 1))
    have h2 : c / 2 ^ (l - (n + 1)) % 2 < 2 := Nat.mod_lt _ (by decide)
    have h3 : val [decide (c / 2 ^ (l - (n + 1)) % 2 = 1)] = c / 2 ^ (l - (n + 1)) % 2 := by
      simp only [val, List.foldl_cons, List.foldl_nil]
      by_cases h : c / 2 ^ (l - (n + 1)) % 2 = 1
      · simp [h]
      · have : c / 2 ^ (l - (n + 1)) % 2 = 0 := by omega
        simp [this]
    rw [h3]
    exact this

/-- `range n` around the index `i`. -/
theorem range_split (n i : Nat) (hi : i < n) :
    List.range n = List.range i ++ i :: List.range' (i + 1) (n - i - 1) := by
  have h1 : List.range' 0 n = List.range' 0 i ++ List.range' i (n - i) := by
    have := @List.range'_append_1 0 i (n - i)
    rw [Nat.zero_add, show i + (n - i) = n by omega] at this
    exact this.symm
  have h2 : List.range' i (n - i) = i :: List.range' (i + 1) (n - i - 1) := by
    have : n - i = (n - i - 1) + 1 := by omega
    rw [this, List.range'_succ]
    simp
  rw [List.range_eq_range', h1, h2, ← List.range_eq_range']

/-- Among the indices below `n` that satisfy `p`, `i` comes after the ones below `i`. -/
theorem getElem?_filter_range (n i : Nat) (p : Nat → Bool) (hi : i < n) (hp : p i = true) :
    ((List.range n).filter p)[((List.range i).filter p).length]? = some i := by
  rw [range_split n i hi, List.filter_append, List.filter_cons_of_pos hp,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Counting the earlier indices of length `l` is counting `l` in the earlier lengths. -/
theorem length_filter_range_getD (lens : List Nat) (l i : Nat) (hi : i ≤ lens.length) :
    ((List.range i).filter (fun j => lens.getD j 0 == l)).length = (lens.take i).count l := by
  rw [← List.countP_eq_length_filter]
  induction i with
  | zero => simp
  | succ i ih =>
    have ih := ih (by omega)
    have hi' : i < lens.length := by omega
    have hg : lens.getD i 0 = lens[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
    rw [List.range_succ, List.countP_append, ih, List.take_add_one,
      List.getElem?_eq_getElem hi', Option.toList_some, List.count_append,
      List.countP_cons, List.countP_nil, List.count_cons, List.count_nil, hg]

/-- Counting by index is counting in the list. -/
theorem countP_range_getD (lens : List Nat) (g : Nat → Bool) :
    (List.range lens.length).countP (fun j => g (lens.getD j 0)) = lens.countP g := by
  induction lens with
  | nil => simp
  | cons x t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map]
    simp only [Function.comp_def, Nat.succ_eq_add_one, List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, List.countP_cons]

/-- `perm` lists the symbols of a length in index order, after those of shorter lengths: the
position of symbol `i` is the number of shorter symbols plus the number of earlier symbols of its
length (`huffman.c:180-183`). -/
theorem perm_getElem? (lens : List Nat) (hall : ∀ x ∈ lens,
    Spec.Huffman.minLen lens ≤ x ∧ x ≤ Spec.Huffman.maxLen lens) (i : Nat) (hi : i < lens.length) :
    (Spec.Huffman.perm lens)[lens.countP (· < lens.getD i 0) +
      (lens.take i).count (lens.getD i 0)]? = some i := by
  have hmem : lens.getD i 0 ∈ lens := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨hl1, hl2⟩ := hall _ hmem
  generalize hl : lens.getD i 0 = l at *
  unfold Spec.Huffman.perm
  have hsplit : List.range' (Spec.Huffman.minLen lens)
      (Spec.Huffman.maxLen lens + 1 - Spec.Huffman.minLen lens) =
      List.range' (Spec.Huffman.minLen lens) (l - Spec.Huffman.minLen lens) ++
        l :: List.range' (l + 1) (Spec.Huffman.maxLen lens - l) := by
    have h1 := @List.range'_append_1 (Spec.Huffman.minLen lens)
      (l - Spec.Huffman.minLen lens) (Spec.Huffman.maxLen lens + 1 - l)
    rw [show Spec.Huffman.minLen lens + (l - Spec.Huffman.minLen lens) = l by omega,
      show l - Spec.Huffman.minLen lens + (Spec.Huffman.maxLen lens + 1 - l) =
        Spec.Huffman.maxLen lens + 1 - Spec.Huffman.minLen lens by omega] at h1
    rw [← h1]
    congr 1
    have : Spec.Huffman.maxLen lens + 1 - l = (Spec.Huffman.maxLen lens - l) + 1 := by omega
    rw [this, List.range'_succ]
  rw [hsplit, List.flatMap_append, List.flatMap_cons]
  have hA : ((List.range' (Spec.Huffman.minLen lens) (l - Spec.Huffman.minLen lens)).flatMap
      fun l' => (List.range lens.length).filter fun j => lens.getD j 0 == l').length =
        lens.countP (· < l) := by
    rw [flatMap_length, countP_range_getD lens
      (fun x => decide (Spec.Huffman.minLen lens ≤ x ∧
        x < Spec.Huffman.minLen lens + (l - Spec.Huffman.minLen lens)))]
    apply List.countP_congr
    intro x hx
    have := (hall x hx).1
    simp only [decide_eq_true_eq]
    omega
  have hf := getElem?_filter_range lens.length i (fun j => lens.getD j 0 == l) hi
    (by show (lens.getD i 0 == l) = true; rw [hl]; exact beq_self_eq_true _)
  rw [length_filter_range_getD lens l i (Nat.le_of_lt hi)] at hf
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hf
  rw [← hA, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hlt]
  exact hf

/-- Reading what `codeword` writes gives the symbol back, for every legal table that is not
over-subscribed. -/
theorem decodeSym_codeword (lens : List Nat) (hlegal : ∀ x ∈ lens, 1 ≤ x ∧ x ≤ 20)
    (hlen : lens.length ≤ 258) (hk : Kraft lens) (i : Nat) (hi : i < lens.length)
    (rest : List Bool) :
    Spec.Huffman.decodeSym lens (Spec.Huffman.codeword lens i ++ rest) = .sym i rest := by
  have hne : lens ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hm1, hmM, hM20, hbounds⟩ := minLen_maxLen lens hne hlegal
  have hmem : lens.getD i 0 ∈ lens := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨hl1, hl2⟩ := hbounds _ hmem
  have hall : ∀ x ∈ lens, Spec.Huffman.minLen lens ≤ x := fun x hx => (hbounds x hx).1
  have hle20 : ∀ x ∈ lens, x ≤ 20 := fun x hx => (hlegal x hx).2
  generalize hl : lens.getD i 0 = l at *
  have hcode : Spec.Huffman.code lens i =
      Spec.Huffman.startAt lens (l - Spec.Huffman.minLen lens) + (lens.take i).count l := by
    unfold Spec.Huffman.code
    rw [hl]
  have hcnt : (lens.take i).count l < lens.count l := by
    have := count_take_lt lens i hi
    rwa [hl] at this
  have hfit := startAt_add_cnt_le lens hall hk l hl1 (by omega)
  generalize hc : Spec.Huffman.code lens i = c at *
  have hc2 : c < 2 ^ l := by omega
  have hcw : Spec.Huffman.codeword lens i =
      (List.range l).reverse.map (fun k => c.testBit k) := by
    unfold Spec.Huffman.codeword
    rw [hl, hc]
  rw [hcw]
  have hcwlen : ((List.range l).reverse.map (fun k => c.testBit k)).length = l := by simp
  generalize hcwdef : (List.range l).reverse.map (fun k => c.testBit k) = cw at *
  have hcwval : ∀ n ≤ l, val (cw.take n) = c / 2 ^ (l - n) := by
    intro n hn
    rw [← hcwdef]
    exact val_take_bits c l n hc2 hn
  have hcwget : ∀ n (h : n < cw.length), cw[n] = c.testBit (l - (n + 1)) := by
    intro n h
    subst hcwdef
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    congr 1
    omega
  -- the value read after `n` bits is above `limit[n]` for every shorter length
  have hnostop : ∀ n, Spec.Huffman.minLen lens ≤ n → n < l →
      ¬ ((c / 2 ^ (l - n) : Nat) : Int) ≤ Spec.Huffman.limit lens n := by
    intro n hn1 hn2 hle
    rw [limit_of_mem lens n hn1 (by omega)] at hle
    have hv := vecAt_mul_le lens (n - Spec.Huffman.minLen lens) (l - n - 1)
    rw [show n - Spec.Huffman.minLen lens + 1 + (l - n - 1) = l - Spec.Huffman.minLen lens by omega,
      show l - n - 1 + 1 = l - n by omega] at hv
    have hdiv : Spec.Huffman.vecAt lens (n - Spec.Huffman.minLen lens) ≤ c / 2 ^ (l - n) :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
    omega
  have hloop : ∀ d n, n + d = l → Spec.Huffman.minLen lens ≤ n → ∀ f, d + 1 ≤ f →
      Spec.Huffman.loop lens f n (c / 2 ^ (l - n)) ((cw ++ rest).drop n) = .sym i rest := by
    intro d
    induction d with
    | zero =>
      intro n hn hmn f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hn' : l = n := by omega
      subst hn'
      have hz : ¬ l > 20 := by omega
      rw [Nat.sub_self, pow_zero, Nat.div_one]
      have hlim := limit_of_mem lens l hl1 hl2
      have hvec := vecAt_eq lens (l - Spec.Huffman.minLen lens)
      rw [show Spec.Huffman.minLen lens + (l - Spec.Huffman.minLen lens) = l by omega] at hvec
      have hstop : (c : Int) ≤ Spec.Huffman.limit lens l := by
        rw [hlim, hvec]
        simp only [Spec.Huffman.cnt]
        omega
      have hbase := base_eq lens hall l hl1 hl2
      have hsucc := countP_lt_succ lens l
      have hlenle : lens.countP (· < l + 1) ≤ lens.length := List.countP_le_length
      have hidx : (c : Int) - Spec.Huffman.base lens l =
          ((lens.countP (· < l) + (lens.take i).count l : Nat) : Int) := by
        rw [hbase]
        omega
      have hcond : ¬ ((c : Int) - Spec.Huffman.base lens l < 0 ∨
          (c : Int) - Spec.Huffman.base lens l ≥ 258) := by
        rw [hidx]
        omega
      have hperm := perm_getElem? lens hbounds i hi
      rw [hl] at hperm
      have hdrop : (cw ++ rest).drop l = rest := List.drop_left' hcwlen
      simp only [Spec.Huffman.loop, hz, hstop, ↓reduceIte, hcond, hdrop]
      rw [hidx, Int.toNat_natCast, hperm]
    | succ d ih =>
      intro n hn hmn f hf
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hnl : n < l := by omega
      have hz : ¬ n > 20 := by omega
      have hns := hnostop n hmn hnl
      have hlt : n < cw.length := by omega
      have hdrop : (cw ++ rest).drop n = cw[n] :: (cw ++ rest).drop (n + 1) := by
        have := List.drop_eq_getElem_cons (l := cw ++ rest) (i := n) (by simp; omega)
        rw [this, List.getElem_append_left hlt]
      have hih := ih (n + 1) (by omega) (by omega) f' (by omega)
      have hstep : 2 * (c / 2 ^ (l - n)) + (if cw[n] then 1 else 0) = c / 2 ^ (l - (n + 1)) := by
        rw [hcwget n hlt, Nat.testBit_eq_decide_div_mod_eq]
        have := div_pow_succ c (l - (n + 1))
        have h2 : c / 2 ^ (l - (n + 1)) % 2 < 2 := Nat.mod_lt _ (by decide)
        rw [show l - n = (l - (n + 1)) + 1 by omega]
        by_cases h : c / 2 ^ (l - (n + 1)) % 2 = 1
        · simp only [h, decide_true, ite_true]; omega
        · have : c / 2 ^ (l - (n + 1)) % 2 = 0 := by omega
          simp only [h, decide_false, Bool.false_eq_true, ite_false]; omega
      simp only [Spec.Huffman.loop, hz, hns, ↓reduceIte, hdrop, hstep]
      exact hih
  unfold Spec.Huffman.decodeSym
  have hlenbits : ¬ (cw ++ rest).length < Spec.Huffman.minLen lens := by
    simp only [List.length_append, hcwlen]; omega
  simp only [hlenbits, ↓reduceIte]
  have htake : (cw ++ rest).take (Spec.Huffman.minLen lens) = cw.take (Spec.Huffman.minLen lens) :=
    List.take_append_of_le_length (by omega)
  rw [htake]
  have hv := hcwval (Spec.Huffman.minLen lens) hl1
  have hv' : List.foldl (fun a b => 2 * a + if b = true then 1 else 0) 0
      (cw.take (Spec.Huffman.minLen lens)) = c / 2 ^ (l - Spec.Huffman.minLen lens) := hv
  rw [hv']
  exact hloop (l - Spec.Huffman.minLen lens) (Spec.Huffman.minLen lens) (by omega)
    (Nat.le_refl _) 23 (by omega)


/-- `Spec.Huffman.DecodeAssigned`, the statement the spec leaves to this task, for every table. -/
theorem decodeAssigned (lens : List Nat) : Spec.Huffman.DecodeAssigned lens := by
  intro hlegal hlen hcomplete i hi rest
  exact decodeSym_codeword lens hlegal hlen (Kraft.of_complete hcomplete) i hi rest

/-! ### Sequences of symbols -/

/-- The codewords of a symbol sequence one after the other: what `sendMTFValues` writes for the
symbols of a block that use one coding table (`compress.c:562-566`). -/
def encodeSyms (lens : List Nat) (syms : List Nat) : List Bool :=
  syms.flatMap (Spec.Huffman.codeword lens)

/-- Reads `n` symbols one after the other with the spec's `decodeSym`: the symbols and the bits
left, or `none` if one of the reads is not a symbol. -/
def decodeSyms (lens : List Nat) : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits =>
    match Spec.Huffman.decodeSym lens bits with
    | .sym s rest => (decodeSyms lens n rest).map fun p => (s :: p.1, p.2)
    | _ => none

/-- Encoding a symbol sequence and decoding as many symbols returns it, whatever follows. -/
theorem decodeSyms_encodeSyms (lens : List Nat) (hlegal : ∀ x ∈ lens, 1 ≤ x ∧ x ≤ 20)
    (hlen : lens.length ≤ 258) (hk : Kraft lens) (syms : List Nat)
    (hsyms : ∀ s ∈ syms, s < lens.length) (rest : List Bool) :
    decodeSyms lens syms.length (encodeSyms lens syms ++ rest) = some (syms, rest) := by
  induction syms with
  | nil => simp [encodeSyms, decodeSyms]
  | cons s t ih =>
    have hs : s < lens.length := hsyms s (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, x < lens.length := fun x hx => hsyms x (List.mem_cons_of_mem _ hx)
    have h := decodeSym_codeword lens hlegal hlen hk s hs (encodeSyms lens t ++ rest)
    have e : encodeSyms lens (s :: t) ++ rest =
        Spec.Huffman.codeword lens s ++ (encodeSyms lens t ++ rest) := by
      simp [encodeSyms]
    rw [List.length_cons, decodeSyms, e, h]
    simp only [ih ht, Option.map_some]

end Bzip2.Proofs.Huffman.Canonical
