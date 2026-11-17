import Batteries.Tactic.OpenPrivate
import Bzip2.Oracle.Decompress.Huffman
import Bzip2.Proofs.Huffman.Bits
import Bzip2.Proofs.Huffman.DecodeTables
import Bzip2.Proofs.Huffman.Stop

/-!
# Huffman proofs: the oracle reads a symbol as the spec does

`Oracle.Decompress.Huffman.decodeSym` (`GET_MTF_VAL`, `decompress.c:74-102`) reads `minLen` bits
and then one bit at a time while the value is above `limit[zn]`; the spec's `decodeSym` does the
same on a list of bits, with the tables as functions of the lengths. `decode_eq_spec` says the
two agree on every table of a stream: the same symbol and the same bits left; `Error.data` where
the spec says `dataError`; `Error.eof` where it says `needMoreInput`; and the spec never says
`staleEntry`.

This covers the incomplete and over-subscribed tables the format can carry: nothing here
assumes the lengths form a prefix code, only the table facts of `DecodeTables` and the stopping
argument of `Stop`.
-/

namespace Bzip2.Proofs.Huffman.Decode

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Huffman
  Bzip2.Proofs.Huffman.Bits Bzip2.Proofs.Huffman.DecodeTables Bzip2.Proofs.Huffman.Stop
  Bzip2.Proofs.Huffman.Loops

open private extend from Bzip2.Oracle.Decompress.Huffman

/-- The oracle's outcome of reading a symbol from the reader `r` against the spec's `Result`:
the same symbol and the same bits left (in the same input) for `sym`; `Error.data` for
`dataError`; `Error.eof` for `needMoreInput`; nothing matches `staleEntry`. -/
def Matches (r : BitReader) : Spec.Huffman.Result → Except Error (Nat × BitReader) → Prop
  | .sym s rest, out => ∃ r', out = .ok (s, r') ∧ r'.data = r.data ∧ bits r' = rest
  | .dataError, out => ∃ d, out = .error (.data d)
  | .needMoreInput, out => out = .error .eof
  | .staleEntry, _ => False

theorem Matches.of_data_eq {r r' : BitReader} (h : r'.data = r.data)
    {res : Spec.Huffman.Result} {out : Except Error (Nat × BitReader)}
    (hm : Matches r' res out) : Matches r res out := by
  cases res with
  | sym s rest =>
    obtain ⟨r'', h1, h2, h3⟩ := hm
    exact ⟨r'', h1, h2.trans h, h3⟩
  | dataError => exact hm
  | needMoreInput => exact hm
  | staleEntry => exact hm

/-- The part of `decodeSym` after the first `minLen` bits: the loop and the lookup in `perm`. -/
def finish (t : Tables) (zn : Nat) (zvec : Int) (r : BitReader) :
    Except Error (Nat × BitReader) :=
  match extend t zn zvec r with
  | .error e => .error e
  | .ok (zn, zvec, r) =>
    let idx := zvec - t.base[zn]!
    if idx < 0 || idx ≥ maxAlphaSize then
      .error (.data "Huffman: index outside perm")
    else
      .ok (t.perm[idx.toNat]!, r)

theorem decodeSym_eq (t : Tables) (r : BitReader) :
    decodeSym t r = (match r.readBits t.minLen with
      | .error e => .error e
      | .ok (v, r) => finish t t.minLen v.toNat r) := by
  unfold decodeSym finish
  rfl

/-- Past 20 bits `extend` fails with `Error.data` (`decompress.c:91-92`). -/
theorem extend_big (t : Tables) (zn : Nat) (zvec : Int) (r : BitReader) (h : zn > 20) :
    ∃ d, extend t zn zvec r = .error (.data d) := by
  rw [extend]
  simp [longestCode, h]

/-- `extend` stops at `zn` when `zvec ≤ limit[zn]` (`decompress.c:93`). -/
theorem extend_stop (t : Tables) (zn : Nat) (zvec : Int) (r : BitReader) (h : ¬ zn > 20)
    (hs : zvec ≤ t.limit[zn]!) : extend t zn zvec r = .ok (zn, zvec, r) := by
  rw [extend]
  simp only [longestCode, h, hs]
  simp

/-- Otherwise `extend` reads one more bit (`decompress.c:94-97`). -/
theorem extend_step (t : Tables) (zn : Nat) (zvec : Int) (r : BitReader) (h : ¬ zn > 20)
    (hs : ¬ zvec ≤ t.limit[zn]!) :
    extend t zn zvec r = (match r.readBit with
      | .error e => .error e
      | .ok (b, r') => extend t (zn + 1) (zvec * 2 + if b then 1 else 0) r') := by
  rw [extend]
  simp only [longestCode, h, hs]
  rfl

/-- The loop of `GET_MTF_VAL` agrees in the oracle and in the spec from every state the loop can
be in, with `k = 21 - zn` bits to go and enough fuel. -/
theorem finish_matches (lens : List Nat) (t : Tables) (hne : lens ≠ [])
    (hlegal : ∀ x ∈ lens, 1 ≤ x ∧ x ≤ 20) (hle : lens.length ≤ maxAlphaSize)
    (hlimit : ∀ n, t.limit[n]! = Spec.Huffman.limit lens n)
    (hbase : ∀ n < maxCodeLen, t.base[n]! = Spec.Huffman.base lens n)
    (hperm : ∀ k < (Spec.Huffman.perm lens).length,
      t.perm[k]! = (Spec.Huffman.perm lens).getD k 0)
    (hplen : (Spec.Huffman.perm lens).length = lens.length) :
    ∀ k zn zvec (r : BitReader) fuel, 21 - zn = k → k + 1 ≤ fuel → Inv lens zn zvec →
      Matches r (Spec.Huffman.loop lens fuel zn zvec (bits r)) (finish t zn (zvec : Int) r) := by
  intro k
  induction k with
  | zero =>
    intro zn zvec r fuel hk hfuel hinv
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hz : zn > 20 := by omega
    obtain ⟨d, hd⟩ := extend_big t zn zvec r hz
    have h1 : Spec.Huffman.loop lens (f + 1) zn zvec (bits r) = .dataError := by
      simp only [Spec.Huffman.loop, hz, ↓reduceIte]
    rw [h1]
    exact ⟨d, by unfold finish; rw [hd]⟩
  | succ k ih =>
    intro zn zvec r fuel hk hfuel hinv
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hz : ¬ zn > 20 := by omega
    by_cases hstop : (zvec : Int) ≤ Spec.Huffman.limit lens zn
    · have hts : (zvec : Int) ≤ t.limit[zn]! := by rw [hlimit]; exact hstop
      have hext := extend_stop t zn zvec r hz hts
      obtain ⟨hznM, hi0, hi1⟩ := index_lt lens hne hlegal zn zvec hinv hstop
      have hmc : maxCodeLen = 23 := rfl
      have hbz : t.base[zn]! = Spec.Huffman.base lens zn := hbase zn (by omega)
      have hidx_lt : ((zvec : Int) - Spec.Huffman.base lens zn).toNat <
          (Spec.Huffman.perm lens).length := by omega
      have hcond : ¬ ((zvec : Int) - Spec.Huffman.base lens zn < 0 ∨
          (zvec : Int) - Spec.Huffman.base lens zn ≥ 258) := by
        have : maxAlphaSize = 258 := rfl
        omega
      have hsome := List.getElem?_eq_getElem hidx_lt
      have hs1 : Spec.Huffman.loop lens (f + 1) zn zvec (bits r) =
          .sym ((Spec.Huffman.perm lens)[((zvec : Int) - Spec.Huffman.base lens zn).toNat])
            (bits r) := by
        simp only [Spec.Huffman.loop, hz, hstop, ↓reduceIte, hcond, hsome]
      have hs2 : finish t zn zvec r =
          .ok ((Spec.Huffman.perm lens)[((zvec : Int) - Spec.Huffman.base lens zn).toNat], r) := by
        unfold finish
        rw [hext]
        simp only [hbz]
        have hc2 : ¬ (decide ((zvec : Int) - Spec.Huffman.base lens zn < 0) = true ∨
            decide ((zvec : Int) - Spec.Huffman.base lens zn ≥ ↑maxAlphaSize) = true) := by
          have : maxAlphaSize = 258 := rfl
          simp only [decide_eq_true_eq, this]
          exact_mod_cast hcond
        simp only [Bool.or_eq_true, hc2, ↓reduceIte]
        rw [hperm _ hidx_lt, List.getD_eq_getElem?_getD, hsome]
        rfl
      rw [hs1, hs2]
      exact ⟨r, rfl, rfl, rfl⟩
    · have hts : ¬ (zvec : Int) ≤ t.limit[zn]! := by rw [hlimit]; exact hstop
      have hs1 : Spec.Huffman.loop lens (f + 1) zn zvec (bits r) =
          (match bits r with
            | [] => .needMoreInput
            | b :: rest =>
              Spec.Huffman.loop lens f (zn + 1) (2 * zvec + if b then 1 else 0) rest) := by
        simp only [Spec.Huffman.loop, hz, hstop, ↓reduceIte]
        rfl
      by_cases hend : r.atEnd = true
      · have hb : bits r = [] := (bits_eq_nil_iff r).mpr hend
        have hs2 : finish t zn zvec r = .error .eof := by
          unfold finish
          rw [extend_step t zn zvec r hz hts, readBit_eof r hend]
        rw [hs1, hs2, hb]
        rfl
      · have hend' : r.atEnd = false := by simpa using hend
        have hb := bits_cons r hend'
        have hrb := readBit_eq r hend'
        have hs2 : finish t zn zvec r =
            finish t (zn + 1) ((zvec : Int) * 2 + if bitAt r.data r.pos then 1 else 0)
              { r with pos := r.pos + 1 } := by
          unfold finish
          rw [extend_step t zn zvec r hz hts, hrb]
        have hih := ih (zn + 1) (2 * zvec + if bitAt r.data r.pos then 1 else 0)
          { r with pos := r.pos + 1 } f (by omega) (by omega) (hinv.step hstop _)
        have hcast : (((2 * zvec + if bitAt r.data r.pos then 1 else 0 : Nat)) : Int) =
            (zvec : Int) * 2 + if bitAt r.data r.pos then 1 else 0 := by
          cases bitAt r.data r.pos <;> simp <;> omega
        rw [hcast] at hih
        rw [hs1, hs2, hb]
        exact Matches.of_data_eq rfl hih

/-- On every table of a stream (1 to 258 code lengths, each in `1 .. 20`, whether or not they form
a prefix code), reading a symbol with the oracle's tables is reading it with the spec's. -/
theorem decode_eq_spec (length : Array UInt8) (hne : 0 < length.size)
    (hle : length.size ≤ maxAlphaSize) (hlegal : ∀ l ∈ length, 1 ≤ l.toNat ∧ l.toNat ≤ 20)
    (r : BitReader) :
    Matches r (Spec.Huffman.decodeSym (lensOf length) (bits r))
      (decodeSym (tablesOf length) r) := by
  have hl : ∀ x ∈ lensOf length, 1 ≤ x ∧ x ≤ 20 := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact hlegal l (Array.mem_def.mpr hl)
  have hne' : lensOf length ≠ [] := by
    intro h
    have := lensOf_length length
    rw [h] at this
    simp only [List.length_nil] at this
    omega
  have hlen : (lensOf length).length ≤ maxAlphaSize := by rw [lensOf_length]; exact hle
  obtain ⟨h1, h2, h3, h4, h5⟩ := tablesOf_eq_spec length hne hle hl
  have hplen := perm_length (lensOf length) hne' hl
  obtain ⟨hm1, hmM, hM20, _⟩ := minLen_maxLen (lensOf length) hne' hl
  rw [decodeSym_eq, h1]
  unfold Spec.Huffman.decodeSym
  by_cases hshort : (bits r).length < Spec.Huffman.minLen (lensOf length)
  · simp only [hshort, ↓reduceIte]
    have hr : r.remaining < Spec.Huffman.minLen (lensOf length) := by
      rw [← bits_length r]; exact hshort
    rw [readBits_eof r _ (by omega) hr]
    rfl
  · simp only [hshort, ↓reduceIte]
    have hrem : Spec.Huffman.minLen (lensOf length) ≤ r.remaining := by
      rw [← bits_length r]; omega
    obtain ⟨v, hv, hvn⟩ := readBits_ok r _ (by omega) (by omega) hrem
    rw [hv]
    have hmat := finish_matches (lensOf length) (tablesOf length) hne' hl hlen h2 h3 h5 hplen
      (21 - Spec.Huffman.minLen (lensOf length)) (Spec.Huffman.minLen (lensOf length)) v.toNat
      { r with pos := r.pos + Spec.Huffman.minLen (lensOf length) } 23 rfl (by omega)
      ⟨Nat.le_refl _, Or.inl rfl⟩
    rw [← drop_bits r _ hrem] at hmat
    have e : List.foldl (fun a b => 2 * a + if b = true then 1 else 0) 0
        (List.take (Spec.Huffman.minLen (lensOf length)) (bits r)) = v.toNat := hvn.symm
    rw [e]
    exact Matches.of_data_eq rfl hmat

/-- `ofLengths` builds exactly `tablesOf length` for the lengths of a stream. -/
theorem ofLengths_eq (length : Array UInt8) (hne : 0 < length.size)
    (hle : length.size ≤ maxAlphaSize) (hlegal : ∀ l ∈ length, 1 ≤ l.toNat ∧ l.toNat ≤ 20) :
    ofLengths length = .ok (tablesOf length) := by
  unfold ofLengths tablesOf
  have h1 : length.isEmpty = false :=
    Array.isEmpty_eq_false_iff.mpr (fun h => by rw [h] at hne; simp at hne)
  have h2 : decide (length.size > maxAlphaSize) = false := by
    rw [decide_eq_false_iff_not]; omega
  have h3 : (length.any fun l => l == 0 || decide (l.toNat > longestCode)) = false := by
    rw [Array.any_eq_false]
    intro i hi
    have h := hlegal length[i] (Array.getElem_mem hi)
    have hl : longestCode = 20 := rfl
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, hl]
    refine ⟨fun h0 => ?_, by omega⟩
    rw [h0] at h
    simp at h
  simp [h1, h2, h3]

end Bzip2.Proofs.Huffman.Decode
