import Bzip2.Spec.Bwt
import Bzip2.Oracle.Decompress.Block
import Mathlib.Data.List.Rotate

/-!
# The BWT inverse walk

The decoder checks `origPtr` against the block length (`decompress.c:497-498`), builds the
inverse links (`decompress.c:565-570`), then starts at the link of `origPtr`
(`decompress.c:572`). This module relates the non-randomised `BZ_GET_FAST` step to the spec's
walk, provided the table has the specified low bytes and links. The table is represented by
the decoder's `Array UInt32`; the spec uses a list of bytes.

The table construction and forward prefix-doubling sort remain to be proved. Independently,
every nonempty block has at least one valid original row in the spec's sorted rotations.
-/

namespace Bzip2.Proofs.Bwt

open Bzip2

/-- A decoder table whose low byte is the BWT last column and whose high bits are the
specified inverse links at every in-range row. -/
def TableMatches (L : List UInt8) (tt : Array UInt32) : Prop :=
  tt.size = L.length ∧ ∀ i, i < L.length →
    (tt[i]! &&& 0xff).toUInt8 = L.getD i 0 ∧
      (tt[i]! >>> 8).toNat = Spec.Bwt.next L i

/-- The low byte of a decoder table entry. -/
def lowByte (x : UInt32) : UInt8 := (x &&& 0xff).toUInt8

/-- Two decoder tables have the same length and low bytes at every index. -/
private def LowBytesEqual (raw cur : Array UInt32) : Prop :=
  cur.size = raw.size ∧
    ∀ (j : Nat), (cur[j]?).map lowByte = (raw[j]?).map lowByte

private theorem lowByte_or_shift (x y : UInt32) :
    lowByte (x ||| (y <<< 8)) = lowByte x := by
  have hs : (y <<< 8).toUInt8 = 0 := by
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp [UInt32.toBitVec_toUInt8]
  simp [lowByte, UInt32.toUInt8_and, UInt32.toUInt8_or, hs]

private theorem lowBytesEqual_modify (raw cur : Array UInt32) (idx : Nat) (y : UInt32)
    (h : LowBytesEqual raw cur) :
    LowBytesEqual raw (cur.modify idx (· ||| (y <<< 8))) := by
  constructor
  · simpa only [Array.size_modify] using h.1
  intro j
  rw [Array.getElem?_modify]
  by_cases hij : idx = j
  · subst idx
    simp only [↓reduceIte, Option.map_map]
    simpa only [Function.comp_def, lowByte_or_shift, Option.map_id] using h.2 j
  · simp only [hij, ↓reduceIte]
    exact h.2 j

/-- One iteration of the decoder's link construction (`decompress.c:565-570`). -/
private def linkStep (i : Nat) (s : Array UInt32 × Array Nat) :
    Array UInt32 × Array Nat :=
  let uc := (s.1[i]! &&& 0xff).toNat
  (s.1.modify s.2[uc]! (· ||| (i.toUInt32 <<< 8)), s.2.modify uc (· + 1))

private theorem linkStep_lowBytesEqual (raw : Array UInt32) (i : Nat)
    (s : Array UInt32 × Array Nat) (h : LowBytesEqual raw s.1) :
    LowBytesEqual raw (linkStep i s).1 := by
  exact lowBytesEqual_modify raw s.1 _ _ h

private theorem linkLoop_lowBytesEqual (raw : Array UInt32) (l : List Nat)
    (s : Array UInt32 × Array Nat) (h : LowBytesEqual raw s.1) :
    LowBytesEqual raw ((forIn l s fun i s => pure (ForInStep.yield (linkStep i s)) :
      Id (Array UInt32 × Array Nat)).1) := by
  induction l generalizing s with
  | nil => simpa
  | cons i l ih =>
    simpa [List.forIn_cons] using ih (linkStep i s) (linkStep_lowBytesEqual raw i s h)

private theorem links_lowBytesEqual (raw : Array UInt32) (c : Array Nat) :
    LowBytesEqual raw (Oracle.Decompress.Block.links raw c) := by
  unfold Oracle.Decompress.Block.links
  simp only [Id.run_bind, Id.run_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply linkLoop_lowBytesEqual raw _ (raw, c)
  exact ⟨rfl, by intro k; rfl⟩

/-- Building the decoder's inverse links preserves the table size. -/
theorem links_size (raw : Array UInt32) (c : Array Nat) :
    (Oracle.Decompress.Block.links raw c).size = raw.size :=
  (links_lowBytesEqual raw c).1

/-- Building the decoder's inverse links preserves every byte of the BWT last column.
The C update also writes only above the low byte (`decompress.c:565-570`). -/
theorem links_low_byte (raw : Array UInt32) (c : Array Nat) (j : Nat) :
    ((Oracle.Decompress.Block.links raw c)[j]?).map lowByte =
      (raw[j]?).map lowByte :=
  (links_lowBytesEqual raw c).2 j

/-- At an in-range row, link construction leaves the last-column byte unchanged. -/
theorem links_low_byte_get (raw : Array UInt32) (c : Array Nat) (j : Nat)
    (hj : j < raw.size) :
    lowByte ((Oracle.Decompress.Block.links raw c)[j]!) = lowByte (raw[j]!) := by
  have hl : j < (Oracle.Decompress.Block.links raw c).size := by
    simpa only [links_size] using hj
  have h := links_low_byte raw c j
  rw [Array.getElem?_eq_some_getElem! _ _ hl,
    Array.getElem?_eq_some_getElem! _ _ hj] at h
  exact Option.some.inj (by simpa only [Option.map_some] using h)

/-- The non-randomised BWT walk, using the oracle's `Walk.next` step without RLE1. -/
def inverseWalk (tt : Array UInt32) : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, t =>
    let (b, w) := Oracle.Decompress.Block.Walk.next tt false
      { tPos := t, used := 0, rand := Oracle.Decompress.Block.Rand.init }
    b :: inverseWalk tt k w.tPos

/-- The inverse walk emits one byte per step, even if the table is malformed. -/
theorem inverseWalk_length (tt : Array UInt32) (k t : Nat) :
    (inverseWalk tt k t).length = k := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => simp [inverseWalk, ih]

private theorem next_lt (L : List UInt8) (hL : 0 < L.length) (i : Nat) :
    Spec.Bwt.next L i < L.length := by
  unfold Spec.Bwt.next
  cases hf : (List.range L.length).find? (fun j => Spec.Bwt.slot L j == i) with
  | none => simpa [hf] using hL
  | some j =>
    have hm : j ∈ List.range L.length := List.mem_of_find?_eq_some hf
    simpa only [hf, Option.getD_some, List.mem_range] using hm

/-- A table with the spec's bytes and links gives the spec's walk at any valid start row. -/
theorem decode_eq_spec (L : List UInt8) (tt : Array UInt32) (k t : Nat)
    (hL : 0 < L.length) (hm : TableMatches L tt) (ht : t < L.length) :
    inverseWalk tt k t = Spec.Bwt.walk L k t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    obtain ⟨hb, hn⟩ := hm.2 t ht
    simp only [inverseWalk, Spec.Bwt.walk, Oracle.Decompress.Block.Walk.next,
      Bool.false_eq_true, ↓reduceIte]
    rw [hb, hn]
    exact congrArg (List.cons (L.getD t 0))
      (ih (Spec.Bwt.next L t) (next_lt L hL t))

/-- At a valid `origPtr`, the oracle's non-randomised inverse walk agrees with the spec's
decoder when `links` has the spec's bytes and links. -/
theorem decode_bwt (L : List UInt8) (p : Nat) (raw : Array UInt32) (c : Array Nat)
    (hp : Spec.Bwt.ValidInput L p)
    (hm : TableMatches L (Oracle.Decompress.Block.links raw c)) :
    inverseWalk (Oracle.Decompress.Block.links raw c) L.length
      (((Oracle.Decompress.Block.links raw c)[p]! >>> 8).toNat) =
        Spec.Bwt.decodeBwt L p := by
  have hL : 0 < L.length := Nat.lt_of_le_of_lt (Nat.zero_le p) hp
  have hn := (hm.2 p hp).2
  rw [hn]
  exact decode_eq_spec L (Oracle.Decompress.Block.links raw c) L.length
    (Spec.Bwt.next L p) hL hm
    (next_lt L hL p)

/-- The low-byte premise for decoding can be checked on the raw table, before links are built. -/
theorem decode_bwt_of_high_links (L : List UInt8) (p : Nat) (raw : Array UInt32)
    (c : Array Nat) (hp : Spec.Bwt.ValidInput L p)
    (hsize : raw.size = L.length)
    (hbytes : ∀ i, i < L.length → lowByte (raw[i]!) = L.getD i 0)
    (hnext : ∀ i, i < L.length →
      ((Oracle.Decompress.Block.links raw c)[i]! >>> 8).toNat = Spec.Bwt.next L i) :
    inverseWalk (Oracle.Decompress.Block.links raw c) L.length
      (((Oracle.Decompress.Block.links raw c)[p]! >>> 8).toNat) =
        Spec.Bwt.decodeBwt L p := by
  apply decode_bwt L p raw c hp
  constructor
  · simpa only [links_size] using hsize
  · intro i hi
    constructor
    · change lowByte ((Oracle.Decompress.Block.links raw c)[i]!) = L.getD i 0
      rw [links_low_byte_get raw c i (by rw [hsize]; exact hi)]
      exact hbytes i hi
    · exact hnext i hi

/-- The oracle rejects an out-of-range `origPtr` before constructing the inverse table
(`decompress.c:497-498`). -/
theorem output_invalid_origPtr (h : Oracle.Decompress.Header.Header)
    (b : Oracle.Decompress.Symbols.Block) (hp : b.tt.size ≤ h.origPtr) :
    Oracle.Decompress.Block.output h b =
      .error (.data "Block: origPtr not below nblock") := by
  simp [Oracle.Decompress.Block.output, hp]
  rfl

/-- An empty last column is rejected by the oracle's `origPtr` check. -/
theorem output_empty (h : Oracle.Decompress.Header.Header)
    (b : Oracle.Decompress.Symbols.Block) (hb : b.tt.isEmpty) :
    Oracle.Decompress.Block.output h b =
      .error (.data "Block: origPtr not below nblock") := by
  apply output_invalid_origPtr
  have h0 : b.tt.size = 0 := Array.isEmpty_iff_size_eq_zero.mp hb
  omega

/-- The specification's inverse is correct for a one-byte block. -/
theorem inverse_singleton (x : UInt8) :
    Spec.Bwt.IsOrigPtr [x] 0 ∧
      Spec.Bwt.decodeBwt (Spec.Bwt.bwt [x]) 0 = [x] := by
  simp [Spec.Bwt.IsOrigPtr, Spec.Bwt.decodeBwt, Spec.Bwt.walk, Spec.Bwt.next,
    Spec.Bwt.slot, Spec.Bwt.cftab, Spec.Bwt.bwt, Spec.Bwt.sortedRotations,
    Spec.Bwt.rotation, List.rotate]

/-- The spec's last column has one byte for each rotation. -/
theorem bwt_length (b : List UInt8) : (Spec.Bwt.bwt b).length = b.length := by
  simp [Spec.Bwt.bwt, Spec.Bwt.sortedRotations]

/-- A pointer to the original rotation passes the decoder's range check. -/
theorem origPtr_valid (b : List UInt8) (p : Nat) (hp : Spec.Bwt.IsOrigPtr b p) :
    Spec.Bwt.ValidInput (Spec.Bwt.bwt b) p := by
  simpa only [Spec.Bwt.ValidInput, bwt_length] using hp.1

/-- Every nonempty block occurs among its sorted rotations, at a valid original row. -/
theorem exists_origPtr (b : List UInt8) (hb : 0 < b.length) :
    ∃ p, Spec.Bwt.IsOrigPtr b p := by
  have hm : b ∈ Spec.Bwt.sortedRotations b := by
    unfold Spec.Bwt.sortedRotations
    rw [List.mem_insertionSort, List.mem_map]
    exact ⟨0, List.mem_range.mpr hb, by simp [Spec.Bwt.rotation]⟩
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp hm
  obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hp
  refine ⟨p, ?_, hp⟩
  simpa [Spec.Bwt.sortedRotations] using hbound

/-- The spec's forward transform of a nonempty block forms a valid BWT pair. -/
theorem bwt_isBwtPair (b : List UInt8) (hb : 0 < b.length) :
    ∃ p, Spec.Bwt.IsBwtPair (Spec.Bwt.bwt b) p := by
  obtain ⟨p, hp⟩ := exists_origPtr b hb
  exact ⟨p, b, rfl, hp⟩

/-- Correctness of the spec's inverse also makes that inverse unique. -/
theorem inverse_unique_of_correct (hc : Spec.Bwt.InverseCorrect) :
    Spec.Bwt.InverseUnique := by
  intro L p b b' hb hb'
  obtain ⟨hL, hp⟩ := hb
  obtain ⟨hL', hp'⟩ := hb'
  have h₁ := (hc b p hp).2
  have h₂ := (hc b' p hp').2
  rw [hL] at h₁
  rw [hL'] at h₂
  exact h₁.symm.trans h₂

end Bzip2.Proofs.Bwt
