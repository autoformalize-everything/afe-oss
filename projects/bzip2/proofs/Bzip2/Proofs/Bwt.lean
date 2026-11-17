import Bzip2.Spec.Bwt
import Bzip2.Oracle.Decompress.Block

/-!
# The BWT inverse walk

The decoder checks `origPtr` against the block length (`decompress.c:497-498`), builds the
inverse links (`decompress.c:565-570`), then starts at the link of `origPtr`
(`decompress.c:572`). This module relates the non-randomised `BZ_GET_FAST` step to the spec's
walk, provided the table has the specified low bytes and links. The table is represented by
the decoder's `Array UInt32`; the spec uses a list of bytes.

The table construction and forward prefix-doubling sort remain to be proved.
-/

namespace Bzip2.Proofs.Bwt

open Bzip2

/-- A decoder table whose low byte is the BWT last column and whose high bits are the
specified inverse links at every in-range row. -/
def TableMatches (L : List UInt8) (tt : Array UInt32) : Prop :=
  tt.size = L.length ∧ ∀ i, i < L.length →
    (tt[i]! &&& 0xff).toUInt8 = L.getD i 0 ∧
      (tt[i]! >>> 8).toNat = Spec.Bwt.next L i

/-- The non-randomised BWT walk, using the oracle's `Walk.next` step without RLE1. -/
def inverseWalk (tt : Array UInt32) : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, t =>
    let (b, w) := Oracle.Decompress.Block.Walk.next tt false
      { tPos := t, used := 0, rand := Oracle.Decompress.Block.Rand.init }
    b :: inverseWalk tt k w.tPos

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

end Bzip2.Proofs.Bwt
