import Bzip2.Spec.Crc
import Bzip2.Oracle.Crc

/-!
# CRC correspondence

The oracle's table lookup implements `BZ_UPDATE_CRC` (`bzlib_private.h:167-172`),
with the initial value and final complement from `bzlib_private.h:157-165`.
The combined CRC rotates and xors each block CRC in `compress.c:606-608`, starting
at zero in `bzlib.c:192`.

The bridge uses `UInt32.toBitVec` for states and `UInt8.toBitVec` for bytes.
The byte-array proof covers the default full-array range of the oracle's CRC function.
-/

namespace Bzip2.Proofs.Crc

private theorem table_correct : ∀ i : Fin 256,
    (Oracle.Crc.table[i.val]!).toBitVec =
      Spec.Crc.crcUpdate 0 (UInt8.ofNat i.val).toBitVec := by
  decide +kernel

private theorem ofNat_mod_256 (x : Nat) :
    BitVec.ofNat 8 (x % 256) = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

private theorem table_lookup (c : UInt32) (b : UInt8) :
    (Oracle.Crc.table[((c >>> 24) ^^^ b.toUInt32).toNat &&& 0xff]!).toBitVec =
      Spec.Crc.crcUpdate 0 ((c.toBitVec >>> 24).truncate 8 ^^^ b.toBitVec) := by
  let i := ((c >>> 24) ^^^ b.toUInt32).toNat &&& 0xff
  have hi : i < 256 := by
    exact Nat.and_lt_two_pow _ (by decide : 0xff < 2 ^ 8)
  have hb : (UInt8.ofNat i).toBitVec =
      (c.toBitVec >>> 24).truncate 8 ^^^ b.toBitVec := by
    change BitVec.ofNat 8 i = _
    simp only [i, show 0xff = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    rw [ofNat_mod_256]
    change BitVec.ofNat 8 (c >>> 24 ^^^ b.toUInt32).toBitVec.toNat = _
    rw [BitVec.ofNat_toNat]
    rw [UInt32.toBitVec_xor, BitVec.setWidth_xor, UInt32.toBitVec_shiftRight,
      UInt8.toBitVec_toUInt32]
    simp
  have h := table_correct ⟨i, hi⟩
  simpa only [hb] using h

private theorem bit_linear (x y : BitVec 32) :
    Spec.Crc.crcBit (x ^^^ y) = Spec.Crc.crcBit x ^^^ Spec.Crc.crcBit y := by
  unfold Spec.Crc.crcBit
  rw [BitVec.msb_xor, BitVec.shiftLeft_xor_distrib]
  cases hx : x.msb <;> cases hy : y.msb <;>
    simp_all <;> grind [BitVec.xor_assoc, BitVec.xor_comm, BitVec.xor_self]

private theorem iterate_linear (n : Nat) (x y : BitVec 32) :
    (Nat.iterate Spec.Crc.crcBit n) (x ^^^ y) =
      (Nat.iterate Spec.Crc.crcBit n) x ^^^
        (Nat.iterate Spec.Crc.crcBit n) y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [bit_linear, ih]

private theorem low_msb (lo : BitVec 24) (n : Nat) (hn : n < 8) :
    ((0#8 ++ lo) <<< n).msb = false := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]
  have hi : 24 ≤ 31 - n := by omega
  have hnot : ¬ 31 - n < 24 := by omega
  simp only [show (31 : Nat) < 32 by decide, decide_true, Bool.true_and,
    show ¬ (31 : Nat) < n by omega, decide_false, Bool.not_false]
  rw [BitVec.getLsbD_append]
  simp [hnot]

private theorem low_iter (lo : BitVec 24) : ∀ n ≤ 8,
    (Nat.iterate Spec.Crc.crcBit n) (0#8 ++ lo) = (0#8 ++ lo) <<< n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro hn
    have hlt : n < 8 := by omega
    rw [Function.iterate_succ_apply', ih (by omega)]
    rw [show Spec.Crc.crcBit ((0#8 ++ lo) <<< n) =
        ((0#8 ++ lo) <<< n) <<< 1 by
      simp [Spec.Crc.crcBit, low_msb lo n hlt]]
    rw [← BitVec.shiftLeft_add]

private theorem shift_eq (hi : BitVec 8) (lo : BitVec 24) :
    (hi ++ lo) <<< 8 = (0#8 ++ lo) <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i h
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases hi8 : i < 8
  · simp [hi8]
  · have h24 : i - 8 < 24 := by omega
    simp only [show i < 32 by omega, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
    simp [h24]

private theorem split_eq (c : BitVec 32) : c = ((c >>> 24).truncate 8 ++ c.truncate 24) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h24 : i < 24
  · simp [h24, BitVec.truncate_eq_setWidth]
  · have h8 : i - 24 < 8 := by omega
    simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    rw [show 24 + (i - 24) = i by omega, ite_eq_right h24]
    simp only [h8, decide_true, Bool.true_and]

private theorem top_eq (b : BitVec 8) : b.zeroExtend 32 <<< 24 = b ++ 0#24 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft]
  by_cases h24 : i < 24
  · simp [h24]
  · have h8 : i - 24 < 8 := by omega
    simp [h24, h8, hi, show i - 24 < 32 by omega]

private theorem gethigh (hi : BitVec 8) (lo : BitVec 24) :
    ((hi ++ lo) >>> 24).truncate 8 = hi := by
  rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ushiftRight_eq_extractLsb]
  exact BitVec.extractLsb'_append_eq_left

private theorem xor_split (hi b : BitVec 8) (lo : BitVec 24) :
    (hi ++ lo) ^^^ (b ++ 0#24) =
      ((hi ^^^ b) ++ 0#24) ^^^ (0#8 ++ lo) := by
  rw [BitVec.xor_append, BitVec.xor_append]
  simp

private theorem bit_formula (c : BitVec 32) (b : BitVec 8) :
    Spec.Crc.crcUpdate c b =
      (c <<< 8) ^^^ Spec.Crc.crcUpdate 0 ((c >>> 24).truncate 8 ^^^ b) := by
  let hi : BitVec 8 := (c >>> 24).truncate 8
  let lo : BitVec 24 := c.truncate 24
  have hc : c = hi ++ lo := split_eq c
  rw [hc]
  unfold Spec.Crc.crcUpdate
  rw [top_eq b, gethigh hi lo, top_eq (hi ^^^ b)]
  rw [xor_split hi b lo, iterate_linear, low_iter lo 8 (by decide), shift_eq hi lo]
  simp only [Nat.reduceAdd, Function.iterate_succ,
    Function.comp_apply, BitVec.ofNat_eq_ofNat, BitVec.zero_xor]
  exact BitVec.xor_comm _ _

private theorem updateByte_eq_spec (c : UInt32) (b : UInt8) :
    (Oracle.Crc.updateByte c b).toBitVec = Spec.Crc.crcUpdate c.toBitVec b.toBitVec := by
  rw [bit_formula]
  unfold Oracle.Crc.updateByte
  rw [UInt32.toBitVec_xor, UInt32.toBitVec_shiftLeft, table_lookup]
  simp

private theorem get_bang_eq (data : ByteArray) (i : Nat) (h : i < data.size) :
    data.get! i = data[i]! := by
  simp [getElem!_pos data i h, getElem!_pos data.data i (by simpa using h),
    ByteArray.get!, ByteArray.getElem_eq_getElem_data]

private theorem toList_loop_eq (data : ByteArray) (i : Nat) (acc : List UInt8)
    (hi : i ≤ data.size) :
    ByteArray.toList.loop data i acc =
      acc.reverse ++ ((List.range' i (data.size - i)).map fun j => data[j]!) := by
  generalize hn : data.size - i = n
  induction n using Nat.strong_induction_on generalizing i acc with
  | ind n ih =>
    by_cases hlt : i < data.size
    · have hprev : data.size - (i + 1) < n := by omega
      have hnext : i + 1 ≤ data.size := by omega
      rw [ByteArray.toList.loop.eq_1, ite_eq_left hlt]
      rw [get_bang_eq data i hlt]
      rw [ih (data.size - (i + 1)) hprev (i + 1) (data[i]! :: acc) hnext rfl]
      rw [← hn]
      rw [show data.size - i = (data.size - (i + 1)) + 1 by omega]
      rw [List.range'_succ]
      simp only [List.map_cons, List.reverse_cons]
      simp [List.append_assoc]
    · have hn0 : n = 0 := by omega
      rw [ByteArray.toList.loop.eq_1, ite_eq_right hlt, hn0]
      simp

private theorem toList_eq_range (data : ByteArray) :
    data.toList = (List.range data.size).map fun i => data[i]! := by
  unfold ByteArray.toList
  rw [toList_loop_eq data 0 [] (Nat.zero_le _)]
  simp only [List.reverse_nil, List.nil_append, Nat.sub_zero, List.range_eq_range']

private theorem update_eq_fold (c : UInt32) (data : ByteArray) :
    Oracle.Crc.update c data = data.toList.foldl Oracle.Crc.updateByte c := by
  rw [toList_eq_range]
  simp [Oracle.Crc.update, List.forIn_pure_yield_eq_foldl,
    List.range_eq_range', List.foldl_map]

private theorem foldl_state (bytes : List UInt8) (c : UInt32) :
    (bytes.foldl Oracle.Crc.updateByte c).toBitVec =
      (bytes.map UInt8.toBitVec).foldl Spec.Crc.crcUpdate c.toBitVec := by
  induction bytes generalizing c with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, updateByte_eq_spec]

/-- The oracle's table-driven CRC of every byte array equals the bitwise specification. -/
theorem crc32_eq_spec (data : ByteArray) :
    (Oracle.Crc.crc32 data).toBitVec =
      Spec.Crc.crc32 (data.toList.map UInt8.toBitVec) := by
  unfold Oracle.Crc.crc32 Spec.Crc.crc32 Oracle.Crc.finalise
  rw [update_eq_fold, UInt32.toBitVec_not, foldl_state]
  rfl

/-- The oracle's combined-CRC step equals the specification's rotation and xor. -/
theorem combine_eq_spec (combined blockCrc : UInt32) :
    (Oracle.Crc.combine combined blockCrc).toBitVec =
      Spec.Crc.combineCrc combined.toBitVec blockCrc.toBitVec := by
  unfold Oracle.Crc.combine Spec.Crc.combineCrc
  rw [UInt32.toBitVec_xor, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight]
  simp [BitVec.rotateLeft_def]

private theorem foldl_combine (blocks : List UInt32) (combined : UInt32) :
    (blocks.foldl Oracle.Crc.combine combined).toBitVec =
      (blocks.map UInt32.toBitVec).foldl Spec.Crc.combineCrc combined.toBitVec := by
  induction blocks generalizing combined with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, combine_eq_spec]

/-- Folding the oracle's combination over block CRCs gives the specified stream CRC. -/
theorem streamCrc_eq_spec (blocks : List UInt32) :
    (blocks.foldl Oracle.Crc.combine 0).toBitVec =
      Spec.Crc.streamCrc (blocks.map UInt32.toBitVec) := by
  rw [foldl_combine]
  rfl

end Bzip2.Proofs.Crc
