import Bzip2.Spec.Crc
import Bzip2.Oracle.Crc

/-!
# The table-driven CRC is the specified CRC

`Bzip2.Oracle.Crc` computes the block CRC as the C library does: one table lookup per byte,
`BZ_UPDATE_CRC` (`bzlib_private.h:167-172`), from the initial value `BZ_INITIALISE_CRC`
(`bzlib_private.h:157-160`) to the complement `BZ_FINALISE_CRC` (`bzlib_private.h:162-165`).
`Bzip2.Spec.Crc` defines the same CRC bit by bit, without a table. This module proves the two
equal, on every input, and does the same for the combined CRC: the rotation and xor of each
block CRC into the stream CRC, which `BZ2_compressBlock` does at `compress.c:607-608` (from the
zero set in `BZ2_bzCompressInit`, `bzlib.c:192`) and `BZ2_bzDecompress` at `bzlib.c:832-835`
(from the zero set in `BZ2_bzDecompressInit`, `bzlib.c:515`).

* `updateByte_eq_spec`: one table lookup is the specification's eight bit steps.
* `update_slice_eq_spec`, `crc32_slice_eq_spec`: the oracle's `update` and `crc32` over any slice
  `data[start, stop)` of a byte array.
* `crc32_eq_spec`: the oracle's `crc32` of a whole byte array (the defaults `start := 0` and
  `stop := data.size`).
* `combine_eq_spec`, `streamCrc_eq_spec`: the combined CRC, for one block and for a list of them.

Choices made here. The oracle computes with `UInt32` and `UInt8`, the specification with
`BitVec 32` and `BitVec 8`; the statements relate them through `UInt32.toBitVec` and
`UInt8.toBitVec`. A `ByteArray` is related to the specification's byte list through
`ByteArray.toList`, and the slice `data[start, stop)` is
`(data.toList.drop start).take (stop - start)`.

Edge cases. The C macros see one byte at a time, so the slice and its clamping belong to the
oracle (see `Bzip2.Oracle.Crc`): a `stop` beyond the end of the array is clamped to the end, and
a `start` that is not below the clamped `stop` gives the empty slice. `List.drop` and `List.take`
clamp in the same way, so the slice statements hold for every `start` and `stop`. The oracle
masks the table index with `0xff`; the index `(crc >> 24) ^ byte` of `BZ_UPDATE_CRC` is below 256
already, so the mask changes nothing.
-/

namespace Bzip2.Proofs.Crc

/-! ### The table

Entry `i` of the oracle's table is the specification's byte step applied to the state `0` and the
byte `i`: `table_correct` evaluates all 256 entries in the kernel. `table_lookup` shows that the
entry `updateByte` looks up is the one for the top byte of the state xor the input byte. -/

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

/-! ### The byte step splits at the top byte

A bit step of the specification is linear for xor, and so are eight of them. Split the state into
its top byte and its low 24 bits. The top byte xor the input byte goes through the eight steps as
it would from the state `0`: that is the table entry. The low 24 bits meet a zero top bit at each
of the eight steps, so they are only shifted left by 8. `bit_formula` is the result:
`crcUpdate c b = (c <<< 8) ^^^ crcUpdate 0 (top byte of c ^^^ b)`. -/

private theorem bit_linear (x y : BitVec 32) :
    Spec.Crc.crcBit (x ^^^ y) = Spec.Crc.crcBit x ^^^ Spec.Crc.crcBit y := by
  unfold Spec.Crc.crcBit
  rw [BitVec.msb_xor, BitVec.shiftLeft_xor_distrib]
  grind [BitVec.xor_assoc, BitVec.xor_comm, BitVec.xor_self]

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

private theorem truncate_ushiftRight_append (hi : BitVec 8) (lo : BitVec 24) :
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
  rw [top_eq b, truncate_ushiftRight_append hi lo, top_eq (hi ^^^ b)]
  rw [xor_split hi b lo, iterate_linear, low_iter lo 8 (by decide), shift_eq hi lo]
  simp only [Nat.reduceAdd, Function.iterate_succ,
    Function.comp_apply, BitVec.ofNat_eq_ofNat, BitVec.zero_xor]
  exact BitVec.xor_comm _ _

/-- One step of the oracle's table-driven CRC equals the specification's eight bit steps
(`BZ_UPDATE_CRC`, `bzlib_private.h:167-172`). -/
theorem updateByte_eq_spec (c : UInt32) (b : UInt8) :
    (Oracle.Crc.updateByte c b).toBitVec = Spec.Crc.crcUpdate c.toBitVec b.toBitVec := by
  rw [bit_formula]
  unfold Oracle.Crc.updateByte
  rw [UInt32.toBitVec_xor, UInt32.toBitVec_shiftLeft, table_lookup]
  simp

private theorem foldl_state (bytes : List UInt8) (c : UInt32) :
    (bytes.foldl Oracle.Crc.updateByte c).toBitVec =
      (bytes.map UInt8.toBitVec).foldl Spec.Crc.crcUpdate c.toBitVec := by
  induction bytes generalizing c with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih, updateByte_eq_spec]

/-! ### Byte arrays

`ByteArray.toList` is a loop over `get!`, and the oracle's `update` is a `for` loop over the
indices of the slice. Both are reduced to the list `(data.toList.drop start).take (stop - start)`
and a fold over it. -/

private theorem toList_loop (data : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.toList.loop data i acc = acc.reverse ++ data.data.toList.drop i := by
  fun_induction ByteArray.toList.loop data i acc with
  | case1 i r h ih =>
    have hi : i < data.data.size := h
    have hd := List.drop_eq_getElem_cons (l := data.data.toList) (i := i) (by simpa using hi)
    rw [ih, hd]
    simp [ByteArray.get!, getElem!_pos data.data i hi]
  | case2 i r h =>
    rw [List.drop_eq_nil_of_le (by simpa using h)]
    simp

private theorem toList_eq_data (data : ByteArray) : data.toList = data.data.toList := by
  rw [ByteArray.toList, toList_loop]
  simp

private theorem slice_eq (data : ByteArray) (start stop : Nat) :
    (List.range' start (min stop data.size - start)).map (fun i => data[i]!) =
      (data.toList.drop start).take (stop - start) := by
  apply List.ext_getElem
  · simp [toList_eq_data]
    omega
  · intro j h1 _
    have hj : j < min stop data.size - start := by simpa using h1
    have hlt : start + j < data.size := by omega
    simp [toList_eq_data, getElem!_pos data (start + j) hlt, ByteArray.getElem_eq_getElem_data]

private theorem update_eq_foldl (c : UInt32) (data : ByteArray) (start stop : Nat) :
    Oracle.Crc.update c data start stop =
      ((data.toList.drop start).take (stop - start)).foldl Oracle.Crc.updateByte c := by
  rw [← slice_eq]
  simp [Oracle.Crc.update, List.forIn_pure_yield_eq_foldl, List.foldl_map]

/-- The oracle's CRC state after the slice `data[start, stop)` is the specification's fold of
`crcUpdate` over the bytes of that slice, for every `start` and `stop`. -/
theorem update_slice_eq_spec (c : UInt32) (data : ByteArray) (start stop : Nat) :
    (Oracle.Crc.update c data start stop).toBitVec =
      (((data.toList.drop start).take (stop - start)).map UInt8.toBitVec).foldl
        Spec.Crc.crcUpdate c.toBitVec := by
  rw [update_eq_foldl, foldl_state]

/-- The oracle's CRC of the slice `data[start, stop)` equals the specification's CRC of the bytes
of that slice, for every `start` and `stop`. -/
theorem crc32_slice_eq_spec (data : ByteArray) (start stop : Nat) :
    (Oracle.Crc.crc32 data start stop).toBitVec =
      Spec.Crc.crc32 (((data.toList.drop start).take (stop - start)).map UInt8.toBitVec) := by
  unfold Oracle.Crc.crc32 Spec.Crc.crc32 Oracle.Crc.finalise
  rw [UInt32.toBitVec_not, update_slice_eq_spec]
  rfl

/-- The oracle's CRC of a whole byte array equals the specification's CRC of its bytes. -/
theorem crc32_eq_spec (data : ByteArray) :
    (Oracle.Crc.crc32 data).toBitVec =
      Spec.Crc.crc32 (data.toList.map UInt8.toBitVec) := by
  rw [crc32_slice_eq_spec, toList_eq_data, List.drop_zero, Nat.sub_zero,
    List.take_of_length_le (by simp)]

/-- The oracle's combined-CRC step equals the specification's rotation and xor
(`compress.c:607-608`). -/
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
