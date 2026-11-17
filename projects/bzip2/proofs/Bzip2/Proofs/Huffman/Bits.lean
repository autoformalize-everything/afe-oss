import Bzip2.Oracle.BitIO
import Bzip2.Proofs.Huffman.Loops
import Mathlib.Tactic.Ring

/-!
# Huffman proofs: the bit reader as a list of bits

The spec decodes from a `List Bool`; the oracle reads a `BitReader`. `bits r` is the list of
bits a reader has left: bit `p` of the input is bit `7 - p % 8` of byte `p / 8` (the first bit
read is the most significant, `decompress.c:43-51`). `readBit_eq` and `readBits_ok` say that
`BitReader.readBit` and `BitReader.readBits` take the first bit, or the first `n ≤ 32` bits,
of `bits r` and leave the reader at `bits r` without them; an input that is too short is
`Error.eof` and a width above 32 is `Error.param`, as the oracle's own doc says.

The loop of `readBits` is copied as `readBitsBody` (the proof checks the copy against the
definition) so that it can be argued about as a loop that ends: it ends because every pass takes
at least one bit.
-/

namespace Bzip2.Proofs.Huffman.Bits

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Proofs.Huffman.Loops

/-- Bit `p` of `data`, the bits of each byte taken most significant first. -/
def bitAt (data : ByteArray) (p : Nat) : Bool := (data.get! (p / 8)).toNat.testBit (7 - p % 8)

/-- The bits a reader has left, in reading order. -/
def bits (r : BitReader) : List Bool :=
  (List.range' r.pos (r.data.size * 8 - r.pos)).map (bitAt r.data)

/-- The number a list of bits spells, first bit most significant (the value `zvec` of the
decoder, `decompress.c:90-97`). -/
def val (l : List Bool) : Nat := l.foldl (fun a b => 2 * a + if b then 1 else 0) 0

/-- The number spelled by the `k` bits of `data` from bit `p` on. -/
def valAt (data : ByteArray) (p k : Nat) : Nat := val ((List.range' p k).map (bitAt data))

theorem bits_length (r : BitReader) : (bits r).length = r.remaining := by
  simp [bits, BitReader.remaining]

theorem bits_eq_nil_iff (r : BitReader) : bits r = [] ↔ r.atEnd = true := by
  rw [← List.length_eq_zero_iff, bits_length, BitReader.remaining, BitReader.atEnd]
  simp only [decide_eq_true_eq]
  omega

theorem val_cons (b : Bool) (l : List Bool) :
    val (b :: l) = (if b then 1 else 0) * 2 ^ l.length + val l := by
  have foldl_val : ∀ (l : List Bool) (a : Nat),
      l.foldl (fun a b => 2 * a + if b then 1 else 0) a = a * 2 ^ l.length + val l := by
    intro l
    induction l with
    | nil => intro a; simp [val]
    | cons b l ih =>
      intro a
      have h1 : (b :: l).foldl (fun a b => 2 * a + if b then 1 else 0) a =
          l.foldl (fun a b => 2 * a + if b then 1 else 0) (2 * a + if b then 1 else 0) := rfl
      have h2 : val (b :: l) = (if b then 1 else 0) * 2 ^ l.length + val l := by
        show l.foldl (fun a b => 2 * a + if b then 1 else 0) (2 * 0 + if b then 1 else 0) = _
        rw [ih]; simp
      rw [h1, ih, h2, List.length_cons, pow_succ]
      cases b <;> simp <;> ring
  show l.foldl (fun a b => 2 * a + if b then 1 else 0) (2 * 0 + if b then 1 else 0) = _
  rw [foldl_val]; simp

theorem val_append (l₁ l₂ : List Bool) : val (l₁ ++ l₂) = val l₁ * 2 ^ l₂.length + val l₂ := by
  induction l₁ with
  | nil => simp [val]
  | cons b l ih =>
    rw [List.cons_append, val_cons, val_cons, ih, List.length_append, pow_add]
    ring

theorem val_lt (l : List Bool) : val l < 2 ^ l.length := by
  induction l with
  | nil => simp [val]
  | cons b l ih =>
    rw [val_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem valAt_add (data : ByteArray) (p k j : Nat) :
    valAt data p (k + j) = valAt data p k * 2 ^ j + valAt data (p + k) j := by
  unfold valAt
  rw [← List.range'_append_1, List.map_append, val_append, List.length_map, List.length_range']

theorem valAt_lt (data : ByteArray) (p k : Nat) : valAt data p k < 2 ^ k := by
  have := val_lt ((List.range' p k).map (bitAt data))
  rw [List.length_map, List.length_range'] at this
  exact this

/-- Reading a byte's bits `q ..< q + t`, most significant first, is a shift and a mask. -/
theorem val_byte : ∀ b : Fin 256, ∀ q : Fin 8, ∀ t : Fin 9, q.1 + t.1 ≤ 8 →
    val ((List.range' q.1 t.1).map fun i => (b.1).testBit (7 - i)) =
      (b.1 >>> (8 - q.1 - t.1)) % 2 ^ t.1 := by
  decide +kernel

theorem valAt_byte (data : ByteArray) (p t : Nat) (ht : p % 8 + t ≤ 8) :
    valAt data p t = ((data.get! (p / 8)).toNat >>> (8 - p % 8 - t)) % 2 ^ t := by
  have hb : (data.get! (p / 8)).toNat < 256 := (data.get! (p / 8)).toNat_lt
  have h := val_byte ⟨(data.get! (p / 8)).toNat, hb⟩ ⟨p % 8, Nat.mod_lt _ (by decide)⟩
    ⟨t, by omega⟩ ht
  simp only at h
  rw [← h, valAt]
  congr 1
  rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi : i < t := List.mem_range.mp hi
  have h1 : (p + i) / 8 = p / 8 := by omega
  have h2 : (p + i) % 8 = p % 8 + i := by omega
  simp only [Function.comp, bitAt]
  rw [h1, h2]

theorem take_range' (s l n : Nat) : (List.range' s l).take n = List.range' s (min n l) := by
  rw [List.range'_eq_map_range, List.range'_eq_map_range, ← List.map_take, List.take_range]

theorem take_bits (r : BitReader) (n : Nat) (h : n ≤ r.remaining) :
    (bits r).take n = (List.range' r.pos n).map (bitAt r.data) := by
  rw [bits, ← List.map_take, take_range']
  congr 2
  rw [BitReader.remaining] at h
  omega

theorem drop_bits (r : BitReader) (n : Nat) (h : n ≤ r.remaining) :
    (bits r).drop n = bits { r with pos := r.pos + n } := by
  have h' : n ≤ r.data.size * 8 - r.pos := h
  simp only [bits]
  rw [← List.map_drop, List.drop_range']
  congr 2 <;> omega

theorem uint8_ne_zero (x : UInt8) : (x != 0) = decide (x.toNat ≠ 0) := by
  by_cases h : x = 0
  · subst h; simp
  · have : x.toNat ≠ 0 := fun h0 => h (UInt8.toNat_inj.mp (by simpa using h0))
    simp [h, this]

theorem uint8_testBit (b : UInt8) (k : Nat) (hk : k < 8) :
    ((b >>> k.toUInt8) &&& 1 != 0) = b.toNat.testBit k := by
  have h1 : ((b >>> k.toUInt8) &&& 1).toNat = 1 &&& (b.toNat >>> k) := by
    rw [UInt8.toNat_and, UInt8.toNat_shiftRight, Nat.and_comm]
    simp [Nat.mod_eq_of_lt hk]
  rw [uint8_ne_zero, h1, Nat.testBit]
  generalize 1 &&& (b.toNat >>> k) = m
  cases m <;> simp

/-- The oracle's `readBit` reads the first bit of `bits r`. -/
theorem readBit_eq (r : BitReader) (h : r.atEnd = false) :
    r.readBit = .ok (bitAt r.data r.pos, { r with pos := r.pos + 1 }) := by
  unfold BitReader.readBit
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  congr 2
  exact uint8_testBit _ _ (by omega)

/-- At the end of the input `readBit` fails with `Error.eof`. -/
theorem readBit_eof (r : BitReader) (h : r.atEnd = true) : r.readBit = .error .eof := by
  unfold BitReader.readBit
  simp [h]

theorem bits_cons (r : BitReader) (h : r.atEnd = false) :
    bits r = bitAt r.data r.pos :: bits { r with pos := r.pos + 1 } := by
  have h' : r.pos < r.data.size * 8 := by
    simp only [BitReader.atEnd, decide_eq_false_iff_not] at h; omega
  have := drop_bits r 1 (by rw [BitReader.remaining]; omega)
  rw [← this]
  simp only [bits] at *
  rw [show r.data.size * 8 - r.pos = (r.data.size * 8 - r.pos - 1) + 1 by omega,
    List.range'_succ, List.map_cons]
  rfl

/-- One pass of `readBits` on the shifted-in value: the bits `sh ..` of the byte, `take` of them,
are or-ed in below the `acc` bits (`UInt64` arithmetic, no wrap-around). -/
theorem uint64_step (acc : UInt64) (byte : UInt8) (take sh : Nat) (ht : take ≤ 8) (hsh : sh ≤ 8)
    (hacc : acc.toNat * 2 ^ take < 2 ^ 64) :
    ((acc <<< take.toUInt64) ||| ((byte.toUInt64 >>> sh.toUInt64) &&&
        ((1 <<< take.toUInt64) - 1))).toNat =
      acc.toNat * 2 ^ take + (byte.toNat >>> sh) % 2 ^ take := by
  have h64 : ∀ k, k < 64 → k.toUInt64.toNat = k := fun k hk => by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have ht64 := h64 take (by omega)
  have hsh64 := h64 sh (by omega)
  have hp : 2 ^ take ≤ 2 ^ 8 := Nat.pow_le_pow_right (by omega) ht
  have hp64 : 2 ^ take < 2 ^ 64 := by calc 2 ^ take ≤ 2 ^ 8 := hp
                                           _ < 2 ^ 64 := by decide
  have h1 : (1 <<< take.toUInt64 : UInt64).toNat = 2 ^ take := by
    rw [UInt64.toNat_shiftLeft, ht64, Nat.mod_eq_of_lt (by omega : take < 64)]
    show (1 <<< take) % 2 ^ 64 = 2 ^ take
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp64
  have h2 : ((1 <<< take.toUInt64) - 1 : UInt64).toNat = 2 ^ take - 1 := by
    have hle : (1 : UInt64) ≤ (1 <<< take.toUInt64) := by
      rw [UInt64.le_iff_toNat_le, h1]
      exact Nat.two_pow_pos take
    rw [UInt64.toNat_sub_of_le _ _ hle, h1]; rfl
  have h3 : (acc <<< take.toUInt64).toNat = acc.toNat * 2 ^ take := by
    rw [UInt64.toNat_shiftLeft, ht64, Nat.mod_eq_of_lt (by omega : take < 64), Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt hacc
  have h4 : ((byte.toUInt64 >>> sh.toUInt64) &&& ((1 <<< take.toUInt64) - 1)).toNat =
      (byte.toNat >>> sh) % 2 ^ take := by
    rw [UInt64.toNat_and, h2, UInt64.toNat_shiftRight, hsh64,
      Nat.mod_eq_of_lt (by omega : sh < 64), UInt8.toNat_toUInt64, Nat.and_two_pow_sub_one_eq_mod]
  rw [UInt64.toNat_or, h3, h4]
  have hlt : (byte.toNat >>> sh) % 2 ^ take < 2 ^ take := Nat.mod_lt _ (Nat.two_pow_pos take)
  have := Nat.shiftLeft_add_eq_or_of_lt hlt acc.toNat
  rw [Nat.shiftLeft_eq] at this
  exact this.symm

/-- The body of the `while` loop in `BitReader.readBits`: the state is the value so far, the bit
position and the number of bits still to read (`decompress.c:43-65` reads a byte at a time). -/
def readBitsBody (data : ByteArray) (_ : Unit) (s : UInt64 × Nat × Nat) :
    Id (ForInStep (UInt64 × Nat × Nat)) :=
  if s.2.2 > 0 then
    let byte := (data.get! (s.2.1 / 8)).toUInt64
    let avail := 8 - s.2.1 % 8
    let take := if s.2.2 < avail then s.2.2 else avail
    let bits := (byte >>> (avail - take).toUInt64) &&& ((1 <<< take.toUInt64) - 1)
    pure (ForInStep.yield ((s.1 <<< take.toUInt64) ||| bits, s.2.1 + take, s.2.2 - take))
  else pure (ForInStep.done s)

theorem readBits_eq_loop (r : BitReader) (n : Nat) (h32 : ¬ n > 32) (hr : ¬ n > r.remaining) :
    r.readBits n = (
      let s := forIn Lean.Loop.mk ((0, r.pos, n) : UInt64 × Nat × Nat) (readBitsBody r.data)
      Except.ok (s.1.toUInt32, { r with pos := s.2.1 })) := by
  unfold BitReader.readBits
  simp only [h32, hr, ite_false]
  rfl

/-- The loop of `readBits` takes the remaining bits, however they split over bytes. -/
theorem readBitsBody_spec (data : ByteArray) (n : Nat) (hn : n ≤ 32) :
    ∀ s : UInt64 × Nat × Nat,
      (s.2.2 ≤ n ∧ s.2.1 + s.2.2 ≤ data.size * 8 ∧ s.1.toNat < 2 ^ (n - s.2.2)) →
      (forIn Lean.Loop.mk s (readBitsBody data)).2.1 = s.2.1 + s.2.2 ∧
      (forIn Lean.Loop.mk s (readBitsBody data)).1.toNat =
        s.1.toNat * 2 ^ s.2.2 + valAt data s.2.1 s.2.2 := by
  intro s hs
  refine forIn_loop_rel (β := UInt64 × Nat × Nat)
    (fun s => s.2.2 ≤ n ∧ s.2.1 + s.2.2 ≤ data.size * 8 ∧ s.1.toNat < 2 ^ (n - s.2.2))
    (fun s r => r.2.1 = s.2.1 + s.2.2 ∧
      r.1.toNat = s.1.toNat * 2 ^ s.2.2 + valAt data s.2.1 s.2.2)
    (fun s => s.2.2) (readBitsBody data) ?_ ?_ s hs
  · intro b v _ h
    unfold readBitsBody at h
    split at h
    · cases h
    · have hb : b.2.2 = 0 := by omega
      have : v = b := by cases h; rfl
      subst this
      simp [hb, valAt, val]
  · intro b v hb h
    obtain ⟨hl, hp, hacc⟩ := hb
    unfold readBitsBody at h
    split at h
    · rename_i hpos
      have hv : v = ((b.1 <<< (if b.2.2 < 8 - b.2.1 % 8 then b.2.2 else 8 - b.2.1 % 8).toUInt64)
          ||| (((data.get! (b.2.1 / 8)).toUInt64 >>>
            (8 - b.2.1 % 8 - (if b.2.2 < 8 - b.2.1 % 8 then b.2.2 else 8 - b.2.1 % 8)).toUInt64) &&&
            ((1 <<< (if b.2.2 < 8 - b.2.1 % 8 then b.2.2 else 8 - b.2.1 % 8).toUInt64) - 1)),
          b.2.1 + (if b.2.2 < 8 - b.2.1 % 8 then b.2.2 else 8 - b.2.1 % 8),
          b.2.2 - (if b.2.2 < 8 - b.2.1 % 8 then b.2.2 else 8 - b.2.1 % 8)) := by
        injection h with h; exact h.symm
      generalize htk : (if b.2.2 < 8 - b.2.1 % 8 then b.2.2 else 8 - b.2.1 % 8) = tk at hv
      have h1 : 1 ≤ tk := by
        have : b.2.1 % 8 < 8 := Nat.mod_lt _ (by decide)
        split at htk <;> omega
      have h2 : tk ≤ b.2.2 := by split at htk <;> omega
      have h3 : tk ≤ 8 - b.2.1 % 8 := by split at htk <;> omega
      have hpow : 2 ^ (n - b.2.2) * 2 ^ tk = 2 ^ (n - (b.2.2 - tk)) := by
        rw [← pow_add]; congr 1; omega
      have hacc' : b.1.toNat * 2 ^ tk < 2 ^ (n - (b.2.2 - tk)) := by
        rw [← hpow]
        exact Nat.mul_lt_mul_of_pos_right hacc (Nat.two_pow_pos tk)
      have h32 : 2 ^ (n - (b.2.2 - tk)) ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hstep := uint64_step b.1 (data.get! (b.2.1 / 8)) tk (8 - b.2.1 % 8 - tk) (by omega)
        (by omega) (by
          have : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
          omega)
      have hbyte := valAt_byte data b.2.1 tk (by omega)
      have hacc2 : v.1.toNat = b.1.toNat * 2 ^ tk + valAt data b.2.1 tk := by
        rw [hv]; simp only; rw [hstep, hbyte]
      have hv1 : v.2.1 = b.2.1 + tk := by rw [hv]
      have hv2 : v.2.2 = b.2.2 - tk := by rw [hv]
      refine ⟨⟨by omega, by omega, ?_⟩, by omega, ?_⟩
      · rw [hacc2, hv2]
        have := valAt_lt data b.2.1 tk
        have h4 : (b.1.toNat + 1) * 2 ^ tk ≤ 2 ^ (n - (b.2.2 - tk)) := by
          rw [← hpow]
          exact Nat.mul_le_mul_right _ hacc
        rw [Nat.add_mul, Nat.one_mul] at h4
        omega
      · intro r hr
        obtain ⟨hr1, hr2⟩ := hr
        refine ⟨by rw [hr1, hv1, hv2]; omega, ?_⟩
        rw [hr2, hacc2, hv1, hv2]
        have hadd := valAt_add data b.2.1 tk (b.2.2 - tk)
        rw [show tk + (b.2.2 - tk) = b.2.2 by omega] at hadd
        rw [hadd, Nat.add_mul, Nat.mul_assoc, ← pow_add, show tk + (b.2.2 - tk) = b.2.2 by omega]
        ring
    · cases h

/-- `readBits` takes the first `0 < n ≤ 32` bits of `bits r` as a number, first bit most
significant, and moves the reader past them. -/
theorem readBits_ok (r : BitReader) (n : Nat) (hn0 : 0 < n) (hn : n ≤ 32)
    (hr : n ≤ r.remaining) :
    ∃ v : UInt32, r.readBits n = .ok (v, { r with pos := r.pos + n }) ∧
      v.toNat = val ((bits r).take n) := by
  have hrem : r.pos + n ≤ r.data.size * 8 := by
    rw [BitReader.remaining] at hr; omega
  have hr' : ¬ n > r.remaining := by omega
  rw [readBits_eq_loop r n (by omega) hr']
  have h := readBitsBody_spec r.data n hn ((0, r.pos, n) : UInt64 × Nat × Nat)
    ⟨Nat.le_refl n, by simpa using hrem, by simp⟩
  obtain ⟨h1, h2⟩ := h
  have h0 : (0 : UInt64).toNat = 0 := rfl
  simp only [h0, Nat.zero_mul, Nat.zero_add] at h2
  have hlt : valAt r.data r.pos n < 2 ^ 32 :=
    Nat.lt_of_lt_of_le (valAt_lt r.data r.pos n) (Nat.pow_le_pow_right (by omega) hn)
  refine ⟨(forIn Lean.Loop.mk ((0, r.pos, n) : UInt64 × Nat × Nat)
    (readBitsBody r.data)).1.toUInt32, ?_, ?_⟩
  · dsimp only
    rw [h1]
  · rw [UInt64.toNat_toUInt32, h2, Nat.mod_eq_of_lt (by simpa using hlt), take_bits r n hr]
    rfl

/-- `readBits` fails with `Error.eof` when fewer than `n ≤ 32` bits are left. -/
theorem readBits_eof (r : BitReader) (n : Nat) (hn : n ≤ 32) (hr : r.remaining < n) :
    r.readBits n = .error .eof := by
  unfold BitReader.readBits
  have : ¬ n > 32 := by omega
  simp [this, hr]

end Bzip2.Proofs.Huffman.Bits
