import Bzip2.Oracle.Compress.Bwt

/-! Unit tests of `Bzip2.Oracle.Compress.Bwt`: the forward BWT against a naive sort of all
rotations on small blocks, known examples, and the sizes of long blocks. -/

open Bzip2.Oracle.Compress.Bwt

namespace Bzip2.Test.CompressBwt

/-- Reference: sorts the rotation start indices by comparing the rotations as lists, ties by
index, and reads off the last column and the first row equal to rotation 0. -/
def naive (b : ByteArray) : ByteArray × Nat :=
  let n := b.size
  let rot (s : Nat) : List UInt8 := (List.range n).map fun i => b.get! ((s + i) % n)
  let idx := (List.range n).toArray.qsort fun x y =>
    rot x < rot y || (rot x == rot y && x < y)
  let out := idx.foldl (init := ByteArray.empty) fun o s => o.push (b.get! ((s + n - 1) % n))
  let orig := (idx.findIdx? fun s => rot s == rot 0).getD 0
  (out, orig)

/-- The `len`-byte block whose bytes are `250 + (seed-generated value mod alpha)`. -/
def sample (seed len alpha : Nat) : ByteArray := Id.run do
  let mut s := seed
  let mut b := ByteArray.empty
  for _ in [0:len] do
    s := (s * 1103515245 + 12345) % 2147483648
    b := b.push (250 + (s / 65536) % alpha).toUInt8
  return b

/-- Whether `bwt` agrees with `naive` on every sample with a length below 40 and alphabet of 1
to 4 symbols. -/
def agrees : Bool :=
  (List.range 40).all fun len =>
    (List.range 4).all fun a =>
      (List.range 3).all fun seed =>
        let b := sample (seed + 7 * len + a) len (a + 1)
        bwt b == naive b

#guard agrees

-- The empty block, and a single byte.
#guard bwt .empty == (.empty, 0)
#guard bwt (ByteArray.mk #[5]) == (ByteArray.mk #[5], 0)

-- "banana": rotations sorted are abanan, anaban, ananab, banana, nabana, nanaba.
#guard bwt "banana".toUTF8 == ("nnbaaa".toUTF8, 3)

-- Bytes are compared unsigned, as in C.
#guard bwt (ByteArray.mk #[0x80, 0x01]) == (ByteArray.mk #[0x80, 0x01], 1)

-- A periodic block: `origPtr` is the first row equal to rotation 0.
#guard bwt "abab".toUTF8 == ("bbaa".toUTF8, 0)
#guard bwt "baba".toUTF8 == ("bbaa".toUTF8, 2)

-- Long blocks, small enough for the interpreter: a run of one byte (the worst case for
-- comparison sorts, ⌈log₂ n⌉ rounds here) and pseudo-random bytes.
#guard (bwt (ByteArray.mk (Array.replicate 20000 7))).2 == 0
#guard (bwt (ByteArray.mk (Array.replicate 20000 7))).1.size == 20000
#guard (bwt (sample 1 20000 256)).1.size == 20000

end Bzip2.Test.CompressBwt
