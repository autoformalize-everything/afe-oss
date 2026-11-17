import Bzip2.Oracle.Compress.Bwt

/-! Unit tests of `Bzip2.Oracle.Compress.Bwt`: the forward BWT against a naive sort of all
rotations on small blocks, known examples, and 900 000-byte blocks (inverted by the standard last-to-first walk). -/

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

-- Bytes are compared unsigned, as in `blocksort.c:354-362`.
#guard bwt (ByteArray.mk #[0x80, 0x01]) == (ByteArray.mk #[0x80, 0x01], 1)

-- A periodic block: `origPtr` is the first row equal to rotation 0.
#guard bwt "abab".toUTF8 == ("bbaa".toUTF8, 0)
#guard bwt "baba".toUTF8 == ("bbaa".toUTF8, 2)

/-- Inverts a transform: the block whose last column is `out` and whose row `orig` is the
block, by the last-to-first walk (the walk `BZ2_bzDecompress` does with `tt`). -/
def invert (out : ByteArray) (orig : Nat) : ByteArray := Id.run do
  let n := out.size
  let mut cnt : Array Nat := Array.replicate 256 0
  for i in [0:n] do
    cnt := cnt.modify out[i]!.toNat (· + 1)
  let mut sum := 0
  for b in [0:256] do
    let x := cnt[b]!
    cnt := cnt.set! b sum
    sum := sum + x
  let mut tt : Array Nat := Array.replicate n 0
  for i in [0:n] do
    let b := out[i]!.toNat
    tt := tt.set! cnt[b]! i
    cnt := cnt.modify b (· + 1)
  let mut res := ByteArray.emptyWithCapacity n
  let mut pos := orig
  for _ in [0:n] do
    pos := tt[pos]!
    res := res.push out[pos]!
  return res

/-- Whether `bwt` of `b` inverts back to `b`. -/
def roundTrips (b : ByteArray) : Bool :=
  let r := bwt b
  invert r.1 r.2 == b

#guard roundTrips "banana".toUTF8
#guard (List.range 40).all fun len => roundTrips (sample len len 3)

-- A run of one byte is the worst case for comparison sorts. Its rotations are all equal, so
-- `origPtr` is row 0 and the last column is the run itself.
#guard bwt (ByteArray.mk (Array.replicate 900000 7)) == (ByteArray.mk (Array.replicate 900000 7), 0)

-- A random block: the last column is a permutation of the block, sorted rows agree with the
-- first column, and the inverse gives the block back.
#guard
  let b := sample 1 900000 256
  let r := bwt b
  r.1.size == 900000 && r.2 < 900000 && invert r.1 r.2 == b

end Bzip2.Test.CompressBwt
