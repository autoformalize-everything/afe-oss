import Bzip2.Oracle.Compress.Mtf

/-!
# MTF and RUNA/RUNB unit tests

Expected symbol sequences and frequencies for small BWT columns, short runs, and a long run.
The encoding follows `compress.c:160-231`.
-/

namespace Bzip2.Test.CompressMtf

open Bzip2.Oracle.Compress.Mtf

/-- Whether the encoder returns the expected symbols, frequencies, and used byte count. -/
def check (bwt : ByteArray) (syms freq : List Nat) (nInUse : Nat) : Bool :=
  let r := generateMtf bwt (inUseOf bwt)
  r.syms.toList.map (·.toNat) == syms && r.freq.toList == freq && r.nInUse == nInUse

/-- A block containing `n` copies of `b`. -/
def rep (b : UInt8) (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n b)

#guard check "banana".toUTF8 [2, 2, 3, 2, 2, 2, 4] [0, 0, 5, 1, 1] 3
#guard check (ByteArray.mk #[97, 110, 110, 98, 0, 97, 97])
  [2, 4, 0, 4, 4, 4, 0, 5] [2, 0, 1, 0, 4, 1] 4
#guard check "abracadabra".toUTF8 [0, 2, 5, 3, 4, 2, 5, 2, 5, 5, 3, 6]
  [1, 0, 3, 2, 1, 4, 1] 5

-- A front-byte run followed by a different byte, for lengths one through six.
#guard check (rep 120 1 ++ rep 121 1) [0, 2, 3] [1, 0, 1, 1] 2
#guard check (rep 120 2 ++ rep 121 1) [1, 2, 3] [0, 1, 1, 1] 2
#guard check (rep 120 3 ++ rep 121 1) [0, 0, 2, 3] [2, 0, 1, 1] 2
#guard check (rep 120 4 ++ rep 121 1) [1, 0, 2, 3] [1, 1, 1, 1] 2
#guard check (rep 120 5 ++ rep 121 1) [0, 1, 2, 3] [1, 1, 1, 1] 2
#guard check (rep 120 6 ++ rep 121 1) [1, 1, 2, 3] [0, 2, 1, 1] 2

-- A one-value block exercises final run flushing and EOB placement.
#guard check (rep 120 1) [0, 2] [1, 0, 1] 1
#guard check (rep 120 2) [1, 2] [0, 1, 1] 1
#guard check (rep 120 3) [0, 0, 2] [2, 0, 1] 1
#guard check (rep 120 4) [1, 0, 2] [1, 1, 1] 1
#guard check (rep 120 5) [0, 1, 2] [1, 1, 1] 1
#guard check (rep 120 6) [1, 1, 2] [0, 2, 1] 1
#guard check (rep 0 1000) [1, 0, 0, 1, 0, 1, 1, 1, 1, 2] [3, 6, 1] 1
#guard check (rep 0 999 ++ rep 1 1) [0, 0, 0, 1, 0, 1, 1, 1, 1, 2, 3]
  [4, 5, 1, 1] 2
#guard check .empty [1] [0, 1] 0

end Bzip2.Test.CompressMtf
