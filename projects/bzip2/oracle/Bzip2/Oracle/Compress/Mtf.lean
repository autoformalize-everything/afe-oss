/-!
# Oracle: symbol map, move-to-front and RUNA/RUNB encoding

`makeMaps_e` and `generateMTFValues` of `compress.c:106-115` and `compress.c:120-231`.

Input: the BWT output (`block[ptr[i]-1]` for `i = 0 ..`, i.e. the last column of the sorted
rotations; the caller does the `ptr` indirection) and the symbol map `inUse` (256 flags,
`s->inUse`). Output: the symbols (`s->mtfv`) ending in `EOB = nInUse + 1`, and their
frequencies (`s->mtfFreq`, `nInUse + 2` entries).

Symbols: `RUNA = 0`, `RUNB = 1`, MTF index `j ≥ 1` as `j + 1`, `EOB = nInUse + 1`. A repeat of the
front byte is counted in `zPend` and written as a bijective base-2 number, least significant
digit first (`compress.c:170-188`, `compress.c:212-226`).
-/

namespace Bzip2.Oracle.Compress.Mtf

/-- Result of `generateMTFValues`. -/
structure MtfResult where
  /-- `s->mtfv[0 .. nMTF-1]`, the last one being `EOB`. -/
  syms : Array UInt16
  /-- `s->mtfFreq[0 .. nInUse+1]`. -/
  freq : Array Nat
  /-- `s->nInUse`. -/
  nInUse : Nat
  deriving Repr, BEq, Inhabited

/-- `s->inUse` for a block: which byte values occur in it (`bzlib.c:124`, `bzlib.c:223`,
`bzlib.c:238`). -/
def inUseOf (block : ByteArray) : Array Bool := Id.run do
  let mut u := Array.replicate 256 false
  for b in block do
    u := u.set! b.toNat true
  return u

/-- `makeMaps_e`: `unseqToSeq`, and `nInUse`. Unused byte values map to 0 (unspecified in C). -/
def makeMaps (inUse : Array Bool) : Array UInt8 × Nat := Id.run do
  let mut m := Array.replicate 256 (0 : UInt8)
  let mut n := 0
  for i in [0:256] do
    if inUse[i]! then
      m := m.set! i n.toUInt8
      n := n + 1
  return (m, n)

/-- Emits the pending zero run `zPend > 0` as RUNA/RUNB digits (`compress.c:174-186`). -/
private def flushRun (syms : Array UInt16) (freq : Array Nat) (zPend : Nat) :
    Array UInt16 × Array Nat := Id.run do
  let mut syms := syms
  let mut freq := freq
  let mut z := zPend - 1
  repeat
    let d := z % 2   -- 1: RUNB, 0: RUNA
    syms := syms.push d.toUInt16
    freq := freq.modify d (· + 1)
    if z < 2 then break
    z := (z - 2) / 2
  return (syms, freq)

/-- `generateMTFValues`. Every byte of `bwt` must be marked in `inUse`. -/
def generateMtf (bwt : ByteArray) (inUse : Array Bool) : MtfResult := Id.run do
  let (map, nInUse) := makeMaps inUse
  let eob := nInUse + 1
  let mut freq := Array.replicate (eob + 1) 0
  let mut syms : Array UInt16 := Array.mkEmpty (bwt.size + 1)
  let mut yy : Array UInt8 := Array.ofFn (n := nInUse) fun i => i.val.toUInt8
  let mut zPend := 0
  for b in bwt do
    let c := map[b.toNat]!
    if yy[0]! == c then
      zPend := zPend + 1
    else
      if zPend > 0 then
        (syms, freq) := flushRun syms freq zPend
        zPend := 0
      -- move `c` to the front; `j` is its old position (≥ 1)
      let mut j := 1
      while yy[j]! != c do
        j := j + 1
      let mut k := j
      while k > 0 do
        yy := yy.set! k yy[k-1]!
        k := k - 1
      yy := yy.set! 0 c
      syms := syms.push (j + 1).toUInt16
      freq := freq.modify (j + 1) (· + 1)
  if zPend > 0 then
    (syms, freq) := flushRun syms freq zPend
  syms := syms.push eob.toUInt16
  freq := freq.modify eob (· + 1)
  return { syms, freq, nInUse }

end Bzip2.Oracle.Compress.Mtf
