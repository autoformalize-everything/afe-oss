/-!
# Oracle: forward Burrows-Wheeler transform

`Bzip2.Oracle.Compress.Bwt.bwt block` returns the last column of the sorted rotations of `block`
(what `BZ2_blockSort` leaves in `ptr` and `compress.c` turns into `block[ptr[i]-1]`, see
`blocksort.c:1031-1089`) and `origPtr`, the row of rotation 0 (`blocksort.c:1084-1088`).

Algorithm: prefix doubling on cyclic shifts, each round two stable counting sorts, so
O(n log n) in the worst case, with no comparison sorts; runs of equal bytes need ⌈log₂ n⌉ rounds.

Tie-breaking: rotations are compared as byte strings (unsigned bytes, as in C). Equal rotations
occur exactly when `block` is periodic; they are interchangeable in the output column. `origPtr`
is the row of the *first* of the rows equal to rotation 0, i.e. the smallest row whose rotation
equals rotation 0. This need not match the C library's `origPtr` on periodic blocks (that is
`oracle/compress/byte-exact`); the inverse transform recovers `block` either way.
-/

namespace Bzip2.Oracle.Compress.Bwt

/-- Sorted order of the rotations of `block` (row ↦ start index), together with the equivalence
class of each start index (equal rotations have equal classes; classes increase with rank). -/
def sortRotations (block : ByteArray) : Array Nat × Array Nat := Id.run do
  let n := block.size
  if n == 0 then return (#[], #[])
  -- initial: sort by first byte
  let mut cnt : Array Nat := Array.replicate 256 0
  for i in [0:n] do
    let b := block.get! i |>.toNat
    cnt := cnt.modify b (· + 1)
  let mut sum := 0
  for b in [0:256] do
    let c := cnt[b]!
    cnt := cnt.set! b sum
    sum := sum + c
  let mut p : Array Nat := Array.replicate n 0
  for i in [0:n] do
    let b := block.get! i |>.toNat
    p := p.set! cnt[b]! i
    cnt := cnt.modify b (· + 1)
  let mut c : Array Nat := Array.replicate n 0
  let mut classes := 1
  for i in [1:n] do
    if block.get! p[i]! != block.get! p[i-1]! then classes := classes + 1
    c := c.set! p[i]! (classes - 1)
  let mut k := 1
  while k < n && classes < n do
    -- order by second key: shift the current order by k
    let mut pn : Array Nat := Array.replicate n 0
    for i in [0:n] do
      let v := p[i]!
      pn := pn.set! i (if v >= k then v - k else v + n - k)
    -- stable counting sort by first key
    let mut cn : Array Nat := Array.replicate classes 0
    for i in [0:n] do
      cn := cn.modify c[pn[i]!]! (· + 1)
    let mut s := 0
    for j in [0:classes] do
      let x := cn[j]!
      cn := cn.set! j s
      s := s + x
    let mut p2 : Array Nat := Array.replicate n 0
    for i in [0:n] do
      let v := pn[i]!
      let key := c[v]!
      p2 := p2.set! cn[key]! v
      cn := cn.modify key (· + 1)
    p := p2
    -- new classes
    let mut c2 : Array Nat := Array.replicate n 0
    let mut cls := 1
    for i in [1:n] do
      let a := p[i]!
      let b := p[i-1]!
      let a2 := if a + k >= n then a + k - n else a + k
      let b2 := if b + k >= n then b + k - n else b + k
      if c[a]! != c[b]! || c[a2]! != c[b2]! then cls := cls + 1
      c2 := c2.set! a (cls - 1)
    c := c2
    classes := cls
    k := k * 2
  return (p, c)

/-- The forward BWT of `block`: the last column of the sorted rotations and `origPtr`.
See the module doc for the tie-breaking on periodic blocks. The empty block gives `(empty, 0)`. -/
def bwt (block : ByteArray) : ByteArray × Nat := Id.run do
  let n := block.size
  if n == 0 then return (.empty, 0)
  let (p, c) := sortRotations block
  let mut out := ByteArray.emptyWithCapacity n
  let mut orig := n
  for i in [0:n] do
    let v := p[i]!
    out := out.push (block.get! (if v == 0 then n - 1 else v - 1))
    if orig == n && c[v]! == c[0]! then orig := i
  return (out, orig)

end Bzip2.Oracle.Compress.Bwt
