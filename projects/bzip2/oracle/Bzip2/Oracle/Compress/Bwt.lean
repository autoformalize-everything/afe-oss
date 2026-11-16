/-!
# Oracle: forward Burrows-Wheeler transform

`Bzip2.Oracle.Compress.Bwt.bwt block` returns the last column of the sorted rotations of `block`.
`BZ2_blockSort` leaves the sorted order in `ptr` (`blocksort.c:1025-1029`); compression reads
the preceding byte for each entry (`compress.c:163-167`). It also returns `origPtr`, the row of
rotation 0 (`blocksort.c:1083-1088`).

Algorithm: prefix doubling on cyclic shifts, shifting the current order and then using a stable
counting sort on the first key each round. It takes O(n log n) time in the worst case, with no
comparison sorts; runs of equal bytes need ⌈log₂ n⌉ rounds.

Tie-breaking: rotations are compared as byte strings (unsigned bytes, as in `blocksort.c:354-362`).
Equal rotations occur exactly when `block` is periodic; they are interchangeable in the output
column. `origPtr` is the first row whose rotation equals rotation 0. This may differ from the C
library's `origPtr` on periodic blocks, which is the remit of `oracle/compress/byte-exact`.
The inverse transform recovers `block` either way.
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
