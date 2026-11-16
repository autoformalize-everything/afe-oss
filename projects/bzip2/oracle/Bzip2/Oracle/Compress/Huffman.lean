/-!
# Oracle: code lengths, tables and selectors

Chooses the Huffman coding tables and selectors of one block as `sendMTFValues` does
(`compress.c:273-277` table count, `compress.c:283-316` initial partition, `compress.c:322-451`
refinement and selectors, `compress.c:480-492` codes), with `BZ2_hbMakeCodeLengths`
(`huffman.c:63-148`) and `BZ2_hbAssignCodes` (`huffman.c:152-166`). All arithmetic is the C's
(integer division, heap tie order). The input is the block's MTF/RLE2 symbol sequence, ending
with EOB.

Choices: counts, lengths and codes are `Nat`, the C's `Int32`/`UChar` values never overflow
(weights stay below `2^31` for blocks of at most 900000 symbols). `parent[k] = -1` is stored as
`0`, as node numbers start at 1. The C's fast path for six tables and full groups
(`compress.c:359-386`, `compress.c:410-427`) computes the same costs and counts as the slow
path (`compress.c:388-393`, `compress.c:429-432`; each cost is at most `50 * 17`, below the
16-bit packing limit), so only the slow path is written. The C's `AssertH` checks
(`compress.c:272`, `compress.c:455-459`, `compress.c:488-489`) are preconditions here.
-/

namespace Bzip2.Oracle.Compress.Huffman

/-- `BZ_G_SIZE`: symbols per selector group (`bzlib_private.h:122`). -/
def groupSize : Nat := 50
/-- `BZ_N_ITERS`: refinement iterations (`bzlib_private.h:123`). -/
def numIters : Nat := 4
/-- `BZ_N_GROUPS`: maximum number of coding tables (`bzlib_private.h:121`). -/
def numGroups : Nat := 6

/-- The maximum code length passed to `BZ2_hbMakeCodeLengths` by `sendMTFValues`
(`compress.c:447-451`). -/
def maxCodeLen : Nat := 17

/-- Heap state of `BZ2_hbMakeCodeLengths` (`huffman.c:75-77`); arrays are indexed from 1,
entry 0 a sentinel. -/
private structure HS where
  heap : Array Nat
  weight : Array Nat
  nHeap : Nat

/-- `UPHEAP(z)` (`huffman.c:33-42`). -/
private def upHeap (heap weight : Array Nat) (z : Nat) : Array Nat := Id.run do
  let mut heap := heap
  let mut zz := z
  let tmp := heap[zz]!
  while weight[tmp]! < weight[heap[zz / 2]!]! do
    heap := heap.set! zz heap[zz / 2]!
    zz := zz / 2
  heap.set! zz tmp

/-- `DOWNHEAP(z)` (`huffman.c:44-59`). -/
private def downHeap (heap weight : Array Nat) (nHeap z : Nat) : Array Nat := Id.run do
  let mut heap := heap
  let mut zz := z
  let tmp := heap[zz]!
  repeat
    let mut yy := zz * 2
    if yy > nHeap then break
    if yy < nHeap && weight[heap[yy + 1]!]! < weight[heap[yy]!]! then yy := yy + 1
    if weight[tmp]! < weight[heap[yy]!]! then break
    heap := heap.set! zz heap[yy]!
    zz := yy
  heap.set! zz tmp

/-- `BZ2_hbMakeCodeLengths` (`huffman.c:63-148`): code lengths for `freq`, with zero counts
treated as 1 (`huffman.c:79-80`). Nodes are merged smallest two first, with the C's heap tie
order (`huffman.c:91-110`); while some length exceeds `maxLen` (`huffman.c:114-123`) the weights
are replaced by `1 + w / 2` and the tree rebuilt (`huffman.c:142-146`). Requires
`0 < freq.size ≤ 258`. -/
partial def makeCodeLengths (freq : Array Nat) (maxLen : Nat) : Array Nat := Id.run do
  let alphaSize := freq.size
  let mut weight : Array Nat := Array.replicate (alphaSize * 2 + 2) 0
  for i in [0:alphaSize] do
    weight := weight.set! (i + 1) ((if freq[i]! == 0 then 1 else freq[i]!) <<< 8)
  let mut len : Array Nat := Array.replicate alphaSize 0
  repeat
    let mut nNodes := alphaSize
    let mut nHeap := 0
    let mut heap : Array Nat := Array.replicate (alphaSize + 2) 0
    -- parent: -1 is encoded as 0 (node numbers start at 1; 0 is the sentinel, parent -2).
    let mut parent : Array Nat := Array.replicate (alphaSize * 2 + 2) 0
    weight := weight.set! 0 0
    for i in [1:alphaSize + 1] do
      nHeap := nHeap + 1
      heap := heap.set! nHeap i
      heap := upHeap heap weight nHeap
    while nHeap > 1 do
      let n1 := heap[1]!
      heap := heap.set! 1 heap[nHeap]!
      nHeap := nHeap - 1
      heap := downHeap heap weight nHeap 1
      let n2 := heap[1]!
      heap := heap.set! 1 heap[nHeap]!
      nHeap := nHeap - 1
      heap := downHeap heap weight nHeap 1
      nNodes := nNodes + 1
      parent := (parent.set! n1 nNodes).set! n2 nNodes
      let w1 := weight[n1]!
      let w2 := weight[n2]!
      weight := weight.set! nNodes
        (((w1 &&& 0xffffff00) + (w2 &&& 0xffffff00)) ||| (1 + max (w1 &&& 0xff) (w2 &&& 0xff)))
      nHeap := nHeap + 1
      heap := heap.set! nHeap nNodes
      heap := upHeap heap weight nHeap
    let mut tooLong := false
    for i in [1:alphaSize + 1] do
      let mut j := 0
      let mut k := i
      while parent[k]! != 0 do
        k := parent[k]!
        j := j + 1
      len := len.set! (i - 1) j
      if j > maxLen then tooLong := true
    if !tooLong then break
    for i in [1:alphaSize + 1] do
      weight := weight.set! i ((1 + (weight[i]! >>> 8) / 2) <<< 8)
  return len

/-- `BZ2_hbAssignCodes` (`huffman.c:152-166`): canonical codes for the code lengths `length`,
by increasing length and then symbol (`huffman.c:160-165`). -/
def assignCodes (length : Array Nat) (minLen maxLen : Nat) : Array Nat := Id.run do
  let mut code : Array Nat := Array.replicate length.size 0
  let mut vec := 0
  for n in [minLen:maxLen + 1] do
    for i in [0:length.size] do
      if length[i]! == n then
        code := code.set! i vec
        vec := vec + 1
    vec := vec <<< 1
  return code

/-- The coding tables and selectors of one block, as `sendMTFValues` leaves them in `s->len`,
`s->code` and `s->selector` (`compress.c:404`, `compress.c:447-451`, `compress.c:490-491`). -/
structure Tables where
  /-- `nGroups`, 2 to 6. -/
  nGroups : Nat
  /-- Code length of each symbol, per table (`nGroups` tables of `alphaSize` entries). -/
  len : Array (Array Nat)
  /-- Code of each symbol, per table. -/
  code : Array (Array Nat)
  /-- The table chosen for each group of 50 symbols. -/
  selector : Array Nat
  deriving Repr, BEq, Inhabited

/-- Number of tables for `nMTF` symbols (`compress.c:273-277`). -/
def numTables (nMTF : Nat) : Nat :=
  if nMTF < 200 then 2 else if nMTF < 600 then 3 else if nMTF < 1200 then 4
  else if nMTF < 2400 then 5 else 6

/-- The initial tables (`compress.c:283-316`): `len[t][v]` is 0 (`BZ_LESSER_ICOST`) inside table
`t`'s symbol range and 15 (`BZ_GREATER_ICOST`) elsewhere (`compress.c:308-311`). Ranges are
cut by cumulative frequency: the target is `remF / nPart` (`compress.c:287`), the range grows
until it is reached (`compress.c:288-293`), and on odd steps the last symbol is given back
(`compress.c:295-300`). -/
private def initialLens (mtfFreq : Array Nat) (alphaSize nMTF nGroups : Nat) :
    Array (Array Nat) := Id.run do
  let mut len : Array (Array Nat) := Array.replicate nGroups (Array.replicate alphaSize 15)
  let mut nPart := nGroups
  let mut remF := nMTF
  let mut gs : Int := 0
  while nPart > 0 do
    let tFreq := remF / nPart
    let mut ge : Int := gs - 1
    let mut aFreq := 0
    while aFreq < tFreq && ge < (alphaSize : Int) - 1 do
      ge := ge + 1
      aFreq := aFreq + mtfFreq[ge.toNat]!
    if ge > gs && nPart != nGroups && nPart != 1 && (nGroups - nPart) % 2 == 1 then
      aFreq := aFreq - mtfFreq[ge.toNat]!
      ge := ge - 1
    len := len.set! (nPart - 1)
      ((Array.range alphaSize).map fun (v : Nat) =>
        if Int.ofNat v ≥ gs && Int.ofNat v ≤ ge then 0 else 15)
    nPart := nPart - 1
    gs := ge + 1
    remF := remF - aFreq
  return len

/-- Chooses tables and selectors for `mtfv` (the block's symbols, EOB last) over an alphabet
of `alphaSize = nInUse + 2` symbols, as `sendMTFValues` does: `numIters` passes
(`compress.c:322`) each give every group of 50 symbols to the cheapest table, the first of equal
cost (`compress.c:399-405`), count symbol frequencies per table (`compress.c:410-432`) and
rebuild the lengths from them (`compress.c:447-451`); finally codes are assigned from the
lengths' range (`compress.c:480-492`). Requires `mtfv` nonempty with all symbols
`< alphaSize`. -/
def choose (mtfv : Array UInt16) (alphaSize : Nat) : Tables := Id.run do
  let nMTF := mtfv.size
  let mut mtfFreq : Array Nat := Array.replicate alphaSize 0
  for s in mtfv do
    mtfFreq := mtfFreq.modify s.toNat (· + 1)
  let nGroups := numTables nMTF
  let mut len := initialLens mtfFreq alphaSize nMTF nGroups
  let mut selector : Array Nat := #[]
  for _ in [0:numIters] do
    let mut rfreq : Array (Array Nat) := Array.replicate nGroups (Array.replicate alphaSize 0)
    selector := #[]
    let mut gs := 0
    while gs < nMTF do
      let ge := min (gs + groupSize - 1) (nMTF - 1)
      let mut cost : Array Nat := Array.replicate nGroups 0
      for i in [gs:ge + 1] do
        let icv := mtfv[i]!.toNat
        for t in [0:nGroups] do
          cost := cost.modify t (· + len[t]![icv]!)
      let mut bc := 999999999
      let mut bt := 0
      for t in [0:nGroups] do
        if cost[t]! < bc then
          bc := cost[t]!
          bt := t
      selector := selector.push bt
      for i in [gs:ge + 1] do
        rfreq := rfreq.modify bt fun r => r.modify mtfv[i]!.toNat (· + 1)
      gs := ge + 1
    len := rfreq.map fun f => makeCodeLengths f maxCodeLen
  let code := len.map fun l =>
    assignCodes l (l.foldl min 32) (l.foldl max 0)
  return { nGroups, len, code, selector }

end Bzip2.Oracle.Compress.Huffman
