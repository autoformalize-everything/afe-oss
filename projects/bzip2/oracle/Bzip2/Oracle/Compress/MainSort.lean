/-!
# Oracle: main block sort tie order

The two-byte radix buckets, bucket processing order, forward and backward pointer scans,
quicksort, and quadrant values follow `mainSort` (`blocksort.c:758-1017`). A negative work
budget requests the fallback sorter, as `BZ2_blockSort` does (`blocksort.c:1053-1080`).
Arrays store the C permutation and quadrant values directly. The sorted order is needed only
for the row of rotation zero when rotations are equal; the BWT last column is unaffected.
-/

namespace Bzip2.Oracle.Compress.MainSort

/-- The Knuth gaps used by the small bucket sort (`blocksort.c:479-482`). -/
private def gaps : Array Nat :=
  #[1, 4, 13, 40, 121, 364, 1093, 3280, 9841, 29524, 88573, 265720, 797161, 2391484]

/-- Exchanges two rotation indices. -/
private def swap (p : Array Nat) (a b : Nat) : Array Nat :=
  (p.set! a p[b]!).set! b p[a]!

/-- Compares rotations at a depth and accounts for the work in `mainGtU`
(`blocksort.c:347-469`). `block` and `quadrant` include 34 overshoot entries. -/
private def gt (block : ByteArray) (quadrant : Array Nat) (n a b : Nat) (budget : Int) :
    Bool × Int := Id.run do
  let mut i := a
  let mut j := b
  for _ in [0:12] do
    let x := (block.get! i).toNat
    let y := (block.get! j).toNat
    if x != y then return (x > y, budget)
    i := i + 1
    j := j + 1
  let mut k : Int := n + 8
  let mut budget := budget
  repeat
    for _ in [0:8] do
      let x := (block.get! i).toNat
      let y := (block.get! j).toNat
      if x != y then return (x > y, budget)
      let qx := quadrant[i]!
      let qy := quadrant[j]!
      if qx != qy then return (qx > qy, budget)
      i := i + 1
      j := j + 1
    if i ≥ n then i := i - n
    if j ≥ n then j := j - n
    k := k - 8
    budget := budget - 1
    if k < 0 then break
  return (false, budget)

/-- Shell sort of a small bucket (`blocksort.c:484-555`). -/
private def simpleSort (p : Array Nat) (block : ByteArray) (quadrant : Array Nat)
    (n : Nat) (lo hi : Int) (d : Nat) (budget : Int) : Array Nat × Int := Id.run do
  if hi - lo + 1 < 2 then return (p, budget)
  let mut p := p
  let mut budget := budget
  let size := (hi - lo + 1).toNat
  let mut hp := 0
  while gaps[hp]! < size do hp := hp + 1
  repeat
    if hp == 0 then break
    hp := hp - 1
    let h := gaps[hp]!
    for i in [(lo.toNat + h):hi.toNat + 1] do
      let v := p[i]!
      let mut j := i
      repeat
        let (greater, left) := gt block quadrant n (p[j - h]! + d) (v + d) budget
        budget := left
        if !greater then break
        p := p.set! j p[j - h]!
        j := j - h
        if j ≤ lo.toNat + h - 1 then break
      p := p.set! j v
      if budget < 0 then return (p, budget)
  return (p, budget)

/-- Median of three byte values (`blocksort.c:581-592`). -/
private def med3 (a b c : Nat) : Nat :=
  max (min a b) (min (max a b) c)

/-- Three-way string quicksort of one small bucket (`blocksort.c:620-717`). -/
private def quickSort (p : Array Nat) (block : ByteArray) (quadrant : Array Nat)
    (n loSt hiSt dSt : Nat) (budget : Int) : Array Nat × Int := Id.run do
  let mut p := p
  let mut budget := budget
  let mut stack : Array (Int × Int × Nat) := #[(loSt, hiSt, dSt)]
  while !stack.isEmpty do
    let (lo, hi, d) := stack.back!
    stack := stack.pop
    if hi - lo < 20 || d > 14 then
      let (sorted, left) := simpleSort p block quadrant n lo hi d budget
      p := sorted
      budget := left
      if budget < 0 then return (p, budget)
      continue
    let med := med3 (block.get! (p[lo.toNat]! + d)).toNat
      (block.get! (p[hi.toNat]! + d)).toNat
      (block.get! (p[((lo + hi) / 2).toNat]! + d)).toNat
    let mut unLo := lo
    let mut ltLo := lo
    let mut unHi := hi
    let mut gtHi := hi
    repeat
      repeat
        if unLo > unHi then break
        let c := (block.get! (p[unLo.toNat]! + d)).toNat
        if c == med then
          p := swap p unLo.toNat ltLo.toNat
          ltLo := ltLo + 1
          unLo := unLo + 1
        else if c > med then break
        else unLo := unLo + 1
      repeat
        if unLo > unHi then break
        let c := (block.get! (p[unHi.toNat]! + d)).toNat
        if c == med then
          p := swap p unHi.toNat gtHi.toNat
          gtHi := gtHi - 1
          unHi := unHi - 1
        else if c < med then break
        else unHi := unHi - 1
      if unLo > unHi then break
      p := swap p unLo.toNat unHi.toNat
      unLo := unLo + 1
      unHi := unHi - 1
    if gtHi < ltLo then
      stack := stack.push (lo, hi, d + 1)
      continue
    let leftN := min (ltLo - lo) (unLo - ltLo)
    for j in [0:leftN.toNat] do
      p := swap p (lo + j).toNat (unLo - leftN + j).toNat
    let rightN := min (hi - gtHi) (gtHi - unHi)
    for j in [0:rightN.toNat] do
      p := swap p (unLo + j).toNat (hi - rightN + 1 + j).toNat
    let a : Int × Int × Nat := (lo, lo + unLo - ltLo - 1, d)
    let b : Int × Int × Nat := (hi - (gtHi - unHi) + 1, hi, d)
    let c : Int × Int × Nat := (a.2.1 + 1, b.1 - 1, d + 1)
    let mut next := #[a, b, c]
    if sizeOf next[0]! < sizeOf next[1]! then
      next := swapNext next 0 1
    if sizeOf next[1]! < sizeOf next[2]! then
      next := swapNext next 1 2
    if sizeOf next[0]! < sizeOf next[1]! then
      next := swapNext next 0 1
    for v in next do stack := stack.push v
  return (p, budget)
where
  swapNext (a : Array (Int × Int × Nat)) (i j : Nat) : Array (Int × Int × Nat) :=
    (a.set! i a[j]!).set! j a[i]!
  sizeOf (v : Int × Int × Nat) : Int := v.2.1 - v.1

/-- The main rotation map, or `none` if its work budget was exhausted
(`blocksort.c:758-1017`, `blocksort.c:1053-1080`). -/
def sort? (input : ByteArray) : Option (Array Nat) := Id.run do
  let n := input.size
  if n == 0 then return some #[]
  let mut block := input
  for i in [0:34] do block := block.push (input.get! i)
  let mut quadrant := Array.replicate (n + 34) 0
  let mut count := Array.replicate 65537 0
  for i in [0:n] do
    let key := (input.get! i).toNat * 256 + (input.get! ((i + 1) % n)).toNat
    count := count.modify key (· + 1)
  for i in [1:65537] do
    count := count.set! i (count[i]! + count[i - 1]!)
  let mut p := Array.replicate n 0
  for off in [0:n] do
    let i := n - 1 - off
    let key := (input.get! i).toNat * 256 + (input.get! ((i + 1) % n)).toNat
    let j := count[key]! - 1
    count := count.set! key j
    p := p.set! j i
  let mut order := Array.range 256
  let mut h := 364
  repeat
    h := h / 3
    for i in [h:256] do
      let v := order[i]!
      let freqV := count[(v + 1) * 256]! - count[v * 256]!
      let mut j := i
      while count[(order[j - h]! + 1) * 256]! - count[order[j - h]! * 256]! > freqV do
        order := order.set! j order[j - h]!
        j := j - h
        if j ≤ h - 1 then break
      order := order.set! j v
    if h == 1 then break
  let mut bigDone := Array.replicate 256 false
  let mut smallDone := Array.replicate 65536 false
  let mut budget : Int := n * 9
  for oi in [0:256] do
    let ss := order[oi]!
    for j in [0:256] do
      if j != ss then
        let sb := ss * 256 + j
        if !smallDone[sb]! then
          let lo := count[sb]!
          let hi := count[sb + 1]! - 1
          if hi > lo then
            let (sorted, left) := quickSort p block quadrant n lo hi 2 budget
            p := sorted
            budget := left
            if budget < 0 then return none
        smallDone := smallDone.set! sb true
    let mut copyStart := Array.replicate 256 0
    let mut copyEnd := Array.replicate 256 0
    for j in [0:256] do
      copyStart := copyStart.set! j count[j * 256 + ss]!
      copyEnd := copyEnd.set! j (count[j * 256 + ss + 1]! - 1)
    let mut fwd := count[ss * 256]!
    while fwd < copyStart[ss]! do
      let k := (p[fwd]! + n - 1) % n
      let c := (input.get! k).toNat
      if !bigDone[c]! then
        p := p.set! copyStart[c]! k
        copyStart := copyStart.modify c (· + 1)
      fwd := fwd + 1
    let mut rev := count[(ss + 1) * 256]! - 1
    while rev > copyEnd[ss]! do
      let k := (p[rev]! + n - 1) % n
      let c := (input.get! k).toNat
      if !bigDone[c]! then
        p := p.set! copyEnd[c]! k
        copyEnd := copyEnd.modify c (· - 1)
      rev := rev - 1
    for c in [0:256] do smallDone := smallDone.set! (c * 256 + ss) true
    bigDone := bigDone.set! ss true
    if oi < 255 then
      let st := count[ss * 256]!
      let size := count[(ss + 1) * 256]! - st
      let mut shifts := 0
      while size >>> shifts > 65534 do shifts := shifts + 1
      for j in [0:size] do
        let a := p[st + j]!
        let q := j >>> shifts
        quadrant := quadrant.set! a q
        if a < 34 then quadrant := quadrant.set! (a + n) q
  return some p

end Bzip2.Oracle.Compress.MainSort
