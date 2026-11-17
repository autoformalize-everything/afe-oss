/-!
# Oracle: fallback block sort tie order

Reproduces the order of equal rotations from `fallbackSort` (`blocksort.c:208-329`).
The one-byte radix pass places indices in descending order within each byte bucket
(`blocksort.c:231-245`). Each doubling pass sorts the unresolved buckets by the previous
bucket of the rotation shifted back by `H` (`blocksort.c:259-312`). We keep bucket headers as
Boolean array entries rather than packed bits; this preserves the sort's permutation while
making bucket boundaries explicit.
-/

namespace Bzip2.Oracle.Compress.FallbackSort

/-- Exchanges the values at two positions in the rotation map. -/
private def swap (p : Array Nat) (a b : Nat) : Array Nat :=
  (p.set! a p[b]!).set! b p[a]!

/-- The insertion pass of `fallbackSimpleSort` (`blocksort.c:36-59`). -/
private def simpleSort (p eclass : Array Nat) (lo hi : Nat) : Array Nat := Id.run do
  let mut p := p
  if hi - lo > 3 then
    for off in [0:hi - lo - 3] do
      let i := hi - 4 - off
      let tmp := p[i]!
      let ec := eclass[tmp]!
      let mut j := i + 4
      while j ≤ hi && ec > eclass[p[j]!]! do
        p := p.set! (j - 4) p[j]!
        j := j + 4
      p := p.set! (j - 4) tmp
  for off in [0:hi - lo] do
    let i := hi - 1 - off
    let tmp := p[i]!
    let ec := eclass[tmp]!
    let mut j := i + 1
    while j ≤ hi && ec > eclass[p[j]!]! do
      p := p.set! (j - 1) p[j]!
      j := j + 1
    p := p.set! (j - 1) tmp
  return p

/-- The three-way partition of `fallbackQSort3` (`blocksort.c:92-181`). -/
private def quickSort (p eclass : Array Nat) (loSt hiSt : Nat) : Array Nat := Id.run do
  let mut p := p
  let mut stack : Array (Nat × Nat) := #[(loSt, hiSt)]
  let mut r := 0
  while !stack.isEmpty do
    let (lo, hi) := stack.back!
    stack := stack.pop
    if hi - lo < 10 then
      p := simpleSort p eclass lo hi
      continue
    r := (r * 7621 + 1) % 32768
    let med := eclass[p[if r % 3 == 0 then lo else if r % 3 == 1 then (lo + hi) / 2
      else hi]!]!
    let mut unLo := lo
    let mut ltLo := lo
    let mut unHi : Int := hi
    let mut gtHi : Int := hi
    repeat
      repeat
        if (unLo : Int) > unHi then break
        let ec := eclass[p[unLo]!]!
        if ec == med then
          p := swap p unLo ltLo
          ltLo := ltLo + 1
          unLo := unLo + 1
        else if ec > med then break
        else unLo := unLo + 1
      repeat
        if (unLo : Int) > unHi then break
        let ec := eclass[p[unHi.toNat]!]!
        if ec == med then
          p := swap p unHi.toNat gtHi.toNat
          gtHi := gtHi - 1
          unHi := unHi - 1
        else if ec < med then break
        else unHi := unHi - 1
      if (unLo : Int) > unHi then break
      p := swap p unLo unHi.toNat
      unLo := unLo + 1
      unHi := unHi - 1
    if gtHi < (ltLo : Int) then continue
    let n := min (ltLo - lo) (unLo - ltLo)
    for j in [0:n] do
      p := swap p (lo + j) (unLo - n + j)
    let m := min ((hi : Int) - gtHi).toNat (gtHi - unHi).toNat
    for j in [0:m] do
      p := swap p (unLo + j) (hi - m + 1 + j)
    let leftHi : Int := (lo : Int) + unLo - ltLo - 1
    let rightLo := hi - (gtHi - unHi).toNat + 1
    let left := if leftHi ≥ (lo : Int) then some (lo, leftHi.toNat) else none
    let right := if rightLo ≤ hi then some (rightLo, hi) else none
    if leftHi - (lo : Int) > (hi : Int) - rightLo then
      if let some v := left then stack := stack.push v
      if let some v := right then stack := stack.push v
    else
      if let some v := right then stack := stack.push v
      if let some v := left then stack := stack.push v
  return p

/-- The exact fallback rotation map for a nonempty block (`blocksort.c:208-329`). -/
def sort (block : ByteArray) : Array Nat := Id.run do
  let n := block.size
  if n == 0 then return #[]
  let mut count := Array.replicate 257 0
  for b in block do
    count := count.modify b.toNat (· + 1)
  for i in [1:257] do
    count := count.set! i (count[i]! + count[i - 1]!)
  let mut p := Array.replicate n 0
  for i in [0:n] do
    let b := (block.get! i).toNat
    let j := count[b]! - 1
    count := count.set! b j
    p := p.set! j i
  let mut heads := Array.replicate n false
  for i in [0:256] do
    if count[i]! < n then heads := heads.set! count[i]! true
  let mut h := 1
  repeat
    let mut eclass := Array.replicate n 0
    let mut start := 0
    for i in [0:n] do
      if heads[i]! then start := i
      let k := (p[i]! + n - h) % n
      eclass := eclass.set! k start
    let oldHeads := heads
    let mut notDone := 0
    let mut lo := 0
    while lo < n do
      let mut hi := lo + 1
      while hi < n && !oldHeads[hi]! do
        hi := hi + 1
      if hi - lo > 1 then
        notDone := notDone + hi - lo
        p := quickSort p eclass lo (hi - 1)
        let mut prev : Option Nat := none
        for i in [lo:hi] do
          let ec := eclass[p[i]!]!
          if prev != some ec then heads := heads.set! i true
          prev := some ec
      lo := hi
    h := h * 2
    if h > n || notDone == 0 then break
  return p

end Bzip2.Oracle.Compress.FallbackSort
