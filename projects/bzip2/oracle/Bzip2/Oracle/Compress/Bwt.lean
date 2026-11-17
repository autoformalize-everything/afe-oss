/-!
# Oracle: forward Burrows-Wheeler transform

`Bzip2.Oracle.Compress.Bwt.bwt block` returns the last column of the sorted rotations of `block`.
`BZ2_blockSort` leaves the sorted order in `ptr` (`blocksort.c:1025-1029`); compression reads
the preceding byte for each entry (`compress.c:163-167`). It also returns `origPtr`, the row of
rotation 0 (`blocksort.c:1083-1088`).

Algorithm: a block that repeats a shorter root `w` (`block = w ++ ... ++ w`, found by testing
the periods `n / q` for the prime factors `q` of `n`) is transformed through `w`, whose rotations
are distinct. Rotations of a block with no such period are sorted by prefix doubling on cyclic
shifts, with no comparison sorts. A first counting sort orders them by their first two bytes;
each later round orders them by twice as many bytes: it takes the current order, shifts it by the
key length, and distributes it stably into the classes of the first key. A class is named by the
row where it starts, so its bucket needs no prefix sums and a round is two passes over the block.
Random blocks need two rounds. The time is O(n log n) in the worst case, and the interpreter
handles 900 000-byte blocks in a few seconds (the tests).

Tie-breaking: rotations are compared as byte strings (unsigned bytes, as in `blocksort.c:354-362`).
Equal rotations occur exactly when `block` is periodic; they are interchangeable in the output
column and come in groups of `n / |w|`. `origPtr` is the first row whose rotation equals
rotation 0, the first row of its group. This may differ from the C
library's `origPtr` on periodic blocks, which is the remit of `oracle/compress/byte-exact`.
The inverse transform recovers `block` either way.
-/

namespace Bzip2.Oracle.Compress.Bwt

/-- The key of every rotation of `block` (row ↦ the number of its first two bytes) and how often
each key occurs. The loop is at `i`, whose byte is `cur`; the size `n` is that of `block`. -/
def keyCounts (block : ByteArray) (n i cur : Nat) (keys cnt : Array Nat) :
    Array Nat × Array Nat :=
  if i < n then
    let nxt := (block.get! (if i + 1 == n then 0 else i + 1)).toNat
    let kv := cur * 256 + nxt
    keyCounts block n (i + 1) nxt (keys.push kv) (cnt.set! kv (cnt[kv]! + 1))
  else (keys, cnt)
termination_by n - i

/-- The start indices in the order of their keys: `cnt` holds the next free row of each key. -/
def placeByKey (keys : Array Nat) (n i : Nat) (cnt p : Array Nat) : Array Nat :=
  if i < n then
    let kv := keys[i]!
    let j := cnt[kv]!
    placeByKey keys n (i + 1) (cnt.set! kv (j + 1)) (p.set! j i)
  else p
termination_by n - i

/-- The class of every start index by its key, given the order `p` by key: the first row of the
equal keys. Returns the classes and their number. The loop is at row `i`, after a class that
began at row `st` with key `prev`, and `cls` classes so far. -/
def keyClasses (keys p : Array Nat) (n i st prev cls : Nat) (c : Array Nat) :
    Array Nat × Nat :=
  if i < n then
    let a := p[i]!
    let kv := keys[a]!
    if kv != prev then keyClasses keys p n (i + 1) i kv (cls + 1) (c.set! a i)
    else keyClasses keys p n (i + 1) st prev cls (c.set! a st)
  else (c, cls)
termination_by n - i

/-- One doubling, first half: the start indices of `p` shifted back by `k` and distributed
stably into the classes `c`, which gives the order by the first `2 * k` bytes. `next` holds the
next free row of each class, which is named by its first row. -/
def distribute (p c : Array Nat) (n k i : Nat) (next p2 : Array Nat) : Array Nat :=
  if i < n then
    let v := p[i]!
    let u := if v >= k then v - k else v + n - k
    let kc := c[u]!
    let j := next[kc]!
    distribute p c n k (i + 1) (next.set! kc (j + 1)) (p2.set! j u)
  else p2
termination_by n - i

/-- One doubling, second half: the classes by the first `2 * k` bytes, given the order `p` by
them and the classes `c` by the first `k`. Returns the classes and their number. The loop is
at row `i`, after a class that began at row `st` with the keys `pc` and `pc2` (the classes by
the first and the second `k` bytes), and `cls` classes so far. -/
def doubleClasses (p c : Array Nat) (n k i st pc pc2 cls : Nat) (c2 : Array Nat) :
    Array Nat × Nat :=
  if i < n then
    let a := p[i]!
    let ca := c[a]!
    let ca2 := c[if a + k >= n then a + k - n else a + k]!
    if ca != pc || ca2 != pc2 then
      doubleClasses p c n k (i + 1) i ca ca2 (cls + 1) (c2.set! a i)
    else doubleClasses p c n k (i + 1) st pc pc2 cls (c2.set! a st)
  else (c2, cls)
termination_by n - i

/-- Sorted order of the rotations of `block` (row ↦ start index), together with the class of each
start index: equal rotations have equal classes, and the class of a rotation is the first row
holding a rotation equal to it. `block` must have at least one byte. -/
def sortRotations (block : ByteArray) : Array Nat × Array Nat := Id.run do
  let n := block.size
  let (keys, cnt) := keyCounts block n 0 (block.get! 0).toNat (Array.emptyWithCapacity n)
    (Array.replicate 65536 0)
  let mut sums := cnt
  let mut sum := 0
  for b in [0:65536] do
    let x := cnt[b]!
    sums := sums.set! b sum
    sum := sum + x
  let mut p := placeByKey keys n 0 sums (Array.replicate n 0)
  let (c0, classes0) := keyClasses keys p n 1 0 keys[p[0]!]! 1 (Array.replicate n 0)
  let mut c := c0
  let mut classes := classes0
  let mut k := 2
  while k < n && classes < n do
    p := distribute p c n k 0 (Array.range n) (Array.replicate n 0)
    let a := p[0]!
    let (c2, cls) := doubleClasses p c n k 1 0 c[a]! c[if a + k >= n then a + k - n else a + k]!
      1 (Array.replicate n 0)
    c := c2
    classes := cls
    k := k * 2
  return (p, c)

/-- Whether `block` is its own rotation by `d` (`d ≤ block.size`): it repeats its first `d`
bytes, when `d` divides the size. -/
def hasPeriod (block : ByteArray) (d : Nat) : Bool :=
  block.extract d block.size == block.extract 0 (block.size - d)

/-- The length of the shortest root `w` with `block = w ++ ... ++ w`: the size of `block` divided
by each prime factor `q` of it, as often as `block` still has the period. The empty block gives
0. -/
def rootSize (block : ByteArray) : Nat := Id.run do
  let n := block.size
  let mut d := n
  let mut m := n
  let mut q := 2
  while q * q ≤ m do
    if m % q == 0 then
      while m % q == 0 do
        m := m / q
        if d % q == 0 && hasPeriod block (d / q) then d := d / q
    q := q + 1
  if m > 1 && hasPeriod block (d / m) then d := d / m
  return d

/-- `out` with the byte `x` appended `reps` times. -/
def repeatByte (out : ByteArray) (x : UInt8) : Nat → ByteArray
  | 0 => out
  | r + 1 => repeatByte (out.push x) x r

/-- The last column of the sorted rotations of `root`, each byte `reps` times, from row `i` on:
`p` is the sorted order of the rotations of `root`, whose size is `d`. -/
def lastColumn (root : ByteArray) (reps d i : Nat) (p : Array Nat) (out : ByteArray) :
    ByteArray :=
  if i < d then
    let v := p[i]!
    let x := root.get! (if v == 0 then d - 1 else v - 1)
    lastColumn root reps d (i + 1) p (repeatByte out x reps)
  else out
termination_by d - i

/-- The forward BWT of `block`: the last column of the sorted rotations and `origPtr`.
See the module doc for the tie-breaking on periodic blocks. The empty block gives `(empty, 0)`. -/
def bwt (block : ByteArray) : ByteArray × Nat := Id.run do
  let n := block.size
  if n == 0 then return (.empty, 0)
  let d := rootSize block
  let root := block.extract 0 d
  let (p, c) := sortRotations root
  let reps := n / d
  return (lastColumn root reps d 0 p (ByteArray.emptyWithCapacity n), c[0]! * reps)

end Bzip2.Oracle.Compress.Bwt
