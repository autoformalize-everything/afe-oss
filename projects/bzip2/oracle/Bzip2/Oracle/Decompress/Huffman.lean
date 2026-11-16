import Bzip2.Oracle.BitIO

/-!
# Oracle: Huffman decoding tables

Decoding tables from code lengths, and decoding one symbol from a bit reader, as bzip2 does:
`BZ2_hbCreateDecodeTables` (`huffman.c:170-200`) builds `limit`, `base` and `perm`, and
`GET_MTF_VAL` (`decompress.c:74-102`) reads a symbol with them. `BZ2_decompress` calls the
former once per table with `minLen`/`maxLen` the least and greatest length
(`decompress.c:339-352`).

The C structure is kept: `perm` lists the symbols by increasing length, `base` and `limit` are
indexed by code length, and a symbol is found by reading `minLen` bits and then one bit at a
time until the value is at most `limit[zn]`.

Edge cases, all as in the C code, with no check of the table's shape:
* An incomplete length set (Kraft sum below 1): a code that matches no length keeps growing
  until `zn > 20` and the decoder fails with `Error.data` (`decompress.c:91-92`). Entries of
  `limit` past `maxLen` are 0 (`huffman.c:190`), and the value read is positive by then, so
  the loop does not stop there either.
* An over-subscribed set (Kraft sum above 1): the tables are still built and the symbol found
  is the one the canonical arithmetic gives; some `perm` entries are never reached.
* The index `zvec - base[zn]` outside `0 ..< 258` is `Error.data` (`decompress.c:98-100`).
  Tables built by `createDecodeTables` from lengths in `1..20` never reach that check (the
  index is below the number of symbols whose length is at most `zn`); it is kept so that
  arbitrary `Tables` behave as the C code does.
* Running out of input inside a symbol is `Error.eof` (the C code's `GET_BITS` has no input
  left: `decompress.c:54`, which `BZ2_bzRead` turns into `BZ_UNEXPECTED_EOF`,
  `bzlib.c:1204-1209`). `decodeSym` reads `minLen` bits at once, as the C code does, so the
  reader is unchanged on every error.

Choices: `limit` and `base` are `Array Int` of the C's `BZ_MAX_CODE_LEN` = 23 entries: they
hold `-1` and never overflow `Int32` (`vec` stays below `258 * 2^21`). `perm` is an
`Array Nat` of `BZ_MAX_ALPHA_SIZE` = 258 entries, unused ones 0 (the C leaves them as they
were; no decode reads one). Code lengths are `UInt8`, a table is built from the whole array
of lengths (its size is `alphaSize`), and `ofLengths` refuses what `BZ2_decompress` refuses
before building (a length outside `1..20`, `decompress.c:327`), which `BZ2_hbCreateDecodeTables`
itself does not check (its entries must be at most 21, `docs/surface-area.md`). The per-block
state around it (selectors, `groupPos`, `decompress.c:79-87`) belongs to the stream decoder.
-/

namespace Bzip2.Oracle.Decompress.Huffman

open Bzip2.Oracle Bzip2.Oracle.BitIO

/-- `BZ_MAX_CODE_LEN`: entries of `limit` and `base` that `BZ2_hbCreateDecodeTables` sets
(`bzlib_private.h:116`). -/
def maxCodeLen : Nat := 23

/-- `BZ_MAX_ALPHA_SIZE`: entries of `perm` (`bzlib_private.h:115`). -/
def maxAlphaSize : Nat := 258

/-- The longest code the decoder accepts (`decompress.c:91`, `decompress.c:327`). -/
def longestCode : Nat := 20

/-- The decoding tables of one coding table: `limit`, `base`, `perm` and `minLen` of
`BZ2_hbCreateDecodeTables` and `s->minLens` (`decompress.c:346-352`). -/
structure Tables where
  /-- Largest `zn`-bit code value of length `zn`, or `-1`; 0 outside `minLen..maxLen`. -/
  limit : Array Int
  /-- Offset turning a `zn`-bit code value into an index into `perm`. -/
  base : Array Int
  /-- Symbols by increasing code length, then increasing symbol. -/
  perm : Array Nat
  /-- The shortest code length: the number of bits read first. -/
  minLen : Nat
  deriving Repr, BEq, Inhabited

/-- `BZ2_hbCreateDecodeTables` (`huffman.c:170-200`) on `length` (`alphaSize` = its size) with
the given `minLen` and `maxLen`. Every length must be at most 21 and, to be meaningful, within
`minLen..maxLen` (`ofLengths` ensures both). -/
def createDecodeTables (length : Array UInt8) (minLen maxLen : Nat) : Tables := Id.run do
  let alphaSize := length.size
  -- `huffman.c:180-183`: perm
  let mut perm : Array Nat := Array.replicate maxAlphaSize 0
  let mut pp := 0
  for i in [minLen:maxLen + 1] do
    for j in [0:alphaSize] do
      if length[j]!.toNat == i then
        perm := perm.set! pp j
        pp := pp + 1
  -- `huffman.c:185-188`: base[l + 1] counts the symbols of length l, then prefix sums
  let mut base : Array Int := Array.replicate maxCodeLen 0
  for i in [0:alphaSize] do
    base := base.modify (length[i]!.toNat + 1) (· + 1)
  for i in [1:maxCodeLen] do
    base := base.set! i (base[i]! + base[i - 1]!)
  -- `huffman.c:190-197`: limit
  let mut limit : Array Int := Array.replicate maxCodeLen 0
  let mut vec : Int := 0
  for i in [minLen:maxLen + 1] do
    vec := vec + (base[i + 1]! - base[i]!)
    limit := limit.set! i (vec - 1)
    vec := vec * 2
  -- `huffman.c:198-199`: base
  for i in [minLen + 1:maxLen + 1] do
    base := base.set! i ((limit[i - 1]! + 1) * 2 - base[i]!)
  return { limit, base, perm, minLen }

/-- The tables `BZ2_decompress` builds for one coding table with code lengths `length`
(`decompress.c:339-352`): `minLen` and `maxLen` are the least and greatest length. Fails with
`Error.data` on a length outside `1..20`, which `BZ2_decompress` rejects while reading the
lengths (`decompress.c:327`), and with `Error.param` if there are no lengths or more than
`BZ_MAX_ALPHA_SIZE` of them. -/
def ofLengths (length : Array UInt8) : Except Error Tables :=
  if length.isEmpty || length.size > maxAlphaSize then
    .error (.param "Huffman.ofLengths: alphabet size outside 1..258")
  else if length.any (fun l => l == 0 || l.toNat > longestCode) then
    .error (.data "Huffman.ofLengths: code length outside 1..20")
  else
    let minLen := length.foldl (fun m l => min m l.toNat) 32
    let maxLen := length.foldl (fun m l => max m l.toNat) 0
    .ok (createDecodeTables length minLen maxLen)

/-- The loop of `GET_MTF_VAL` after the first `zn` bits, now `zvec` (`decompress.c:90-97`):
fail when `zn > 20`, stop when `zvec ≤ limit[zn]`, else append one bit. -/
private def extend (t : Tables) (zn : Nat) (zvec : Int) (r : BitReader) :
    Except Error (Nat × Int × BitReader) :=
  if zn > longestCode then .error (.data "Huffman: code longer than 20 bits")
  else if zvec ≤ t.limit[zn]! then .ok (zn, zvec, r)
  else
    match r.readBit with
    | .error e => .error e
    | .ok (b, r') => extend t (zn + 1) (zvec * 2 + if b then 1 else 0) r'
termination_by longestCode + 1 - zn

/-- `GET_MTF_VAL` without the selector bookkeeping (`decompress.c:88-101`): reads the next
symbol of `r` with `t`, returning it and the reader after its code. `Error.eof` if the input
ends inside the code, `Error.data` if the code exceeds 20 bits (`decompress.c:91-92`) or the
index into `perm` is outside `0 ..< 258` (`decompress.c:98-100`). -/
def decodeSym (t : Tables) (r : BitReader) : Except Error (Nat × BitReader) :=
  match r.readBits t.minLen with
  | .error e => .error e
  | .ok (v, r) =>
    match extend t t.minLen v.toNat r with
    | .error e => .error e
    | .ok (zn, zvec, r) =>
      let idx := zvec - t.base[zn]!
      if idx < 0 || idx ≥ maxAlphaSize then
        .error (.data "Huffman: index outside perm")
      else
        .ok (t.perm[idx.toNat]!, r)

end Bzip2.Oracle.Decompress.Huffman
