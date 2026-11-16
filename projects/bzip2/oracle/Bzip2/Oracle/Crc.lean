/-!
# bzip2's CRC, table-driven

The table `BZ2_crc32Table` is `crctable.c:31-99`; the CRC macros are `bzlib_private.h:157-172`
(`BZ_INITIALISE_CRC` at `bzlib_private.h:157-160`, `BZ_FINALISE_CRC` at
`bzlib_private.h:162-165`, `BZ_UPDATE_CRC` at `bzlib_private.h:167-172`). It is the MSB-first
CRC-32 with polynomial `0x04c11db7` (the table's entry 1, `crctable.c:35`), initial value
`0xffffffff`, final complement, no reflection. The table is generated here, not pasted: entry `i`
is `i` shifted into the top byte, then eight shift-and-xor steps.

The combined stream CRC is `compress.c:607-608`: `combined := rotl combined 1 ^^^ blockCRC`,
starting from 0 (`bzlib.c:192`).

Edge cases this module settles (the C macros work on one byte at a time and have none):

* The empty input has CRC `0`: no byte is folded in, so the state stays `0xffffffff` and the
  final complement gives `0`.
* The functions take a slice `data[start, stop)` of a `ByteArray`. `stop` is clamped to
  `data.size`, and a `start` that is not below the clamped `stop` gives the empty slice, so
  out-of-range indices never fail and never read past the array.
-/

namespace Bzip2.Oracle.Crc

/-- The generator polynomial: `BZ2_crc32Table[1]`. -/
def poly : UInt32 := 0x04c11db7

/-- Entry `i` of the table: `i` shifted into the top byte, then eight MSB-first division steps. -/
def entry (i : UInt32) : UInt32 := Id.run do
  let mut c := i <<< 24
  for _ in [0:8] do
    c := if c &&& 0x80000000 != 0 then (c <<< 1) ^^^ poly else c <<< 1
  return c

/-- `BZ2_crc32Table`. -/
def table : Array UInt32 := Array.ofFn (n := 256) fun i => entry i.val.toUInt32

/-- `BZ_INITIALISE_CRC`. -/
def init : UInt32 := 0xffffffff

/-- `BZ_FINALISE_CRC`. -/
def finalise (c : UInt32) : UInt32 := ~~~c

/-- `BZ_UPDATE_CRC` for one byte. -/
@[inline] def updateByte (c : UInt32) (b : UInt8) : UInt32 :=
  (c <<< 8) ^^^ table[((c >>> 24) ^^^ b.toUInt32).toNat &&& 0xff]!

/-- Runs the (not yet finalised) CRC state `c` over `data[start, stop)`; the range is clamped to
the array. -/
def update (c : UInt32) (data : ByteArray) (start : Nat := 0) (stop : Nat := data.size) :
    UInt32 := Id.run do
  let stop := min stop data.size
  let mut c := c
  for i in [start:stop] do
    c := updateByte c data[i]!
  return c

/-- The CRC of `data[start, stop)` as bzip2 stores it for a block. -/
def crc32 (data : ByteArray) (start : Nat := 0) (stop : Nat := data.size) : UInt32 :=
  finalise (update init data start stop)

/-- Folds a block CRC into the combined stream CRC. -/
def combine (combined blockCrc : UInt32) : UInt32 :=
  ((combined <<< 1) ||| (combined >>> 31)) ^^^ blockCrc

end Bzip2.Oracle.Crc
