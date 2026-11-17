import Bzip2.Oracle.Compress.Bwt
import Bzip2.Oracle.Compress.FallbackSort
import Bzip2.Oracle.Compress.MainSort

/-!
# Oracle: byte-exact BWT pointer

The last column is computed by `Bwt.bwt`. Equal rotations give the same preceding byte, but
the encoded pointer names rotation zero's actual row in the C sort map
(`blocksort.c:1083-1088`). For periodic blocks, this module reproduces that map's tie order:
`BZ2_blockSort` uses the fallback sort below 10000 bytes, and otherwise tries the main sort
with work factor 30 before falling back if the budget is exhausted
(`blocksort.c:1039-1081`). For blocks with distinct rotations, the existing first-row pointer
is already exact and no second sort is needed.
-/

namespace Bzip2.Oracle.Compress.ExactBwt

/-- The C compressor's last column and row of rotation zero. The empty block gives
`(empty, 0)`; the stream writer calls this only for nonempty blocks. -/
def bwt (block : ByteArray) : ByteArray × Nat := Id.run do
  let (last, first) := Bwt.bwt block
  if block.size == 0 || Bwt.rootSize block == block.size then return (last, first)
  let order := if block.size < 10000 then FallbackSort.sort block else
    match MainSort.sort? block with
    | some sorted => sorted
    | none => FallbackSort.sort block
  return (last, (order.findIdx? (· == 0)).getD first)

end Bzip2.Oracle.Compress.ExactBwt
