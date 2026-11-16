import Mathlib.Data.List.Basic
import Bzip2.Spec.Rle1

/-!
# bzip2: the specification

What a bzip2 stream is and what it decodes to, stated declaratively, as the vendored bzip2
behaves (`projects/bzip2/upstream`, commit f5dfc96: 1.0.8 plus later fixes; its C sources are the
reference, and `docs/surface-area.md` documents them). The oracle must agree with this
specification, and `Bzip2.Proofs` shows that it does.

Each part goes in its own module under `Bzip2.Spec`, imported here:

* `Bzip2.Spec.Crc`: CRC-32 as bzip2 uses it, the block CRC and the combined stream CRC.
* `Bzip2.Spec.Rle1`: the initial run-length encoding (runs of 4 to 255 equal bytes).
* `Bzip2.Spec.Bwt`: the Burrows–Wheeler transform of a block, its origin pointer, its inverse.
* `Bzip2.Spec.MtfRle2`: the symbol map, move-to-front, and the RUNA/RUNB zero-run code.
* `Bzip2.Spec.Huffman`: code lengths, the canonical code bzip2 assigns, decoding.
* `Bzip2.Spec.Format`: the bit-level syntax of streams and blocks, and `Decodes`: the relation
  between a byte string and what it decompresses to.

Definitions here favour clarity over speed; they need not be executable. They import Mathlib
only, never `Bzip2.Oracle`.
-/

namespace Bzip2.Spec

end Bzip2.Spec
