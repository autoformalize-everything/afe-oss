import Bzip2.Spec
import Bzip2.Oracle

/-!
# bzip2: proofs that the oracle meets the specification

Lemmas per part go in modules under `Bzip2.Proofs` (`Crc`, `Rle`, `Bwt`, `Huffman`, ...), and
the end results here. The targets:

* soundness: `Oracle.decompress x = .ok y → Spec.Decodes x y`
* completeness: `Spec.Decodes x y → Oracle.decompress x = .ok y`
* compression: `Oracle.compress l x = .ok z → Spec.Decodes z x`

No `sorry`, `admit` or new `axiom` anywhere (`tools/check-sources.sh`).
-/

namespace Bzip2.Proofs

end Bzip2.Proofs
