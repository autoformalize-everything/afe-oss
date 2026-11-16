/-!
# bzip2: proofs that the oracle meets the specification

Each result is its own module under `Bzip2.Proofs` (`Crc`, `Rle`, `Bwt`, `Huffman`,
`Decompress`, `Compress`), importing the spec and oracle modules it is about; Lake builds them
all. This file lists none of them and is not edited by tasks (`tools/check-sources.sh` rejects
it). The targets:

* soundness (`Bzip2.Proofs.Decompress`): `Oracle.decompress x = .ok y → Spec.Decodes x y`
* completeness (`Bzip2.Proofs.Decompress`): `Spec.Decodes x y → Oracle.decompress x = .ok y`
* compression (`Bzip2.Proofs.Compress`): `Oracle.compress l x = .ok z → Spec.Decodes z x`

No `sorry`, `admit` or new `axiom` anywhere (`tools/check-sources.sh`).
-/
