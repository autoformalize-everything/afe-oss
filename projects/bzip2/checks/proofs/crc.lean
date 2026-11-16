import Bzip2.Proofs.Crc

/-! What task `bzip2/proofs/crc` provides: the table-driven CRC and the combined CRC of the
oracle equal the specification's. -/

#check @Bzip2.Proofs.Crc.crc32_eq_spec
#check @Bzip2.Proofs.Crc.combine_eq_spec
