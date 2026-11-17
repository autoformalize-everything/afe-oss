import Bzip2.Proofs.Huffman.Decode

/-!
# Proofs: Huffman tables

The oracle's Huffman decoding tables decode as the spec says: `decode_eq_spec`.

* `decode_eq_spec`: for the code lengths of any coding table a stream can carry (1 to 258
  lengths, each in `1 .. 20`: what `BZ2_decompress` checks, `decompress.c:323-333`), reading a
  symbol with `Oracle.Decompress.Huffman.decodeSym` on the tables `Header.parse` builds
  (`DecodeTables.tablesOf`; `Decode.ofLengths_eq`) is reading it with `Spec.Huffman.decodeSym` on
  the bits the reader has left: the same symbol and bits left, `Error.data` where the spec says
  `dataError`, `Error.eof` where it says `needMoreInput`, and the spec never says `staleEntry`.
  Nothing is assumed about the lengths beyond that: incomplete and over-subscribed tables, which
  the decoder accepts (`decompress.c:339-352`), are covered.
-/

namespace Bzip2.Proofs.Huffman

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Proofs.Huffman.Bits
  Bzip2.Proofs.Huffman.DecodeTables Bzip2.Proofs.Huffman.Decode

/-- The oracle's decoding tables decode exactly as the spec's `decodeSym`, on every table the
format can carry: for `length` with between 1 and 258 entries, each in `1 .. 20`, and any reader
`r`, the oracle's result `Oracle.Decompress.Huffman.decodeSym (tablesOf length) r` matches the
spec's `decodeSym` of the code lengths on `bits r`, the bits `r` has left (`Decode.Matches`). -/
theorem decode_eq_spec (length : Array UInt8) (hne : 0 < length.size)
    (hle : length.size ≤ 258) (hlegal : ∀ l ∈ length, 1 ≤ l.toNat ∧ l.toNat ≤ 20)
    (r : BitReader) :
    Matches r (Spec.Huffman.decodeSym (lensOf length) (bits r))
      (Oracle.Decompress.Huffman.decodeSym (tablesOf length) r) :=
  Decode.decode_eq_spec length hne hle hlegal r

end Bzip2.Proofs.Huffman
