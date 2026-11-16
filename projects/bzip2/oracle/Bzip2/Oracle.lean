import Bzip2.Oracle.Error
import Bzip2.Oracle.Decompress
import Bzip2.Oracle.Compress

/-!
# bzip2: the oracle

The executable Lean implementation of bzip2: decompression that accepts and rejects exactly what
the vendored bzip2 (`projects/bzip2/upstream`) does, and compression whose output it decompresses
to the input. The diff fuzzer compares it with the C library, and `Bzip2.Proofs` proves it meets
`Bzip2.Spec`.

The oracle imports Lean core and `Std` only: no Mathlib, no `Bzip2.Spec`, so that the
`bzip2-oracle` executable and the static library the fuzzer links stay small.

This module is the public API, for the CLI, the tests and the fuzzer's FFI to import: `Error`
(`Bzip2.Oracle.Error`), `decompressStream` and `decompress` (`Bzip2.Oracle.Decompress`), and
`compress` (`Bzip2.Oracle.Compress`). It is not edited by tasks (`tools/check-sources.sh` rejects
it). Each part is its own module under `Bzip2.Oracle` (`BitIO`, `Crc`, `Decompress.*`,
`Compress.*`); Lake builds them all, and a module imports the parts it needs directly, with
`Bzip2.Oracle.Error` for the error type.
-/
