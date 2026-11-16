import Bzip2.Oracle.Crc

/-!
# bzip2: the oracle

The executable Lean implementation of bzip2: decompression that accepts and rejects exactly what
the vendored bzip2 (`projects/bzip2/upstream`) does, and compression whose output it decompresses
to the input. The diff fuzzer
compares it with the C library, and `Bzip2.Proofs` proves it meets `Bzip2.Spec`.

The oracle imports Lean core and `Std` only: no Mathlib, no `Bzip2.Spec`, so that the
`bzip2-oracle` executable and the static library the fuzzer links stay small.

Parts go in modules under `Bzip2.Oracle` (`BitIO`, `Crc`, `Decompress.*`, `Compress.*`) and are
imported here. The functions below are the oracle's public API; the CLI, the tests and the
fuzzer's FFI depend on these names and types. Until a part exists, they return
`.unimplemented`.
-/

namespace Bzip2.Oracle

/-- Why a call failed, by libbz2's result codes. -/
inductive Error where
  /-- `BZ_DATA_ERROR_MAGIC`: the input does not start with a bzip2 stream header. -/
  | magic
  /-- `BZ_DATA_ERROR`: the stream is corrupt, including a block or stream CRC mismatch. -/
  | data (detail : String)
  /-- `BZ_UNEXPECTED_EOF`: the input ends inside a stream. -/
  | eof
  /-- `BZ_PARAM_ERROR`: a bad argument, such as a block size level outside 1..9. -/
  | param (detail : String)
  /-- Not implemented yet. -/
  | unimplemented (what : String)
  deriving Repr, BEq, Inhabited

/-- Decompresses the one stream at the start of `input`; returns its output and how many bytes
of `input` the stream occupied. Bytes after the stream are not examined. -/
def decompressStream (input : ByteArray) : Except Error (ByteArray × Nat) :=
  let _ := input
  .error (.unimplemented "decompressStream")

/-- Decompresses `input` as `bzip2 -d` does: one or more concatenated streams. -/
def decompress (input : ByteArray) : Except Error ByteArray :=
  let _ := input
  .error (.unimplemented "decompress")

/-- Compresses `input` as one stream with blocks of `level` × 100 000 bytes, `level` in 1..9,
as `bzip2 -<level>` does. -/
def compress (level : Nat) (input : ByteArray) : Except Error ByteArray :=
  let _ := (level, input)
  .error (.unimplemented "compress")

end Bzip2.Oracle
