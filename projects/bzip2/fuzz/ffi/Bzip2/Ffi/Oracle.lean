import Bzip2.Oracle.Error
import Bzip2.Oracle.Decompress
import Bzip2.Oracle.Compress

/-!
The C-facing oracle calls. Each exported function accepts a `ByteArray` and returns a status,
output bytes, and a consumed input length. The length is meaningful for one-stream decompression;
the other calls report zero. The C shim owns copying and releasing these buffers.

The error numbers match libbz2's public codes (`bzlib.h:42-55`), with -10 reserved for an
unfinished oracle API. A bad stream header is `BZ_DATA_ERROR_MAGIC` (`decompress.c:197-208`).
The one-stream and concatenated-stream entry points are distinct: libbz2's
`BZ2_bzBuffToBuffDecompress` stops on one stream (`bzlib.c:1330-1351`), while the oracle's
`decompress` API accepts concatenated streams.
-/

namespace Bzip2.Ffi.Oracle

/-- Status and output of a C-facing oracle call. -/
structure Result where
  /-- A libbz2 error number, zero on success, or -10 for unfinished oracle code. -/
  code : Int32
  /-- The output bytes, empty on failure. -/
  output : ByteArray
  /-- The number of input bytes used by one stream, zero otherwise. -/
  consumed : UInt64

/-- The C status code corresponding to an oracle error. -/
def errorCode : Bzip2.Oracle.Error → Int32
  | .magic => -5
  | .data _ => -4
  | .eof => -7
  | .param _ => -2
  | .unimplemented _ => -10

/-- The result of decompressing all concatenated streams. -/
@[export bzip2_oracle_lean_decompress]
def decompress (input : ByteArray) : Result :=
  match Bzip2.Oracle.decompress input with
  | .ok output => ⟨0, output, 0⟩
  | .error err => ⟨errorCode err, ByteArray.empty, 0⟩

/-- The result of decompressing the first stream in the input. -/
@[export bzip2_oracle_lean_decompress_stream]
def decompressStream (input : ByteArray) : Result :=
  match Bzip2.Oracle.decompressStream input with
  | .ok (output, consumed) => ⟨0, output, consumed.toUInt64⟩
  | .error err => ⟨errorCode err, ByteArray.empty, 0⟩

/-- The result of compressing one stream at a block size level from 1 to 9. -/
@[export bzip2_oracle_lean_compress]
def compress (level : UInt32) (input : ByteArray) : Result :=
  match Bzip2.Oracle.compress level.toNat input with
  | .ok output => ⟨0, output, 0⟩
  | .error err => ⟨errorCode err, ByteArray.empty, 0⟩

end Bzip2.Ffi.Oracle
