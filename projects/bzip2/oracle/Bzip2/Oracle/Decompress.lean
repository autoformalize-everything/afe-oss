import Bzip2.Oracle.Error

/-!
The oracle's decompression API. Task `bzip2/oracle/decompress/stream` implements it here, over
the parts in `Bzip2.Oracle.Decompress.*`; until then it returns `.unimplemented`.
-/

namespace Bzip2.Oracle

/-- Decompresses the one stream at the start of `input`; returns its output and how many bytes
of `input` the stream occupied. Bytes after the stream are not examined. -/
def decompressStream (input : ByteArray) : Except Error (ByteArray × Nat) :=
  let _ := input
  .error (.unimplemented "decompressStream")

/-- Decompresses `input` as `bzip2 -d` does: one or more concatenated streams. -/
def decompress (input : ByteArray) : Except Error ByteArray :=
  let _ := input
  .error (.unimplemented "decompress")

end Bzip2.Oracle
