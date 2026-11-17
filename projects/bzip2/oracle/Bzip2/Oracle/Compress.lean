import Bzip2.Oracle.Compress.Stream

/-!
The oracle's compression API. The stream writer follows `BZ2_compressBlock`
(`compress.c:602-668`); invalid block levels are rejected as by `BZ2_bzCompressInit`
(`bzlib.c:154-161`).
-/

namespace Bzip2.Oracle

/-- Compresses `input` as one stream with blocks of `level` × 100 000 bytes, `level` in 1..9,
as `bzip2 -<level>` does. -/
def compress (level : Nat) (input : ByteArray) : Except Error ByteArray :=
  if level < 1 || level > 9 then .error (.param "compress: level must be in 1..9")
  else .ok (Compress.Stream.compress level input)

end Bzip2.Oracle
