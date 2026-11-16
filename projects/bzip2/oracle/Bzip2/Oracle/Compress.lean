import Bzip2.Oracle.Error

/-!
The oracle's compression API. Task `bzip2/oracle/compress/stream` implements it here, over the
parts in `Bzip2.Oracle.Compress.*`; until then it returns `.unimplemented`.
-/

namespace Bzip2.Oracle

/-- Compresses `input` as one stream with blocks of `level` × 100 000 bytes, `level` in 1..9,
as `bzip2 -<level>` does. -/
def compress (level : Nat) (input : ByteArray) : Except Error ByteArray :=
  let _ := (level, input)
  .error (.unimplemented "compress")

end Bzip2.Oracle
