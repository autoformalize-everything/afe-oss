/-!
# Oracle errors

The result codes shared by all oracle parts; re-exported by `Bzip2.Oracle`.
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

end Bzip2.Oracle
