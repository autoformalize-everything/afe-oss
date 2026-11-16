import Bzip2.Oracle

/-! What task `bzip2/oracle/compress/stream` provides: the compression API, implemented.
The 14 bytes are `bzip2 -9 < /dev/null`. -/

open Bzip2.Oracle

#guard match compress 9 .empty with
  | .ok z => z.data == #[0x42, 0x5A, 0x68, 0x39, 0x17, 0x72, 0x45, 0x38, 0x50, 0x90, 0, 0, 0, 0]
  | .error _ => false
#guard match compress 1 "hello hello hello hello".toUTF8 with
  | .ok z => z.size > 14 && z.data.extract 0 4 == #[0x42, 0x5A, 0x68, 0x31]
  | .error _ => false
#guard match compress 0 .empty with
  | .error (.param _) => true
  | _ => false
#guard match compress 10 .empty with
  | .error (.param _) => true
  | _ => false
