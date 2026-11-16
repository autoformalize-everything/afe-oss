import Bzip2.Oracle.Crc

/-! What task `bzip2/oracle/crc` provides. -/

open Bzip2.Oracle.Crc

#check (crc32 : ByteArray → UInt32)
#check (combine : UInt32 → UInt32 → UInt32)
#guard crc32 "123456789".toUTF8 == 0xFC891918
#guard crc32 .empty == 0
