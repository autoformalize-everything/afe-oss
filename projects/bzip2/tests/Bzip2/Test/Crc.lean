import Bzip2.Oracle.Crc

/-! Unit tests of `Bzip2.Oracle.Crc`. The table entries are those of `upstream/crctable.c`:
entries 0-3 (line 35), 128 (line 67), 252-255 (line 98). -/

open Bzip2.Oracle.Crc

#guard crc32 "123456789".toUTF8 == 0xFC891918
#guard crc32 .empty == 0
#guard crc32 "xx123456789yy".toUTF8 2 11 == 0xFC891918
#guard crc32 "123456789".toUTF8 0 0 == 0
-- the range is clamped to the array
#guard crc32 "123456789".toUTF8 0 100 == 0xFC891918
#guard crc32 "123456789".toUTF8 20 30 == 0

#guard table.size == 256
#guard table[0]! == 0x00000000
#guard table[1]! == 0x04c11db7
#guard table[2]! == 0x09823b6e
#guard table[3]! == 0x0d4326d9
#guard table[128]! == 0x690ce0ee
#guard table[252]! == 0xbcb4666d
#guard table[253]! == 0xb8757bda
#guard table[254]! == 0xb5365d03
#guard table[255]! == 0xb1f740b4

-- `compress.c:607-608`: rotate left by one, then xor
#guard combine 0 0x1234 == 0x1234
#guard combine 0x80000001 0x10 == 0x13
#guard combine 0x40000000 0 == 0x80000000
