import Bzip2.Oracle.Error

/-! Unit tests are `#guard`s and `example`s in a module of their own per part: building this
library runs them. This one is the template. -/

open Bzip2.Oracle

#guard Error.magic == .magic
#guard Error.data "crc" != .eof
#guard (default : Error) == .magic
