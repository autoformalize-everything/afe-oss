import Bzip2.Oracle

/-! What task `bzip2/oracle/decompress/stream` provides: the decompression API, implemented.
The 14 bytes are `bzip2 -9 < /dev/null`: header, end-of-stream magic, combined CRC 0. -/

open Bzip2.Oracle

/-- The empty stream. -/
def emptyStream : ByteArray :=
  ⟨#[0x42, 0x5A, 0x68, 0x39, 0x17, 0x72, 0x45, 0x38, 0x50, 0x90, 0, 0, 0, 0]⟩

#guard match decompress emptyStream with
  | .ok out => out.size == 0
  | .error _ => false
#guard match decompressStream emptyStream with
  | .ok (out, used) => out.size == 0 && used == 14
  | .error _ => false
#guard match decompress "not a bzip2 stream".toUTF8 with
  | .error .magic => true
  | _ => false
#guard match decompress (emptyStream.extract 0 10) with
  | .error .eof => true
  | _ => false
