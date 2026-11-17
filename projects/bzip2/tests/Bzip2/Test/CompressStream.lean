import Bzip2.Oracle.Compress

/-!
# Oracle stream writer tests

Checks the empty stream and a one-byte block against the vendored `bzip2 -1 -c` output.
The expected bytes exercise the header, block metadata, symbol map, selectors, codes and trailer
of `BZ2_compressBlock` (`compress.c:622-668`).
-/

open Bzip2.Oracle

#guard match compress 1 .empty with
  | .ok z => z == ByteArray.mk #[
      0x42, 0x5a, 0x68, 0x31, 0x17, 0x72, 0x45, 0x38, 0x50, 0x90, 0, 0, 0, 0]
  | .error _ => false

#guard match compress 1 "a".toUTF8 with
  | .ok z => z == ByteArray.mk #[
      0x42, 0x5a, 0x68, 0x31, 0x31, 0x41, 0x59, 0x26, 0x53, 0x59, 0x19, 0x93, 0x9b,
      0x6b, 0, 0, 0, 1, 0, 0x20, 0, 0x20, 0, 0x21, 0x18, 0x46, 0x82, 0xee, 0x48,
      0xa7, 0x0a, 0x12, 0x03, 0x32, 0x73, 0x6d, 0x60]
  | .error _ => false

#guard match compress 0 .empty with
  | .error (.param _) => true
  | _ => false

#guard match compress 10 .empty with
  | .error (.param _) => true
  | _ => false
