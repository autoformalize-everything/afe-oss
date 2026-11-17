import Bzip2.Oracle.Decompress.Block

/-!
Tests for `Bzip2.Oracle.Decompress.Block` against what the vendored libbz2 gives for streams of
one block. Every check is a `#guard`, so building this module runs them.

`tests/vectors/decompress-block/*.txt` are streams (`hex`, the stream level `level`) run
through the C library by `../classify.c` (see `regenerate.sh` there), followed by what C
reported: `result` (`ok`, or `data` for `BZ_DATA_ERROR`), and for `ok` the `size` of the
output, a `hash` of it and, up to 4096 bytes, the bytes themselves (`out`).

* `real.txt`: blocks of streams made by the vendored `bzip2`: text, runs of 4, 5, 255, 256 and
  1000 bytes (count bytes), all byte values, a periodic block.
* `blocks.txt`: blocks made by `generate.py`'s encoder: randomised blocks (the flag of bzip2
  before 0.9.5), count bytes 251 to 255, a run of four at the block end (`data`), a flipped
  block CRC (`data`), `origPtr ≥ nblock` (`data`), and a wrong `origPtr` below `nblock`, which
  C accepts when the CRC is that of the bytes it then writes.

The stream of each case has one block, so the result of `decodeBlock` on it, started after the
stream header and the block magic (bit 80), is the result of the stream.
-/

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Header
  Bzip2.Oracle.Decompress.Symbols Bzip2.Oracle.Decompress.Block

namespace Bzip2.Test.DecompressBlock

/-- The cases of a vector file's text: blocks of lines, each ended by an empty line. -/
def cases (text : String) : Array (Array String) :=
  (text.splitOn "\n\n").toArray.map (fun b => (b.splitOn "\n").toArray.filter (· ≠ ""))
    |>.filter (fun b => !b.isEmpty)

/-- The words after the label `key` on the case's line starting with `key`, if there is one. -/
def field (c : Array String) (key : String) : Option (Array String) :=
  (c.find? (fun l => (l.splitOn " ").head! == key)).map
    (fun l => ((l.splitOn " ").drop 1).filter (· ≠ "") |>.toArray)

/-- The first word on the line `key`, or the empty string. -/
def word (c : Array String) (key : String) : String :=
  ((field c key).getD #[])[0]?.getD ""

/-- A hex digit's value. -/
def hexDigit (ch : Char) : UInt8 :=
  (if ch.isDigit then ch.toNat - 48 else ch.toNat - 87).toUInt8

/-- Bytes from contiguous hex digits. -/
def fromHex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut bytes := ByteArray.empty
  for i in [0:s.length / 2] do
    bytes := bytes.push (hexDigit chars[2 * i]! * 16 + hexDigit chars[2 * i + 1]!)
  return bytes

/-- The hash `generate.py` records: `h = h * 31 + byte` in a `UInt32`. -/
def hash (b : ByteArray) : UInt32 := b.foldl (fun h x => h * 31 + x.toUInt32) 0

/-- The stream of a case. -/
def stream (c : Array String) : ByteArray := fromHex (word c "hex")

/-- Whether `decodeBlock` on the stream `z` of level `level` gives the result C reported in
`c`. For `ok`, also: the CRC returned is the stored one (bits 80 to 111), and the reader is
left at the end-of-stream magic. -/
def agreesOn (c : Array String) (level : Nat) (z : ByteArray) : Bool :=
  match decodeBlock level { data := z, pos := 80 }, word c "result" with
  | .error (.data _), "data" => true
  | .ok (out, after), "ok" =>
    out.bytes.size == (word c "size").toNat! &&
    (hash out.bytes).toNat == (word c "hash").toNat! &&
    (match field c "out" with
     | none => out.bytes.size > 4096
     | some _ => out.bytes == fromHex (word c "out")) &&
    (match ({ data := z, pos := 80 } : BitReader).readBits 32 with
     | .ok (stored, _) => stored == out.blockCRC
     | .error _ => false) &&
    (match after.readBits 24 with
     | .ok (hi, r) =>
       hi == 0x177245 && (match r.readBits 24 with | .ok (lo, _) => lo == 0x385090 | _ => false)
     | .error _ => false)
  | _, _ => false

/-- Whether `decodeBlock` on the case's stream gives the result C reported. -/
def agrees (c : Array String) : Bool := agreesOn c (word c "level").toNat! (stream c)

#guard (cases (include_str "../../vectors/decompress-block/real.txt")).all agrees
#guard (cases (include_str "../../vectors/decompress-block/blocks.txt")).all agrees

-- The files hold the cases this module is about (a file that loses cases must fail here).
#guard (cases (include_str "../../vectors/decompress-block/real.txt")).size == 12
#guard (cases (include_str "../../vectors/decompress-block/blocks.txt")).size == 18

/-- The case of `file` whose comment starts with `title`. -/
def named (file title : String) : Array String :=
  ((cases file).find? (fun c => c[0]!.startsWith ("# " ++ title))).getD #[]

/-- The hand-made blocks. -/
def blocks : String := include_str "../../vectors/decompress-block/blocks.txt"

-- The cases the task names, found by their titles: they exist, and with the result intended.
#guard word (named blocks "randomised block, 3 kB") "result" == "ok"
#guard word (named blocks "randomised block, 8 kB") "result" == "ok"
#guard word (named blocks "count byte 255: a run of 259") "result" == "ok"
#guard word (named blocks "four equal bytes end the block") "result" == "data"
#guard word (named blocks "block CRC with one bit flipped") "result" == "data"
#guard word (named blocks "origPtr == nblock (data)") "result" == "data"
#guard word (named blocks "origPtr off by 5, CRC of the rotation") "result" == "ok"

/-- The stream of a case with byte `i` xor-ed with `x`. -/
def flipped (c : Array String) (i : Nat) (x : UInt8) : ByteArray :=
  let z := stream c
  z.set! i (z.get! i ^^^ x)

-- The randomisation flag (the top bit of byte 14) matters: without it the bytes differ, and
-- the CRC fails.
/-- The 3 kB randomised block with its flag cleared. -/
def unflagged : BitReader :=
  { data := flipped (named blocks "randomised block, 3 kB") 14 0x80, pos := 80 }

#guard (match decodeBlock 9 unflagged with
  | .error (.data _) => true | _ => false)
-- `agreesOn` notices a wrong result, size, hash and byte.
#guard !agreesOn ((named blocks "count byte 252").map
  (fun l => if l.startsWith "result" then "result data" else l)) 1
  (stream (named blocks "count byte 252"))
#guard !agrees ((named blocks "count byte 252").map
  (fun l => if l.startsWith "size" then "size 1" else l))
#guard !agrees ((named blocks "count byte 252").map
  (fun l => if l.startsWith "hash" then "hash 1" else l))
#guard !agrees ((named blocks "count byte 252").map
  (fun l => if l.startsWith "out" then "out 00" else l))

/-! `output` on blocks given directly. -/

/-- A header with the fields `output` reads; the others are empty. -/
def hdr (crc : UInt32) (origPtr : Nat) (randomised : Bool := false) : Header :=
  { storedBlockCRC := crc, blockRandomised := randomised, origPtr, usedBytes := #[],
    alphaSize := 0, selectors := #[], tables := #[] }

/-- The `Symbols.Block` of the BWT output `s`: its bytes and their counts. -/
def bwtOut (s : String) : Bzip2.Oracle.Decompress.Symbols.Block :=
  let tt := s.toUTF8.toList.toArray.map UInt8.toUInt32
  { tt, unzftab := (Array.range 256).map fun v => (tt.filter (· == v.toUInt32)).size.toUInt32 }

/-- Whether `output` fails with `Error.data`. -/
def isData : Except Error Output → Bool
  | .error (.data _) => true
  | _ => false

-- "banana": the sorted rotations end in "nnbaaa", and the text is row 3.
#guard (output (hdr (Crc.crc32 "banana".toUTF8) 3) (bwtOut "nnbaaa")).toOption.map
  (·.bytes) == some "banana".toUTF8
-- Started at another row, the walk writes a rotation of the text.
#guard (output (hdr (Crc.crc32 "abanan".toUTF8) 0) (bwtOut "nnbaaa")).toOption.map
  (·.bytes) == some "abanan".toUTF8
-- `origPtr ≥ nblock`, and the empty block.
#guard isData (output (hdr (Crc.crc32 "banana".toUTF8) 6) (bwtOut "nnbaaa"))
#guard isData (output (hdr 0 0) (bwtOut ""))
-- A wrong CRC.
#guard isData (output (hdr (Crc.crc32 "banana".toUTF8 ^^^ 1) 3) (bwtOut "nnbaaa"))
-- A block shorter than 618 bytes is the same randomised or not.
#guard (output (hdr (Crc.crc32 "banana".toUTF8) 3 true) (bwtOut "nnbaaa")).toOption.map
  (·.bytes) == some "banana".toUTF8
-- "qqqq\x02": a run of six; "qqqq" alone: the count is read past the end.
#guard (output (hdr (Crc.crc32 "qqqqqq".toUTF8) 4)
  { tt := #[0x71, 0x71, 0x71, 0x71, 0x02],
    unzftab := (Array.replicate 256 0).set! 0x71 4 |>.set! 2 1 }).toOption.map
  (·.bytes) == some "qqqqqq".toUTF8
#guard isData (output (hdr (Crc.crc32 "qqqq".toUTF8) 0) (bwtOut "qqqq"))
-- A count over `nblock`.
#guard isData (output (hdr (Crc.crc32 "banana".toUTF8) 3)
  { (bwtOut "nnbaaa") with unzftab := (Array.replicate 256 0).set! 0x61 7 })

end Bzip2.Test.DecompressBlock
