import Bzip2.Oracle.Decompress.Symbols

/-!
Tests for `Bzip2.Oracle.Decompress.Symbols` against what the vendored libbz2 leaves behind
after decoding a block's symbols, and against a slow reference. Every check is a `#guard`, so
building this module runs them.

`tests/vectors/decompress-symbols/*.txt` are streams (`hex`, the stream level `level`) run
through the C library by `symbols.c` (see `regenerate.sh` there), followed by what C reported:
`result` (`ok`, `data` for `BZ_DATA_ERROR`, `eof` for input that ran out), and for `ok` the
block's `nblock`, the bit position `pos` after its last symbol, the byte counts `unzftab`, a
`hash` of the block's bytes and, up to 4096 bytes, the bytes themselves (`tt`).

* `real.txt`: blocks of streams made by the vendored `bzip2`.
* `symbols.txt`: small synthetic blocks: several groups and tables, selector order, runs and
  move-to-front.
* `limits.txt`: the limits, each failing with the C error class: a run too long, a block over
  `100000 * level` bytes (and exactly at it), running out of selectors, EOB missing before the
  input ends.

The reference decodes the same symbols into a `List`, undoes the runs and the move-to-front on
lists, and does not share the oracle's loop; it reads symbols with `Huffman.decodeSym` and the
header with `Header.parse`, which have their own tests.
-/

open Bzip2.Oracle Bzip2.Oracle.BitIO Bzip2.Oracle.Decompress.Header
  Bzip2.Oracle.Decompress.Huffman Bzip2.Oracle.Decompress.Symbols

namespace Bzip2.Test.DecompressSymbols

/-- The cases of a vector file's text: blocks of lines, each ended by an empty line. -/
def cases (text : String) : Array (Array String) :=
  (text.splitOn "\n\n").toArray.map (fun b => (b.splitOn "\n").toArray.filter (· ≠ ""))
    |>.filter (fun b => !b.isEmpty)

/-- The words after the label `key` on the case's line starting with `key`, if there is one. -/
def field (c : Array String) (key : String) : Option (Array String) :=
  (c.find? (fun l => (l.splitOn " ").head! == key)).map
    (fun l => ((l.splitOn " ").drop 1).filter (· ≠ "") |>.toArray)

/-- The number on the line `key`. -/
def nat (c : Array String) (key : String) : Nat :=
  ((field c key).getD #[])[0]!.toNat!

/-- A two-digit hex number. -/
def hexByte (s : String) : UInt8 :=
  s.foldl (fun a ch => a * 16 + (if ch.isDigit then ch.toNat - 48 else ch.toNat - 87).toUInt8) 0

/-- Bytes from contiguous hex digits. -/
def fromHex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut bytes := ByteArray.empty
  for i in [0:s.length / 2] do
    bytes := bytes.push (hexByte (String.ofList [chars[2 * i]!, chars[2 * i + 1]!]))
  return bytes

/-- The hash `symbols.c` prints: `h = h * 31 + byte` in a `UInt32`. -/
def hash (tt : Array UInt32) : UInt32 := tt.foldl (fun h b => h * 31 + b) 0

/-- Reads symbols of `h`'s block one by one into a list, 50 to a selector, until EOB, the way
`GET_MTF_VAL` does, with `Huffman.decodeSym`; `fuel` bounds their number. -/
def refSymbols (h : Header) (r : BitReader) (i : Nat) (acc : List Nat) :
    Nat → Except Error (List Nat × BitReader)
  | 0 => .error (.data "reference: out of fuel")
  | fuel + 1 =>
    if h2 : i / groupSize < h.selectors.size then
      match decodeSym h.tables[h.selectors[i / groupSize]]! r with
      | .error e => .error e
      | .ok (s, r) =>
        if s + 1 == h.alphaSize then .ok (acc.reverse, r)
        else refSymbols h r (i + 1) (s :: acc) fuel
    else .error (.data "reference: out of selectors")

/-- The bytes of the symbols `syms`, naively: runs are summed digit by digit and the
move-to-front list is a `List` (`decompress.c:386-487`). `mtf` is the list, `es` and `n` the run
so far and the weight of its next digit, `out` the bytes so far, reversed. -/
def refBytes (used : Array UInt8) (mtf : List Nat) (es n : Nat) (out : List Nat) :
    List Nat → List Nat
  | [] => (List.replicate es (used[mtf.head!]!).toNat ++ out).reverse
  | s :: rest =>
    if s < 2 then refBytes used mtf (es + (s + 1) * n) (2 * n) out rest
    else
      let out := List.replicate es (used[mtf.head!]!).toNat ++ out
      let b := mtf[s - 1]!
      refBytes used (b :: mtf.eraseIdx (s - 1)) 0 1 ((used[b]!).toNat :: out) rest

/-- Whether the oracle's block is what the reference gives: the same bytes, the same counts
and the same position after EOB. -/
def matchesReference (h : Header) (r : BitReader) (b : Block) (after : BitReader) : Bool :=
  match refSymbols h r 0 [] 5000 with
  | .error _ => false
  | .ok (syms, r') =>
    let bytes := refBytes h.usedBytes (List.range 256) 0 1 [] syms
    b.tt.toList.map UInt32.toNat == bytes &&
    (List.range 256).all (fun v => b.unzftab[v]!.toNat == bytes.count v) &&
    r'.bitPos == after.bitPos

/-- Whether `decode` on the case's stream gives the result recorded from C. The block starts at
bit 80, after the stream header and the block magic. -/
def agrees (c : Array String) : Bool :=
  let level := nat c "level"
  let reader : BitReader := { data := fromHex ((field c "hex").getD #[])[0]!, pos := 80 }
  let expected := ((field c "result").getD #[])[0]!
  match parse level reader with
  | .error _ => false
  | .ok (h, r) =>
    match decode level h r, expected with
    | .error (.data _), "data" => true
    | .error .eof, "eof" => true
    | .ok (b, after), "ok" =>
      b.tt.size == nat c "nblock" && after.bitPos == nat c "pos" &&
      ((field c "unzftab").getD #[]).map String.toNat! == b.unzftab.map UInt32.toNat &&
      (hash b.tt).toNat == nat c "hash" &&
      (match field c "tt" with
       | none => true
       | some bytes => bytes.map hexByte == b.tt.map UInt32.toUInt8) &&
      (b.tt.size > 4096 || matchesReference h r b after)
    | _, _ => false

#guard (cases (include_str "../../vectors/decompress-symbols/real.txt")).all agrees
#guard (cases (include_str "../../vectors/decompress-symbols/symbols.txt")).all agrees
#guard (cases (include_str "../../vectors/decompress-symbols/limits.txt")).all agrees

-- The files hold the cases this module is about (a file that loses cases must fail here).
#guard (cases (include_str "../../vectors/decompress-symbols/real.txt")).size == 7
#guard (cases (include_str "../../vectors/decompress-symbols/symbols.txt")).size == 4
#guard (cases (include_str "../../vectors/decompress-symbols/limits.txt")).size == 21

/-- The first case of `symbols.txt`, with `key`'s line replaced by `line`. -/
def tampered (key line : String) : Array String :=
  ((cases (include_str "../../vectors/decompress-symbols/symbols.txt"))[0]!).map
    (fun l => if l.startsWith (key ++ " ") then line else l)

-- `agrees` notices a wrong result, count, position and byte.
#guard agrees (tampered "level" "level 1")
#guard !agrees (tampered "result" "result data")
#guard !agrees (tampered "nblock" "nblock 1")
#guard !agrees (tampered "pos" "pos 1")
#guard !agrees (tampered "hash" "hash 1")
#guard !agrees (tampered "tt" "tt 00")

-- A level outside 1..9 is a parameter error, as for the header (`Header.parse`).
#guard (match decode 0 default (BitReader.ofByteArray ByteArray.empty) with
  | .error (.param _) => true | _ => false)
#guard (match decode 10 default (BitReader.ofByteArray ByteArray.empty) with
  | .error (.param _) => true | _ => false)

end Bzip2.Test.DecompressSymbols
