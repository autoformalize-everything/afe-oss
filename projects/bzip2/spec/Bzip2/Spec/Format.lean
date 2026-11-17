import Bzip2.Spec.Crc
import Bzip2.Spec.Rle1
import Bzip2.Spec.Bwt
import Bzip2.Spec.MtfRle2
import Bzip2.Spec.Huffman

/-!
# The bzip2 stream format

This is a bit-level decoder for the format accepted by the `bzip2 -d` program. Bytes are
read most significant bit first, and multi-bit integers are big-endian (`decompress.c:43-68`).
The `BZh` header and level come from `decompress.c:197-209`; block magic, CRC, randomisation
flag and 24-bit `origPtr` from `decompress.c:222-264`; the map, selectors and delta-coded
lengths from `decompress.c:266-334`, where selectors past 18002 are read but ignored
(`decompress.c:299-306`); groups of 50 symbols from `decompress.c:74-102`.
The block size and `origPtr` checks are at `decompress.c:358` and
`decompress.c:495-498`; block and combined CRC checks are at `bzlib.c:823-848`.
The end marker and CRC are read at `decompress.c:587-609`. Padding bits are discarded, as the
library stops at the end marker; `bzip2` starts another stream and ignores trailing garbage
after a later magic error (`bzip2.c:435-479`, `bzip2.c:531-543`). An incomplete later header
remains an EOF error (`bzlib.c:1202-1212`).
The compressor writes the header, block fields and trailer at `compress.c:621-665`.

The representation is a list of bytes and a list of bits. This keeps the spec structural and
lets a failed read distinguish exhaustion from a bad field. `.eof` models the file-reading
wrapper's `BZ_UNEXPECTED_EOF`, not a return from `BZ2_bzDecompress` itself.
-/

namespace Bzip2.Spec.Format

/-- The first failure reported by the file-reading decoder. -/
inductive Error where
  | magic
  | data
  | eof
  deriving DecidableEq, Repr

/-- A parser of most-significant-bit-first fields. -/
abbrev Parser (α : Type) := StateT (List Bool) (Except Error) α

/-- The bits of a byte, most significant first. -/
def byteBits (b : UInt8) : List Bool :=
  (List.range 8).reverse.map fun i => b.toNat.testBit i

/-- The bit stream represented by a byte list. -/
def bits (bytes : List UInt8) : List Bool := bytes.flatMap byteBits

/-- Read one bit; an exhausted field is an EOF error. -/
def readBit : Parser Bool := do
  match (← get) with
  | [] => throw .eof
  | b :: bs =>
    set bs
    return b

/-- Read an unsigned big-endian field of `n` bits. -/
def readNat (n : Nat) : Parser Nat := do
  let mut value := 0
  for _ in [:n] do
    value := 2 * value + if (← readBit) then 1 else 0
  return value

/-- Read a byte-sized field. -/
def readByte : Parser Nat := readNat 8

/-- Check a field at the point where the C decoder checks it. -/
def require (p : Bool) (err : Error := .data) : Parser Unit :=
  if p then pure () else throw err

/-- Read the 16 group flags and the 16-bit maps for flagged groups. -/
def readMap : Parser (List UInt8) := do
  let flags ← (List.range 16).mapM fun _ => readBit
  let groups ← (List.range 16).mapM fun i => do
    if flags[i]! then
      let bs ← (List.range 16).mapM fun j => do
        let present ← readBit
        return if present then [UInt8.ofNat (16 * i + j)] else []
      return bs.flatten
    else return []
  let used := groups.flatten
  require (!used.isEmpty)
  return used

/-- Read one unary MTF selector, rejecting an index outside the group count. -/
def readUnary (groups : Nat) : Nat → Nat → Parser Nat
  | 0, _ => throw .data
  | fuel + 1, index => do
    if (← readBit) then
      if index + 1 ≥ groups then throw .data
      else readUnary groups fuel (index + 1)
    else return index

/-- Undo selector move-to-front coding, starting with tables in numerical order. -/
def undoSelectors (groups : Nat) (codes : List Nat) : List Nat :=
  ((codes.foldl (fun (s : List Nat × List Nat) i =>
      let t := s.1.getD i 0
      (t :: s.1.erase t, t :: s.2)) (List.range groups, [])).2).reverse

/-- Read all `nSelectors` selectors but keep only the first 18002, as the C decoder reads the
rest without storing them and then clamps `nSelectors` (`decompress.c:299-306`). -/
def readSelectors : Parser (Nat × List Nat) := do
  let groups ← readNat 3
  require (2 ≤ groups && groups ≤ 6)
  let count ← readNat 15
  require (0 < count)
  let codes ← (List.range count).mapM fun _ => readUnary groups groups 0
  return (groups, undoSelectors groups (codes.take 18002))

/-- Read one length's zero-terminated sequence of up/down deltas. As in
`decompress.c:326-331`, the range check on `curr` precedes each bit read, so an out-of-range
length is a data error even when no bits remain. `fuel` bounds the remaining bits; each step
reads two, so it runs out only after `readBit` has already failed. -/
def readDelta : Nat → Nat → Parser Nat
  | fuel, curr => do
    require (1 ≤ curr && curr ≤ 20)
    if !(← readBit) then return curr
    let down ← readBit
    match fuel with
    | 0 => throw .eof
    | fuel + 1 => readDelta fuel (if down then curr - 1 else curr + 1)

/-- Read one table's code lengths for the entire Huffman alphabet. -/
def readLengths (size : Nat) : Parser (List Nat) := do
  let mut curr ← readNat 5
  let mut lens := []
  for _ in [:size] do
    curr ← readDelta (← get).length curr
    lens := curr :: lens
  return lens.reverse

/-- Read the tables in group order. -/
def readTables (groups size : Nat) : Parser (List Huffman.Lens) :=
  (List.range groups).mapM fun _ => readLengths size

/-- Read one Huffman symbol, keeping the unused suffix of the bit stream. -/
def readSymbol (lens : Huffman.Lens) : Parser Nat := do
  match Huffman.decodeSym lens (← get) with
  | .sym s rest =>
    set rest
    return s
  | .needMoreInput => throw .eof
  | .dataError | .staleEntry => throw .data

/-- Decode symbols in groups of 50, stopping at EOB. A new group's selector is checked before
its first bit is read (`decompress.c:76-79`). The MTF/RLE2 checks run as soon as their
triggering symbol has been read, before any later Huffman failure. `fuel` bounds the
remaining bits; every symbol reads at least one, so it runs out only after a failed read. -/
def readSymbols (level : Nat) (used : List UInt8) (selectors : List Nat)
    (tables : List Huffman.Lens) : Nat → Nat → List Nat → Parser (List UInt8)
  | fuel, index, syms => do
    let some selector := selectors[index / 50]? | throw .data
    let some lens := tables[selector]? | throw .data
    let sym ← readSymbol lens
    let syms := syms ++ [sym]
    match MtfRle2.decode level used syms with
    | .ok block => return block
    | .error .dataError => throw .data
    | .error .needMoreInput =>
      match fuel with
      | 0 => throw .eof
      | fuel + 1 => readSymbols level used selectors tables fuel (index + 1) syms

/-- The historic randomisation table `BZ2_rNums`, in `randtable.c:27-79`. -/
def randomNumbers : List Nat :=
  [619, 720, 127, 481, 931, 816, 813, 233, 566, 247, 985, 724, 205, 454, 863, 491,
   741, 242, 949, 214, 733, 859, 335, 708, 621, 574, 73, 654, 730, 472, 419, 436,
   278, 496, 867, 210, 399, 680, 480, 51, 878, 465, 811, 169, 869, 675, 611, 697,
   867, 561, 862, 687, 507, 283, 482, 129, 807, 591, 733, 623, 150, 238, 59, 379,
   684, 877, 625, 169, 643, 105, 170, 607, 520, 932, 727, 476, 693, 425, 174, 647,
   73, 122, 335, 530, 442, 853, 695, 249, 445, 515, 909, 545, 703, 919, 874, 474,
   882, 500, 594, 612, 641, 801, 220, 162, 819, 984, 589, 513, 495, 799, 161, 604,
   958, 533, 221, 400, 386, 867, 600, 782, 382, 596, 414, 171, 516, 375, 682, 485,
   911, 276, 98, 553, 163, 354, 666, 933, 424, 341, 533, 870, 227, 730, 475, 186,
   263, 647, 537, 686, 600, 224, 469, 68, 770, 919, 190, 373, 294, 822, 808, 206,
   184, 943, 795, 384, 383, 461, 404, 758, 839, 887, 715, 67, 618, 276, 204, 918,
   873, 777, 604, 560, 951, 160, 578, 722, 79, 804, 96, 409, 713, 940, 652, 934,
   970, 447, 318, 353, 859, 672, 112, 785, 645, 863, 803, 350, 139, 93, 354, 99,
   820, 908, 609, 772, 154, 274, 580, 184, 79, 626, 630, 742, 653, 282, 762, 623,
   680, 81, 927, 626, 789, 125, 411, 521, 938, 300, 821, 78, 343, 175, 128, 250,
   170, 774, 972, 275, 999, 639, 495, 78, 352, 126, 857, 956, 358, 619, 580, 124,
   737, 594, 701, 612, 669, 112, 134, 694, 363, 992, 809, 743, 168, 974, 944, 375,
   748, 52, 600, 747, 642, 182, 862, 81, 344, 805, 988, 739, 511, 655, 814, 334,
   249, 515, 897, 955, 664, 981, 649, 113, 974, 459, 893, 228, 433, 837, 553, 268,
   926, 240, 102, 654, 459, 51, 686, 754, 806, 760, 493, 403, 415, 394, 687, 700,
   946, 670, 656, 610, 738, 392, 760, 799, 887, 653, 978, 321, 576, 617, 626, 502,
   894, 679, 243, 440, 680, 879, 194, 572, 640, 724, 926, 56, 204, 700, 707, 151,
   457, 449, 797, 195, 791, 558, 945, 679, 297, 59, 87, 824, 713, 663, 412, 693,
   342, 606, 134, 108, 571, 364, 631, 212, 174, 643, 304, 329, 343, 97, 430, 751,
   497, 314, 983, 374, 822, 928, 140, 206, 73, 263, 980, 736, 876, 478, 430, 305,
   170, 514, 364, 692, 829, 82, 855, 953, 676, 246, 369, 970, 294, 750, 807, 827,
   150, 790, 288, 923, 804, 378, 215, 828, 592, 281, 565, 555, 710, 82, 896, 831,
   547, 261, 524, 462, 293, 465, 502, 56, 661, 821, 976, 991, 658, 869, 905, 758,
   745, 193, 768, 550, 608, 933, 378, 286, 215, 979, 792, 961, 61, 688, 793, 644,
   986, 403, 106, 366, 905, 644, 372, 567, 466, 434, 645, 210, 389, 550, 919, 135,
   780, 773, 635, 389, 707, 100, 626, 958, 165, 504, 920, 176, 193, 713, 857, 265,
   203, 50, 668, 108, 645, 990, 626, 197, 510, 357, 358, 850, 858, 364, 936, 638]

/-- Undo the historic block randomisation before RLE1 (`bzlib_private.h:137-149`,
`decompress.c:574-577`, `bzlib.c:563-586`). -/
def derandomise (xs : List UInt8) : List UInt8 := Id.run do
  let mut remaining := 0
  let mut position := 0
  let mut out := []
  for x in xs do
    if remaining = 0 then
      remaining := randomNumbers.getD position 0
      position := (position + 1) % 512
    remaining := remaining - 1
    out := (if remaining = 1 then x ^^^ 1 else x) :: out
  return out.reverse

/-- Read and decode one block, including its decoded-byte CRC. -/
def readBlock (level : Nat) : Parser (List UInt8 × BitVec 32) := do
  let storedCrc ← readNat 32
  let randomised ← readBit
  let origPtr ← readNat 24
  require (origPtr ≤ 10 + MtfRle2.maxBlock level)
  let used ← readMap
  let (groups, selectors) ← readSelectors
  let tables ← readTables groups (used.length + 2)
  let lastColumn ← readSymbols level used selectors tables (← get).length 0 []
  require (origPtr < lastColumn.length)
  let rle := Bwt.decodeBwt lastColumn origPtr
  let rle := if randomised then derandomise rle else rle
  require (match (Rle1.decState rle).run with
    | some (_, 4) => false
    | _ => true)
  let output := Rle1.decodeRle1 rle
  let crc := Crc.blockCrc (output.map fun b => BitVec.ofNat 8 b.toNat)
  require (crc.toNat == storedCrc)
  return (output, crc)

/-- Consume unused bits of the trailer's final byte. Their values are not checked. -/
def discardPadding : Parser Unit := do
  let count := (← get).length % 8
  let _ ← readNat count

/-- Read blocks until the end marker, checking the combined CRC. -/
def readBlocks (level : Nat) : Nat → List UInt8 → BitVec 32 → Parser (List UInt8)
  | 0, _, _ => throw .eof
  | fuel + 1, output, combined => do
    let first ← readByte
    if first = 0x17 then
      for expected in [0x72, 0x45, 0x38, 0x50, 0x90] do
        require ((← readByte) == expected)
      let stored ← readNat 32
      require (combined.toNat == stored)
      discardPadding
      return output
    else
      require (first == 0x31)
      for expected in [0x41, 0x59, 0x26, 0x53, 0x59] do
        require ((← readByte) == expected)
      let (block, crc) ← readBlock level
      readBlocks level fuel (output ++ block) (Crc.combineCrc combined crc)

/-- Read one `BZh` stream, returning its level and decoded bytes. -/
def readStream : Parser (Nat × List UInt8) := do
  for expected in [0x42, 0x5a, 0x68] do
    require ((← readByte) == expected) .magic
  let levelByte ← readByte
  require (0x31 ≤ levelByte && levelByte ≤ 0x39) .magic
  let level := levelByte - 0x30
  let output ← readBlocks level (← get).length [] 0#32
  return (level, output)

/-- Decode successive streams as `bzip2 -d` does. A magic error after a complete stream
means trailing garbage; an EOF or data error in that position is still reported. -/
def decodeAll : Nat → List Bool → List UInt8 → Bool → Except Error (List UInt8)
  | 0, _, _, _ => .error .eof
  | fuel + 1, input, output, completed =>
    match readStream input with
    | .error .magic => if completed then .ok output else .error .magic
    | .error e => .error e
    | .ok ((_, block), rest) =>
      if rest.isEmpty then .ok (output ++ block)
      else decodeAll fuel rest (output ++ block) true

/-- The output of `bzip2 -d`, or its first format failure. -/
def decode (input : List UInt8) : Except Error (List UInt8) :=
  decodeAll (input.length + 1) (bits input) [] false

/-- The input stream decodes to these bytes under `bzip2 -d`'s concatenation rules. -/
def Decodes (input output : List UInt8) : Prop := decode input = .ok output

instance (input output : List UInt8) : Decidable (Decodes input output) := by
  unfold Decodes
  infer_instance

/-- A compressor result is one complete stream of the requested level, decoding to its input.
The block decoder checks the size bound and both CRCs. -/
def ValidCompression (level : Nat) (input output : List UInt8) : Prop :=
  1 ≤ level ∧ level ≤ 9 ∧
    readStream (bits output) = .ok ((level, input), [])

/-- `printf x | bzip2 -c`: a complete one-byte stream from the program. -/
example : Decodes
    [0x42, 0x5a, 0x68, 0x39, 0x31, 0x41, 0x59, 0x26, 0x53, 0x59,
     0x77, 0x4b, 0xb0, 0x14, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00,
     0x40, 0x20, 0x00, 0x21, 0x18, 0x46, 0x82, 0xee, 0x48, 0xa7,
     0x0a, 0x12, 0x0e, 0xe9, 0x76, 0x02, 0x80] [120] := by
  decide +kernel

/-- An empty `bzip2 -c` stream, followed by another empty stream. -/
example : Decodes
    ([0x42, 0x5a, 0x68, 0x39, 0x17, 0x72, 0x45, 0x38, 0x50, 0x90, 0, 0, 0, 0] ++
     [0x42, 0x5a, 0x68, 0x39, 0x17, 0x72, 0x45, 0x38, 0x50, 0x90, 0, 0, 0, 0]) [] := by
  decide +kernel

/-- The first malformed header gives a magic failure. -/
example : decode [0x42, 0x5a, 0x68, 0x30] = .error .magic := by decide +kernel

/-- An incomplete header is an EOF failure before its level can be checked. -/
example : decode [0x42, 0x5a, 0x68] = .error .eof := by decide +kernel

/-- A block whose input ends right after the first code length's 5-bit `curr`, which is 0.
The range check precedes the next bit read (`decompress.c:326-328`), so `bzip2 -d` reports
a data error; one byte fewer ends inside the selectors and is an EOF failure. -/
example : decode
    [0x42, 0x5a, 0x68, 0x39, 0x31, 0x41, 0x59, 0x26, 0x53, 0x59,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x40,
     0x00, 0x20, 0x01, 0x00, 0x00] = .error .data := by decide +kernel

example : decode
    [0x42, 0x5a, 0x68, 0x39, 0x31, 0x41, 0x59, 0x26, 0x53, 0x59,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x40,
     0x00, 0x20, 0x01, 0x00] = .error .eof := by decide +kernel

/-- A block with one selector whose input ends after 50 one-bit symbols. The missing
selector for the 51st symbol is checked before its bits are read (`decompress.c:76-79`), so
`bzip2 -d` reports a data error; one byte fewer is an EOF failure. -/
example : decode
    [0x42, 0x5a, 0x68, 0x39, 0x31, 0x41, 0x59, 0x26, 0x53, 0x59,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x60,
     0x00, 0x20, 0x00, 0x21, 0x27, 0xa8, 0x2b, 0x4f, 0x50, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00] = .error .data := by decide +kernel

example : decode
    [0x42, 0x5a, 0x68, 0x39, 0x31, 0x41, 0x59, 0x26, 0x53, 0x59,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x60,
     0x00, 0x20, 0x00, 0x21, 0x27, 0xa8, 0x2b, 0x4f, 0x50, 0x00,
     0x00, 0x00, 0x00, 0x00] = .error .eof := by decide +kernel

end Bzip2.Spec.Format
