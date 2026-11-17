import Bzip2.Oracle.Compress.Blocks
import Bzip2.Oracle.Crc

/-!
Tests for `Bzip2.Oracle.Compress.Blocks`; every check is a `#guard`, so building this module runs
them.

* Hand-computed RLE1 of short runs (`bzlib.c:216-247`) and the cut of runs at 255
  (`bzlib.c:276`), the empty input (no blocks), and the block CRC against `Crc.crc32` of the
  original bytes.
* `tests/vectors/compress-blocks/*.txt`: for inputs around the block limit of level 1 and level 9
  (`nblockMAX = 99 981` and `899 981`, `bzlib.c:194`), the blocks the vendored libbz2 builds:
  `nblock`, `blockCRC`, an FNV-1a hash of the block's bytes and `inUse`, as printed by a debug
  line added (out of tree) at the top of `BZ2_compressBlock` (`generate.py` there). Each input is
  given once as `bzip2` drives the library and once as `BZ2_bzBuffToBuffCompress` does. A vector
  file is embedded with `include_str`; its first line describes the input (see `makeInput`).
-/

open Bzip2.Oracle.Compress.Blocks

namespace Bzip2.Test.CompressBlocks

/-- A block of `n` copies of `b`. -/
def rep (b : UInt8) (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n b)

/-- The `n` bytes `0, 1, …, 255, 0, …`. -/
def seqBytes (n : Nat) : ByteArray := ByteArray.mk ((Array.range n).map fun i => (i % 256).toUInt8)

/-- `n` runs of four bytes, alternately 10 and 11. -/
def pairsBytes (n : Nat) : ByteArray :=
  (List.range n).foldl (fun acc j => acc ++ rep (10 + (j % 2).toUInt8) 4) ByteArray.empty

/-- The input a vector's `input` line describes: `run B N`, `seq N` and `pairs N` segments. -/
partial def makeInput : List String → ByteArray
  | "run" :: b :: n :: rest => rep b.toNat!.toUInt8 n.toNat! ++ makeInput rest
  | "seq" :: n :: rest => seqBytes n.toNat! ++ makeInput rest
  | "pairs" :: n :: rest => pairsBytes n.toNat! ++ makeInput rest
  | _ => ByteArray.empty

/-- FNV-1a over the bytes, as the C debug line computes it. -/
def fnv (data : ByteArray) : UInt32 :=
  data.foldl (fun h b => (h ^^^ b.toUInt32) * 16777619) 2166136261

/-- `n` as a lowercase hex digit string, padded to `width` digits. -/
def hex (n width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (width - s.length) ++ s

/-- A block as a vector line: `block nblock blockCRC fnv inUse`. -/
def render (b : Block) : String :=
  let nibble (q : Nat) : Nat :=
    (List.range 4).foldl (fun a k => a + (if b.inUse[q + k]! then 1 <<< k else 0)) 0
  s!"block {b.data.size} {hex b.crc.toNat 8} {hex (fnv b.data).toNat 8} " ++
    String.join ((List.range 64).map fun i => hex (nibble (4 * i)) 1)

/-- Whether `split` gives, for the vector's input, level and mode, the blocks in the vector. -/
def agrees (text : String) : Bool :=
  let l := text.splitOn "\n" |>.filter (· ≠ "")
  let input := makeInput ((l[0]!.splitOn " ").drop 1)
  let level := ((l[1]!.splitOn " ")[1]!).toNat!
  let part (name nextName : String) : List String :=
    (l.dropWhile (· ≠ name) |>.drop 1).takeWhile (· ≠ nextName)
  (split level input false).toList.map render == part "program" "oneshot" &&
    (split level input true).toList.map render == part "oneshot" "program"

/-- The `nblock`s of `split`'s blocks. -/
def sizes (level : Nat) (input : ByteArray) (oneShot : Bool := false) : List Nat :=
  (split level input oneShot).toList.map (·.data.size)

-- RLE1: a run of one to three bytes is kept; four or more become four bytes and a count.
#guard (split 1 (rep 97 3)).map (·.data.toList) == #[[97, 97, 97]]
#guard (split 1 (rep 97 4)).map (·.data.toList) == #[[97, 97, 97, 97, 0]]
#guard (split 1 (rep 97 5)).map (·.data.toList) == #[[97, 97, 97, 97, 1]]
#guard (split 1 (rep 97 255)).map (·.data.toList) == #[[97, 97, 97, 97, 251]]
-- A run is cut at 255: 600 = 255 + 255 + 90.
#guard (split 1 (rep 97 600)).map (·.data.toList) ==
  #[[97, 97, 97, 97, 251, 97, 97, 97, 97, 251, 97, 97, 97, 97, 86]]
#guard (split 1 (rep 97 256)).map (·.data.toList) == #[[97, 97, 97, 97, 251, 97]]
#guard (split 1 ("aabbbc".toUTF8)).map (·.data.toList) == #[[97, 97, 98, 98, 98, 99]]
-- `inUse` has the byte and the count byte.
#guard (List.range 256).filter (fun i => (split 1 (rep 97 600))[0]!.inUse[i]!) == [86, 97, 251]
-- No input, no block.
#guard (split 1 ByteArray.empty).size == 0
#guard (split 9 ByteArray.empty true).size == 0

-- The block CRC is over the original bytes: one block, and a block cut at a run's start.
#guard (split 1 (rep 97 600))[0]!.crc == Bzip2.Oracle.Crc.crc32 (rep 97 600)
#guard (split 1 "hello".toUTF8)[0]!.crc == Bzip2.Oracle.Crc.crc32 "hello".toUTF8
-- 99 982 distinct bytes: the first block is full after 99 981 bytes; the byte pending then is a
-- block of its own (as `bzip2` runs the library) or part of the full block (one `BZ_FINISH`).
#guard sizes 1 (seqBytes 99982) == [99981, 1]
#guard sizes 1 (seqBytes 99982) true == [99982]
#guard (split 1 (seqBytes 99982))[0]!.crc == Bzip2.Oracle.Crc.crc32 (seqBytes 99981)
#guard (split 1 (seqBytes 99982))[1]!.crc ==
  Bzip2.Oracle.Crc.crc32 ((seqBytes 99982).extract 99981 99982)

-- Level 1, `nblockMAX = 99 981`.
#guard agrees (include_str "../../vectors/compress-blocks/empty-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/byte-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/short-runs-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99980-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99981-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99982-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99983-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq199964-l1.txt")
-- Runs of 255, 256 and 511 bytes: cut at 255.
#guard agrees (include_str "../../vectors/compress-blocks/run255-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/run256-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/run511-l1.txt")
-- A long run after `k` distinct bytes, for `k` from 99 974 to 99 983: the run straddles the
-- limit, and the block that is closed has the run's first bytes or none of it.
#guard agrees (include_str "../../vectors/compress-blocks/seq99974-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99976-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99978-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99980-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99981-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99982-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99983-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99978-run255-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq99978-run256-l1.txt")
-- Runs of four bytes, five output bytes each, up to the limit.
#guard agrees (include_str "../../vectors/compress-blocks/pairs19996-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/pairs19996-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/pairs19997-run600-l1.txt")
#guard agrees (include_str "../../vectors/compress-blocks/run100000-seq99900-l1.txt")

-- Level 9, `nblockMAX = 899 981`.
#guard agrees (include_str "../../vectors/compress-blocks/empty-l9.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq899981-l9.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq899982-l9.txt")
#guard agrees (include_str "../../vectors/compress-blocks/seq899977-run600-l9.txt")

