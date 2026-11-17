import Mathlib.Data.List.Basic

/-!
# bzip2: the initial run-length encoding (RLE1)

The first transform the compressor applies to the input bytes and the last one the decompressor
undoes. A run of 4 to 255 equal bytes is written as 4 copies followed by a count byte
(0..251) of *further* copies; runs of 1 to 3 bytes are copied unchanged.

Everything here is about the bytes of *one block*. When a block fills, the compressor writes it
without flushing the pending run (`bzlib.c:390-392`); `prepare_new_block` leaves that run intact
(`bzlib.c:117-126`), so it is written wholly in the next block. A flush or finish does write the
pending run (`bzlib.c:384-386`). Block boundaries belong to `Bzip2.Spec.Format`. So does the
de-randomisation of blocks with the `blockRandomised` bit, which is applied to the bytes
*before* this stage (`BZ_RAND_UPD_MASK` in the randomised branch of `bzlib.c:538-590`), and the
CRC, which is over the decoded bytes.

References are to `projects/bzip2/upstream/bzlib.c` (commit f5dfc96) unless stated otherwise.

## The decoder: `decodeRle1`

`unRLE_obuf_to_output_FAST` (`bzlib.c:536`) and `unRLE_obuf_to_output_SMALL` (`bzlib.c:706`)
have the same logic and differ only in how the next byte is fetched; `decodeRle1` models both.
The decoder holds the byte `k0` and reads on: after `k0` it reads up to three more bytes, stopping
at the first one that differs from `k0`; if all three are equal, 4 bytes are equal and the *next*
byte is read unconditionally as a count (`bzlib.c:659`; alike `bzlib.c:584`, `bzlib.c:754`,
`bzlib.c:799`).

Edge cases, each decided in `bzlib.c`:

1. **Runs of 1 to 3 equal bytes** are copied (`state_out_len` set to 1, 2 or 3 and the run
   ended by a different byte, `bzlib.c:639-657`, the non-randomised FAST branch; the others
   are alike).
2. **Four equal bytes** are always followed by a count byte `c`, and the run is `4 + c`
   copies (`state_out_len = k1 + 4`, `bzlib.c:659`; alike `bzlib.c:584`, `bzlib.c:754`,
   `bzlib.c:799`). Nothing in the decoder restricts `c`.
3. **Count bytes above 251** (252..255) are accepted: the run is then 256..259 bytes, longer than
   a compressor ever writes (it cuts runs at 255, so `c ≤ 251`). No error is raised.
4. **After a count byte the run state is reset.** The byte read right after the count (`k0`,
   `bzlib.c:660`) starts a fresh run, even if it equals the run's byte: `a a a a 0 a a a a 0`
   decodes to 8 copies of `a`, and `a a a a 0 a` to 5.
5. **A block that ends right after 4 equal bytes** (no count byte) is rejected. The end-of-block
   checks (`nblock_used == save_nblock+1`, `bzlib.c:639-657`, the non-randomised FAST branch;
   the others are alike) follow only the first three reads; there is none before the count read
   (`bzlib.c:658-659`). So the decoder fetches the count
   byte past the end of the block, then `k0` once more, and `nblock_used` reaches
   `save_nblock+2`. The run is written, and then `nblock_used > save_nblock+1` makes the function
   return `True` (`bzlib.c:560`, `bzlib.c:633`, `bzlib.c:730`, `bzlib.c:779`) and
   `BZ2_bzDecompress` return `BZ_DATA_ERROR` (`bzlib.c:823`), before the block CRC is looked at.
   The written run has length `4 + garbage`: the byte the inverse-BWT walk yields past the end
   of the block (not a function of this module's input). `decodeRle1` returns just the 4
   bytes for this case and `Rle1.Truncated` says that it happened; decoding as a whole fails on
   such a block, so that output is irrelevant.
6. **A block that ends after a run of fewer than 4 bytes, or right after a count byte**, is fine
   (`nblock_used == save_nblock+1` gives `return False`, no error: `bzlib.c:557`,
   `bzlib.c:637-638`, `bzlib.c:727`, `bzlib.c:776`).
7. **The empty block** cannot reach this stage: `origPtr >= nblock` is rejected first
   (`decompress.c:497`), so a block has at least one byte. `decodeRle1 [] = []` anyway.

## The encoder: `encodeRle1`

`ADD_CHAR_TO_BLOCK` (`bzlib.c:260-285`) keeps the pending run `(state_in_ch, state_in_len)`. A byte
that equals it extends the run, unless the run already has 255 bytes (`state_in_len == 255`,
`bzlib.c:275-276`); otherwise the pending run is written by `add_pair_to_block`
(`bzlib.c:216-248`) and the byte starts a new one. Written: 1 to 3 bytes verbatim, otherwise
4 copies and the byte `len - 4` (`bzlib.c:237-245`); `flush_RL` (`bzlib.c:252-256`) writes the last
run. So a run of 256 equal bytes becomes the 255-run (`a a a a 251`) and then a single `a`; a run
of 259 becomes `a a a a 251 a a a a 0`. `encodeRle1` models the same state machine.
(The compressor also stops filling a block early, `bzlib.c:298`; that is a block-boundary matter.)
-/

namespace Bzip2.Spec.Rle1

/-- The decoder's state: the output so far, and the byte of the current run with the number of
equal bytes seen (`none` before the first byte and right after a count byte). A run of length 4
means that the next byte is a count. -/
structure DecState where
  /-- The bytes written so far. -/
  out : List UInt8 := []
  /-- The byte of the current run and how many equal bytes were seen, if a run is open. -/
  run : Option (UInt8 × Nat) := none

/-- Consume one byte (`k1`) of the RLE1 block. -/
def decStep (s : DecState) (x : UInt8) : DecState :=
  match s.run with
  | some (c, 4) => { out := s.out ++ List.replicate x.toNat c, run := none }
  | some (c, n) =>
      if x = c then { out := s.out ++ [x], run := some (c, n + 1) }
      else { out := s.out ++ [x], run := some (x, 1) }
  | none => { out := s.out ++ [x], run := some (x, 1) }

/-- The decoder's state after all bytes of a block. -/
def decState (xs : List UInt8) : DecState := xs.foldl decStep {}

/-- The block ends right after 4 equal bytes, with no count byte: the C decoder reports
`BZ_DATA_ERROR` (edge case 5). -/
def Truncated (xs : List UInt8) : Prop :=
  ∃ c, (decState xs).run = some (c, 4)

/-- The state machine of the compressor (`state_in_ch`, `state_in_len`): the output so far and
the pending run. -/
structure EncState where
  /-- The RLE1 bytes written so far. -/
  out : List UInt8 := []
  /-- The pending run: its byte and length (`state_in_ch`, `state_in_len`), if any. -/
  run : Option (UInt8 × Nat) := none

/-- What `add_pair_to_block` writes for a run of `n` copies of `c` (`bzlib.c:216-248`). -/
def pair (c : UInt8) (n : Nat) : List UInt8 :=
  if n < 4 then List.replicate n c else List.replicate 4 c ++ [UInt8.ofNat (n - 4)]

/-- `ADD_CHAR_TO_BLOCK` (`bzlib.c:260-285`). -/
def encStep (s : EncState) (x : UInt8) : EncState :=
  match s.run with
  | none => { s with run := some (x, 1) }
  | some (c, n) =>
      if x = c ∧ n < 255 then { s with run := some (c, n + 1) }
      else { out := s.out ++ pair c n, run := some (x, 1) }

/-- `flush_RL` (`bzlib.c:252-257`): write the pending run. -/
def encFlush (s : EncState) : List UInt8 :=
  match s.run with
  | none => s.out
  | some (c, n) => s.out ++ pair c n

/-- The RLE1 decoder, as `unRLE_obuf_to_output_FAST`/`_SMALL` behave on any byte string. On a
block that ends right after 4 equal bytes (see `Rle1.Truncated`), where C fails, the result is
what was decoded so far. See the module doc for the edge cases. -/
def decodeRle1 (xs : List UInt8) : List UInt8 := (decState xs).out

/-- The RLE1 encoder of the compressor (`ADD_CHAR_TO_BLOCK`, `add_pair_to_block`): runs are cut
at 255 bytes. -/
def encodeRle1 (xs : List UInt8) : List UInt8 := encFlush (xs.foldl encStep {})

/-- The roundtrip statement: decoding what the compressor wrote gives the input back. Left to
`bzip2/proofs/rle`, not proved here. -/
def Rle1Roundtrip : Prop := ∀ x : List UInt8, decodeRle1 (encodeRle1 x) = x

private def rep (b : UInt8) (n : Nat) : List UInt8 := List.replicate n b

-- Runs of 3, 4, 5, 255 and 256 equal bytes, encoding.
example : encodeRle1 (rep 7 3) = [7, 7, 7] := by decide +kernel
example : encodeRle1 (rep 7 4) = [7, 7, 7, 7, 0] := by decide +kernel
example : encodeRle1 (rep 7 5) = [7, 7, 7, 7, 1] := by decide +kernel
example : encodeRle1 (rep 7 255) = [7, 7, 7, 7, 251] := by decide +kernel
example : encodeRle1 (rep 7 256) = [7, 7, 7, 7, 251, 7] := by decide +kernel
example : encodeRle1 (rep 7 259) = [7, 7, 7, 7, 251, 7, 7, 7, 7, 0] := by decide +kernel
-- ... and decoding them back.
example : decodeRle1 [7, 7, 7] = rep 7 3 := by decide +kernel
example : decodeRle1 [7, 7, 7, 7, 0] = rep 7 4 := by decide +kernel
example : decodeRle1 [7, 7, 7, 7, 1] = rep 7 5 := by decide +kernel
example : decodeRle1 [7, 7, 7, 7, 251] = rep 7 255 := by decide +kernel
example : decodeRle1 [7, 7, 7, 7, 251, 7] = rep 7 256 := by decide +kernel
example : decodeRle1 (encodeRle1 (rep 7 256)) = rep 7 256 := by decide +kernel
-- A count byte above 251 is accepted: 4 + 255 = 259 bytes.
example : decodeRle1 [7, 7, 7, 7, 255] = rep 7 259 := by decide +kernel
example : decodeRle1 [7, 7, 7, 7, 252] = rep 7 256 := by decide +kernel
-- The byte after a count starts a fresh run (edge case 4).
example : decodeRle1 [7, 7, 7, 7, 0, 7, 7, 7, 7, 0] = rep 7 8 := by decide +kernel
example : decodeRle1 [7, 7, 7, 7, 0, 7] = rep 7 5 := by decide +kernel
-- A block ending right after 4 equal bytes is truncated (edge case 5); one ending after 3 is not.
example : decodeRle1 [7, 7, 7, 7] = rep 7 4 := by decide +kernel
example : (decState [7, 7, 7, 7]).run = some (7, 4) := by decide +kernel
example : (decState [7, 7, 7]).run = some (7, 3) := by decide +kernel
example : (decState [7, 7, 7, 7, 0]).run = none := by decide +kernel
example : (decState [1, 7, 7, 7, 7, 3]).run = none := by decide +kernel

end Bzip2.Spec.Rle1
