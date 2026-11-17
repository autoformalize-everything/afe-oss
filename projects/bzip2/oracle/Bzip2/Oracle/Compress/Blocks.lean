import Bzip2.Oracle.Crc

/-!
# Oracle: input to blocks (RLE1, block CRCs)

Splits the input into the blocks the C compressor builds, as `bzlib.c` does while it reads input:
`ADD_CHAR_TO_BLOCK` (`bzlib.c:260-284`), `add_pair_to_block` (`bzlib.c:216-247`), `flush_RL`
(`bzlib.c:252-256`), `copy_input_until_stop` (`bzlib.c:289-329`) and the state machine around it
in `handle_compress` (`bzlib.c:361-404`). A `Block` holds what the block-level code in
`compress.c` starts from: the post-RLE1 bytes (`s->block[0 .. nblock-1]`), the finalised block CRC
(`s->blockCRC`, `compress.c:606`) and the symbol map (`s->inUse`).

RLE1 (`add_pair_to_block`): a run of `len` equal bytes, `len ≤ 255` (a run is cut when it reaches
255, `bzlib.c:276`), is written as the byte `len` times if `len ≤ 3`, else four copies and the
byte `len - 4` (`bzlib.c:224-246`). The count byte is marked in `inUse` as well
(`bzlib.c:238`).

Facts this module settles, each read off the C code:

* **The block limit.** `nblockMAX = 100000 * level - 19` (`bzlib.c:194`). The block is closed when
  `nblock ≥ nblockMAX` is seen *before the next input byte is read* (`bzlib.c:298`, `bzlib.c:314`
  and `bzlib.c:390-393`), so a block may exceed `nblockMAX`: the run written last is up to 5
  bytes. The block is never closed in the middle of a run's bytes and never at a point where
  `nblock < nblockMAX`.
* **The pending run belongs to the next block.** A run is written to the block (and its bytes
  are folded into `blockCRC`, `bzlib.c:220-222` and `bzlib.c:267`) only when the next byte ends it.
  When a block is closed at `nblock ≥ nblockMAX`, the run still pending (`state_in_ch`,
  `state_in_len`) is not flushed (`bzlib.c:390-393` do not call `flush_RL`); it is written to the
  next block, and its bytes are in the next block's CRC. So the block CRC is over the original
  bytes of the runs written to that block, and a run is never split between blocks.
* **The fast path.** `bzlib.c:264-272` (a different byte after a run of length 1) does what
  `add_pair_to_block` does with length 1 (`bzlib.c:225-227`), so it is not modelled apart.
* **Empty input.** No byte is read, so `nblock = 0` at the end; `BZ2_compressBlock` writes no
  block when `nblock = 0` (`compress.c:604`, `compress.c:630`). There are no blocks.
  Otherwise the last block is never empty: its pending run is written by `flush_RL`
  (`bzlib.c:385`).
* **The last byte and a full block.** Whether a block that is full exactly when the last input
  byte has been read is closed without the pending run depends on how the library is driven.
  With `BZ_RUN` calls followed by an empty `BZ_FINISH` (`bzip2`'s `compressStream`,
  `bzip2.c:355-362`; `BZ2_bzWrite`, `bzlib.c:964-1005`), the check `nblock >= nblockMAX`
  (`bzlib.c:390`) runs after `copy_input_until_stop` and closes the block; the pending run is then
  alone in one more block. With the whole input in one `BZ_FINISH` call
  (`BZ2_bzBuffToBuffCompress`, `bzlib.c:1250-1351`, call at `bzlib.c:1282`) `avail_in_expect`
  is `0` as well (`bzlib.c:384`), so `flush_RL` first writes the pending run into the full block,
  which is the last. `split` takes the choice as `oneShot` (default: the program's,
  `bzip2 -<level>`).
  Everywhere else the two give the same blocks.
-/

namespace Bzip2.Oracle.Compress.Blocks

/-- One block as `compress.c` receives it. -/
structure Block where
  /-- `s->block[0 .. nblock-1]`: the block after RLE1. -/
  data : ByteArray
  /-- `s->blockCRC` after `BZ_FINALISE_CRC` (`compress.c:606`): the CRC of the original bytes
  (before RLE1) of the runs written to this block. -/
  crc : UInt32
  /-- `s->inUse`: 256 flags, the byte values that occur in `data`. -/
  inUse : Array Bool
  deriving BEq, Inhabited

/-- `s->nblockMAX` for a level in 1..9 (`bzlib.c:194`). -/
def nblockMax (level : Nat) : Nat := 100000 * level - 19

/-- The compressor's input state: the block being filled and the run still pending
(`state_in_ch`, `state_in_len`; `none` is `state_in_ch = 256`, `bzlib.c:131-135`). -/
structure State where
  /-- `s->block[0 .. nblock-1]`. -/
  block : ByteArray := ByteArray.empty
  /-- `s->blockCRC`, not yet finalised (`BZ_INITIALISE_CRC`, `bzlib_private.h:157-160`). -/
  crc : UInt32 := Crc.init
  /-- `s->inUse`. -/
  inUse : Array Bool := Array.replicate 256 false
  /-- `s->state_in_ch`, or `none` for 256. -/
  ch : Option UInt8 := none
  /-- `s->state_in_len`. -/
  len : Nat := 0

/-- `add_pair_to_block` (`bzlib.c:216-247`): writes the pending run to the block, if there is
one (the callers test `state_in_ch < 256`, `bzlib.c:277`, `bzlib.c:254`). -/
def addPairToBlock (s : State) : State :=
  match s.ch with
  | none => s
  | some ch => Id.run do
    let mut crc := s.crc
    for _ in [0:s.len] do
      crc := Crc.updateByte crc ch
    let mut inUse := s.inUse.set! ch.toNat true
    let mut block := s.block
    if s.len ≤ 3 then
      for _ in [0:s.len] do
        block := block.push ch
    else
      inUse := inUse.set! (s.len - 4) true
      for _ in [0:4] do
        block := block.push ch
      block := block.push (s.len - 4).toUInt8
    return { s with block, crc, inUse }

/-- `ADD_CHAR_TO_BLOCK` (`bzlib.c:260-284`): the byte `b` extends the pending run, or ends it
(a different byte, or a run of 255) and starts a new one. -/
def addCharToBlock (s : State) (b : UInt8) : State :=
  if s.ch == some b && s.len != 255 then
    { s with len := s.len + 1 }
  else
    { addPairToBlock s with ch := some b, len := 1 }

/-- The block `s` as a `Block`, with its CRC finalised (`BZ_FINALISE_CRC`,
`bzlib_private.h:162-165`). -/
def State.toBlock (s : State) : Block :=
  { data := s.block, crc := Crc.finalise s.crc, inUse := s.inUse }

/-- `prepare_new_block` (`bzlib.c:116-126`): an empty block; the pending run stays. -/
def State.next (s : State) : State :=
  { ch := s.ch, len := s.len }

/-- Splits `input` into blocks for `level` in 1..9 (the caller checks the level, as
`BZ2_bzCompressInit` does, `bzlib.c:159-161`).

The loop of `copy_input_until_stop`: close the block when `nblock ≥ nblockMAX`, before reading the
next byte (`bzlib.c:298`). At the end `flush_RL` writes the pending run (`bzlib.c:385`) and
the last block is closed if it is not empty (`compress.c:604`). With `oneShot = false`, a block
that is full after the last byte is closed first (`bzlib.c:390-393`); see the module doc. -/
def split (level : Nat) (input : ByteArray) (oneShot : Bool := false) : Array Block :=
  Id.run do
    let max := nblockMax level
    let mut blocks : Array Block := #[]
    let mut s : State := {}
    for b in input do
      if s.block.size ≥ max then
        blocks := blocks.push s.toBlock
        s := s.next
      s := addCharToBlock s b
    if !oneShot && s.block.size ≥ max then
      blocks := blocks.push s.toBlock
      s := s.next
    s := addPairToBlock s
    if s.block.size > 0 then
      blocks := blocks.push s.toBlock
    return blocks

end Bzip2.Oracle.Compress.Blocks
