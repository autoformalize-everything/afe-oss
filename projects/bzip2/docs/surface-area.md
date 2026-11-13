# bzip2: external surface area

Maintained by fleet task `bzip2/surface-area`. Machine-readable companion: `surface-area.json`.

- **Source:** `projects/bzip2/upstream/` = bzip2 commit `f5dfc96063fef2d9c5446d0733867d899ef9b942`
  (1.0.8 plus later upstream fixes). Unless stated otherwise, every `file:line` citation is
  relative to that directory.
- **Code wins.** Where `manual.xml`, `bzip2.1` or a header comment disagrees with the code, this
  document describes the code and lists the disagreement in [§9](#9-discrepancies-between-the-documentation-and-the-code).
- **Confidence.** Claims tagged **(verified)** were also checked by compiling the vendored sources
  outside the repository and running small test programs on x86-64 Linux with gcc. Claims tagged
  **(uncertain)** are inferences that were not confirmed. Everything else is read directly from
  the cited lines.
- "The library" means the seven objects built into `libbz2.a`: `blocksort.o huffman.o crctable.o
  randtable.o compress.o decompress.o bzlib.o` (`Makefile:30-36`).

## Contents

1. [Overview](#1-overview)
2. [The stream API as a state machine](#2-the-stream-api-as-a-state-machine)
3. [Types](#3-types)
4. [Macros](#4-macros)
5. [Public functions](#5-public-functions)
6. [Exported internals](#6-exported-internals)
7. [Programs](#7-programs)
8. [The .bz2 format](#8-the-bz2-format)
9. [Discrepancies between the documentation and the code](#9-discrepancies-between-the-documentation-and-the-code)
10. [Open questions](#10-open-questions)

---

## 1. Overview

`bzlib.h` is the only installed header (`Makefile:88`). It declares 24 functions with
`BZ_API`, one struct type (`bz_stream`), one opaque type (`BZFILE`) and the `BZ_*` macros. They
form five layers:

| Layer | Functions | Built under `BZ_NO_STDIO`? | Implemented in |
|---|---|---|---|
| Low-level stream API (compression) | `BZ2_bzCompressInit`, `BZ2_bzCompress`, `BZ2_bzCompressEnd` | yes | `bzlib.c:148-484` |
| Low-level stream API (decompression) | `BZ2_bzDecompressInit`, `BZ2_bzDecompress`, `BZ2_bzDecompressEnd` | yes | `bzlib.c:492-878` |
| High-level `BZFILE` API over `FILE*` | `BZ2_bzReadOpen`, `BZ2_bzRead`, `BZ2_bzReadGetUnused`, `BZ2_bzReadClose`, `BZ2_bzWriteOpen`, `BZ2_bzWrite`, `BZ2_bzWriteClose`, `BZ2_bzWriteClose64` | no (`bzlib.h:137-202`, `bzlib.c:881-1242`) | `bzlib.c:916-1241` |
| One-shot buffer-to-buffer utilities | `BZ2_bzBuffToBuffCompress`, `BZ2_bzBuffToBuffDecompress` | yes | `bzlib.c:1250-1351` |
| zlib-style compatibility functions | `BZ2_bzlibVersion` (always built), `BZ2_bzopen`, `BZ2_bzdopen`, `BZ2_bzread`, `BZ2_bzwrite`, `BZ2_bzflush`, `BZ2_bzclose`, `BZ2_bzerror` (stdio only) | `BZ2_bzlibVersion` only (`bzlib.c:1369`, guard at `bzlib.c:1375-1570`) | `bzlib.c:1369-1569` |

How they fit together:

- Every higher layer is written on top of the low-level stream API. The high-level API embeds a
  `bz_stream` in a private `bzFile` record (`bzlib.c:892-902`) and calls `BZ2_bzCompress` /
  `BZ2_bzDecompress` with a 5000-byte (`BZ_MAX_UNUSED`) staging buffer. The buffer utilities
  run one `Init`/`Compress(BZ_FINISH)` or `Init`/`Decompress` call on a stack `bz_stream`
  (`bzlib.c:1259-1297`, `1310-1350`). The zlib-style functions wrap the high-level API
  (`bzlib.c:1385-1535`).
- The stream API drives the internal engine: `BZ2_compressBlock` (`compress.c:602`) with
  `BZ2_blockSort` (`blocksort.c:1031`) and the Huffman helpers (`huffman.c`) for compression,
  `BZ2_decompress` (`decompress.c:106`) for decompression. Those internals are global symbols
  that `bzlib.h` does not declare; they are listed in [§6](#6-exported-internals).
- Programs: `bzip2` (installed also as `bunzip2` and `bzcat`) links `libbz2` and uses only the
  high-level API plus `BZ2_bzlibVersion` (`bzip2.c:346-603`, `1629`, `1672`). `bzip2recover`
  does **not** link the library; it has its own bit reader (`Makefile:43-44`,
  `bzip2recover.c:149-265`). `bzgrep`, `bzmore`, `bzdiff` (and the links `bzegrep`, `bzfgrep`,
  `bzless`, `bzcmp`) are `/bin/sh` scripts that pipe through `bzip2 -cd...`.

Global facts that apply to every library function:

- **No mutable global state.** The only global data are two lookup tables,
  `BZ2_crc32Table` and `BZ2_rNums`, which the library only reads (they are declared non-`const`,
  `crctable.c:31`, `randtable.c:26`). All per-stream state lives in memory reachable from a
  `bz_stream` (`strm->state`) or a `BZFILE`.
- **Thread safety.** Consequently distinct streams/handles can be used from different threads
  concurrently, provided the allocator (`bzalloc`/`bzfree`, default `malloc`/`free`) and, for
  the stdio layers, the `FILE*` and `stderr` are thread-safe. Nothing in the source locks; one
  stream or handle must not be used by two threads at once. `bzlib.h:227-234` (and
  `bzlib.c:1355-1362`) say the zlib-style functions were not reviewed for thread safety. This is
  an inference from the absence of shared mutable state, not a documented guarantee
  **(uncertain** as a guarantee; no counter-example found in the source).
- **Reentrancy.** No library function calls back into user code except through `bzalloc` /
  `bzfree`. Re-entering the library on the *same* stream from those callbacks is not supported
  (the stream would be mid-update).
- **Assertion failures.** Internal consistency checks use `AssertH(cond, code)`. In a normal
  build a failure calls `BZ2_bz__AssertH__fail(code)`, which prints to `stderr` and calls
  `exit(3)` (`bzlib_private.h:56-60`, `bzlib.c:40-86`). Under `BZ_NO_STDIO` it calls the
  user-supplied `bz_internal_error(code)` (`bzlib_private.h:86-90`). The error numbers are
  listed under [`BZ2_bz__AssertH__fail`](#bz2_bz__asserth__fail).
- **Verbosity output.** Only `verbosity >= 2` produces library output on `stderr`; level 1
  produces none from the library (it is used by the `bzip2` program). The thresholds are
  `>= 2` (`compress.c:611`, `compress.c:663`, `decompress.c:238`, `decompress.c:528`,
  `bzlib.c:829`, `blocksort.c:1076`), `>= 3` (`compress.c:261`, `302`, `436`, `513`, `525`, `541`,
  `596`, `bzlib.c:826`, `844`, `blocksort.c:1069`) and `>= 4` (`blocksort.c:229`, `263`, `308`,
  `320`, `767`, `800`, `893`, `1008`). Under `BZ_NO_STDIO` all `VPrintf*` macros are no-ops
  (`bzlib_private.h:92-97`).
- **Configuration check.** `BZ2_bzCompressInit` and `BZ2_bzDecompressInit` (and everything built
  on them) return `BZ_CONFIG_ERROR` unless `sizeof(int)==4`, `sizeof(short)==2` and
  `sizeof(char)==1` (`bzlib.c:90-97`, `157`, `499`).
- **Memory.** Low-level allocation is always `bzalloc(opaque, nbytes, 1)` (the `BZALLOC` macro,
  `bzlib_private.h:102`), freeing is `bzfree(opaque, ptr)` (`bzlib_private.h:103`). The
  defaults are `malloc(items*size)` and `free` skipping `NULL` (`bzlib.c:101-112`). The
  high-level API allocates its `bzFile` record with plain `malloc` and always uses the default
  allocators for its embedded stream (`bzlib.c:937`, `946-948`, `1113`, `1123-1125`).

---

## 2. The stream API as a state machine

### 2.1 Compression

The internal compression state `EState` has a `mode` (`BZ_M_IDLE=1`, `BZ_M_RUNNING=2`,
`BZ_M_FLUSHING=3`, `BZ_M_FINISHING=4`, `bzlib_private.h:178-181`) and a sub-state
(`BZ_S_INPUT`, `BZ_S_OUTPUT`, `bzlib_private.h:183-184`) saying whether the engine is collecting
input into the current block or draining a compressed block to `next_out`.

States visible to the caller:

| State | Meaning |
|---|---|
| UNINIT | `strm->state` is not a valid `EState` for this `strm` (never initialised, or after `BZ2_bzCompressEnd`, which sets `strm->state = NULL`). Detected only when `state` is `NULL` or points to memory whose first word is not `strm`; a garbage `state` pointer is dereferenced (undefined behaviour). |
| RUNNING | after a successful `BZ2_bzCompressInit` (`bzlib.c:191`), or after a completed flush. |
| FLUSHING | `BZ_FLUSH` accepted, not finished. Records `avail_in_expect = strm->avail_in` (`bzlib.c:429-430`). |
| FINISHING | `BZ_FINISH` accepted, not finished. Records `avail_in_expect = strm->avail_in` (`bzlib.c:435-436`). |
| IDLE | after `BZ_STREAM_END` (`bzlib.c:460`). Only `BZ2_bzCompressEnd` is useful. |

Transitions of `BZ2_bzCompress(strm, action)` (`bzlib.c:407-464`). "Progress" means at least one
byte was consumed from `next_in` or written to `next_out` during the call (`bzlib.c:363-402`).
"Done" means the remembered input is exhausted (`avail_in_expect == 0`), the run-length
accumulator is empty, and the last compressed block has been fully copied out
(`bzlib.c:447-448`, `458-459`).

| From | `action` | Result | To |
|---|---|---|---|
| any | `strm == NULL`, `strm->state == NULL`, or `state->strm != strm` | `BZ_PARAM_ERROR` (`bzlib.c:411-414`) | unchanged |
| IDLE | any | `BZ_SEQUENCE_ERROR` (`bzlib.c:419-420`) | IDLE |
| RUNNING | `BZ_RUN`, progress | `BZ_RUN_OK` (`bzlib.c:423-425`) | RUNNING |
| RUNNING | `BZ_RUN`, no progress (for example `avail_in == 0` with no compressed bytes pending, or `avail_out == 0` while a compressed block is pending) | `BZ_PARAM_ERROR` (`bzlib.c:425`) **(verified)** | RUNNING |
| RUNNING | `BZ_FLUSH` | enter FLUSHING, then immediately handled as FLUSHING/`BZ_FLUSH` in the same call (`goto preswitch`, `bzlib.c:428-432`); so it may return `BZ_RUN_OK` directly **(verified)** | FLUSHING or RUNNING |
| RUNNING | `BZ_FINISH` | enter FINISHING, then handled as FINISHING/`BZ_FINISH` in the same call (`bzlib.c:434-438`); so it may return `BZ_STREAM_END` directly **(verified)** | FINISHING or IDLE |
| RUNNING | any other value | `BZ_PARAM_ERROR` (`bzlib.c:439-440`) **(verified)** | RUNNING |
| FLUSHING | not `BZ_FLUSH` | `BZ_SEQUENCE_ERROR` (`bzlib.c:443`) | FLUSHING |
| FLUSHING | `BZ_FLUSH` but `strm->avail_in != avail_in_expect` | `BZ_SEQUENCE_ERROR` (`bzlib.c:444-445`) | FLUSHING |
| FLUSHING | `BZ_FLUSH`, not done | `BZ_FLUSH_OK` (`bzlib.c:446-448`) | FLUSHING |
| FLUSHING | `BZ_FLUSH`, done | `BZ_RUN_OK` (`bzlib.c:449-450`) | RUNNING |
| FINISHING | not `BZ_FINISH` | `BZ_SEQUENCE_ERROR` (`bzlib.c:453`) | FINISHING |
| FINISHING | `BZ_FINISH` but `strm->avail_in != avail_in_expect` | `BZ_SEQUENCE_ERROR` (`bzlib.c:454-455`) | FINISHING |
| FINISHING | `BZ_FINISH`, no progress (for example `avail_out == 0` while compressed output is pending) | `BZ_SEQUENCE_ERROR` (`bzlib.c:456-457`) **(verified)** | FINISHING |
| FINISHING | `BZ_FINISH`, progress, not done | `BZ_FINISH_OK` (`bzlib.c:458-459`) | FINISHING |
| FINISHING | `BZ_FINISH`, progress, done | `BZ_STREAM_END` (`bzlib.c:460-461`) | IDLE |

Other transitions: `BZ2_bzCompressInit` takes UNINIT to RUNNING; `BZ2_bzCompressEnd` takes any
initialised state to UNINIT (`bzlib.c:476-481`). Note that FLUSHING/FINISHING count input
through `avail_in_expect` while consuming (`bzlib.c:318`, `325`); the caller must not change
`avail_in` at all while FLUSHING or FINISHING, though it may move `next_in` (only `avail_in` is
compared).

`BZ_SEQUENCE_ERROR` therefore means one of: the stream already ended (IDLE); a different action
was passed while a flush/finish is in progress; `avail_in` changed during a flush/finish; or a
`BZ_FINISH` call could make no progress.

**Flush semantics.** `BZ_FLUSH` ends the current block, but the bit writer drains whole bytes
from its 32-bit buffer only *before* adding new bits (`compress.c:58-78`), and only the last
block is drained and padded to a byte boundary (`bsFinishWrite`, `compress.c:46-54`,
`657-666`). So after a completed flush up to 31 bits of the block (possibly including whole
bytes) remain in the compressor's bit buffer and are emitted only with the next block or the
finish. Therefore the bytes emitted up to a completed flush are not by themselves enough to
decode the flushed data: a decoder given exactly those bytes produced 0 output bytes in testing
**(verified)**. A flush with no pending input emits no block (`compress.c:604`, `630`), except
that if it is the stream's first block the stream header is still written
(`compress.c:622-628`) **(verified** by review: 3 bytes `BZh` emitted, the 4th held in the
buffer**)**.

### 2.2 Decompression

Internal `DState.state` is `BZ_X_IDLE=1`, `BZ_X_OUTPUT=2`, or one of the parser states
`BZ_X_MAGIC_1` (10) … `BZ_X_CCRC_4` (50) (`bzlib_private.h:291-334`). Visible states:

| State | Meaning |
|---|---|
| UNINIT | `strm->state` not valid for `strm` (never initialised or after `BZ2_bzDecompressEnd`, which sets it to `NULL`). Same detection limits as for compression. |
| PARSING | `state >= BZ_X_MAGIC_1`: reading headers, tables or Huffman data. Initial state after `BZ2_bzDecompressInit` is `BZ_X_MAGIC_1` (`bzlib.c:512`). |
| OUTPUT | `BZ_X_OUTPUT`: a block has been decoded and its bytes are being written to `next_out` (`decompress.c:527`). |
| IDLE | `BZ_X_IDLE`: end-of-stream marker and combined CRC read (`decompress.c:611`). |

`BZ2_bzDecompress(strm)` (`bzlib.c:808-858`) loops: in OUTPUT it writes run-length-decoded bytes
until `avail_out == 0` or the block is exhausted; when a block is exhausted it checks the block
CRC and moves to PARSING (`bzlib.c:824-836`); in PARSING it calls `BZ2_decompress`, which reads
input until it needs more bytes, finishes a block, or reaches the end of stream.

| From | Condition | Result | To |
|---|---|---|---|
| any | `strm == NULL`, `strm->state == NULL`, or `state->strm != strm` | `BZ_PARAM_ERROR` (`bzlib.c:812-815`) | unchanged |
| IDLE | — | `BZ_SEQUENCE_ERROR` (`bzlib.c:818`) **(verified)** | IDLE |
| PARSING | input exhausted before the next structure is complete | `BZ_OK` (`decompress.c:54`, `bzlib.c:851`) | PARSING |
| PARSING | first four bytes are not `B`,`Z`,`h`,`'1'..'9'` | `BZ_DATA_ERROR_MAGIC` (`decompress.c:197-208`) **(verified)** | PARSING (state left at the failing byte) |
| PARSING | `bzalloc` fails for the block arrays | `BZ_MEM_ERROR` (`decompress.c:211-220`) | PARSING |
| PARSING | any structural check fails (see [§8](#8-the-bz2-format)) | `BZ_DATA_ERROR` | PARSING |
| PARSING | block fully decoded | continue in OUTPUT within the same call (`decompress.c:527`, `584`; `bzlib.c:851`) | OUTPUT |
| PARSING | end-of-stream marker read, combined CRC matches | `BZ_STREAM_END` (`bzlib.c:843-849`) | IDLE |
| PARSING | end-of-stream marker read, combined CRC differs | `BZ_DATA_ERROR` (`bzlib.c:847-848`) | IDLE |
| OUTPUT | `avail_out` reaches 0 with block bytes pending | `BZ_OK` (`bzlib.c:837-838`) | OUTPUT |
| OUTPUT | block exhausted, block CRC differs | `BZ_DATA_ERROR` (`bzlib.c:830-831`) **(verified)** | OUTPUT |
| OUTPUT | inverse-BWT walk out of range / overruns (corrupt data) | `BZ_DATA_ERROR` (`bzlib.c:560-561`, `633-634`, `730-731`, `779-780`, `bzlib_private.h:446`, `453`, `477`) | OUTPUT |
| OUTPUT | block exhausted, CRC ok | combined CRC updated, continue PARSING in the same call (`bzlib.c:832-836`) | PARSING |

`BZ2_bzDecompressInit` takes UNINIT to PARSING; `BZ2_bzDecompressEnd` takes any initialised
state to UNINIT (`bzlib.c:870-875`).

Notes:

- `BZ2_bzDecompress` does not require `avail_out > 0`: with `avail_out == 0` it still parses
  input up to the end of the first block and returns `BZ_OK` **(verified)**.
- `BZ_SEQUENCE_ERROR` from `BZ2_bzDecompress` means exactly "called again after the stream
  ended" (state IDLE). One `Init` decodes exactly one stream; concatenated streams need a new
  `Init` (see `BZ2_bzReadGetUnused` and `bzip2.c:454-482`).
- After any error return the internal state is left where the error was detected; there is no
  terminal error state. The only documented next call is `BZ2_bzDecompressEnd`
  (`manual.xml:1567-1569`). What a further `BZ2_bzDecompress` call does is not specified
  (**uncertain**; see [§10](#10-open-questions)).
- The decoder reads input one byte at a time and only when it needs more bits (`GET_BITS`,
  `decompress.c:43-65`), so on `BZ_STREAM_END` `next_in` points just past the byte that holds the
  last bit of the combined CRC; trailing bytes are not consumed **(verified)**.

---

## 3. Types

### `bz_stream`

Declared at `bzlib.h:57-75`. The caller allocates it; the library never allocates or frees the
struct itself. The library keeps a back-pointer to it (`EState.strm`/`DState.strm`,
`bzlib_private.h:199`, `350`) and rejects a stream whose `state->strm != strm`
(`bzlib.c:414`, `474`, `815`, `868`), so **a `bz_stream` must not be moved or copied between
`Init` and `End`.**

| Field | Type | Set by | Read by | Meaning and state between calls |
|---|---|---|---|---|
| `next_in` | `char *` | caller before each `Compress`/`Decompress`; library advances it by the number of bytes consumed (`bzlib.c:303`, `321`; `decompress.c:60`) | `BZ2_bzCompress`, `BZ2_bzDecompress` | Next input byte. The library does not keep a pointer into the input buffer between calls; input is copied into internal state (compression block or bit buffer). |
| `avail_in` | `unsigned int` | caller; library decrements per byte consumed (`bzlib.c:304`, `322`; `decompress.c:61`) | `Compress`, `Decompress` | Bytes available at `next_in`. During FLUSHING/FINISHING it must keep exactly the value the library leaves it at (`bzlib.c:444`, `454`). |
| `total_in_lo32`, `total_in_hi32` | `unsigned int` | zeroed by `Init` (`bzlib.c:204-205`, `516-517`); library increments a 64-bit count split in two halves (`bzlib.c:305-306`, `323-324`; `decompress.c:62-64`) | caller; `BZ2_bzWriteClose64` (`bzlib.c:1074-1077`) | Total bytes consumed since `Init`. Never read by the engine itself; the caller should not change them. |
| `next_out` | `char *` | caller; library advances it per byte produced (`bzlib.c:350`, `550`, `618`/`677`, `720`, `769`) | `Compress`, `Decompress` | Where the next output byte goes. |
| `avail_out` | `unsigned int` | caller; library decrements per byte produced | `Compress`, `Decompress` | Free space at `next_out`. |
| `total_out_lo32`, `total_out_hi32` | `unsigned int` | zeroed by `Init` (`bzlib.c:206-207`, `518-519`); incremented by the library (`bzlib.c:351-352`, `552-553`, `664-667`, `722-723`, `771-772`) | caller; `BZ2_bzWriteClose64` (`bzlib.c:1078-1081`) | Total bytes produced since `Init`, as a 64-bit count. |
| `state` | `void *` | `BZ2_bzCompressInit` / `BZ2_bzDecompressInit` set it to a freshly allocated `EState` / `DState` (`bzlib.c:203`, `511`); `End` sets it to `NULL` (`bzlib.c:481`, `875`). On `Init` failure it is left unchanged. | all stream functions | Private engine state. Opaque to the caller. Passing a compression stream to a decompression function or vice versa is not detected (both private structs start with the `strm` back-pointer) and is undefined. |
| `bzalloc` | `void *(*)(void *, int, int)` | caller before `Init`; if `NULL`, `Init` stores `default_bzalloc` in the field (`bzlib.c:165`, `505`) | `Init` (`bzlib.c:168-179`, `508`), `BZ2_bzDecompress` on reading the stream header (`decompress.c:212-218`) | Allocator. Always called as `bzalloc(opaque, nbytes, 1)` (`bzlib_private.h:102`). Must return `NULL` on failure. Must stay valid until `End`. |
| `bzfree` | `void (*)(void *, void *)` | caller before `Init`; if `NULL`, `Init` stores `default_bzfree` (`bzlib.c:166`, `506`) | `Init` on its failure path (`bzlib.c:182-185`), `End` (`bzlib.c:476-479`, `870-874`) | Deallocator, called as `bzfree(opaque, ptr)` (`bzlib_private.h:103`). |
| `opaque` | `void *` | caller before `Init` | passed through as the first argument of `bzalloc`/`bzfree` | Never interpreted by the library. |

Memory obtained through `bzalloc` (all freed by the matching `End`):

- Compression (`bzlib.c:168-179`): `sizeof(EState)`, then `n*4`, `(n+34)*4` and `65537*4` bytes
  where `n = 100000*blockSize100k` (`BZ_N_OVERSHOOT = 34`, `bzlib_private.h:186-189`).
- Decompression: `sizeof(DState)` in `Init` (`bzlib.c:508`); when the stream header is read,
  either `n*4` bytes (`tt`) or, with `small`, `n*2` (`ll16`) plus `(n+1)/2` (`ll4`) bytes, where
  `n = 100000*blockSize100k` from the header (`decompress.c:211-220`).

### `BZFILE`

`typedef void BZFILE;` (`bzlib.h:140`), declared only without `BZ_NO_STDIO`. A `BZFILE*` is an
opaque handle; it actually points to the private `bzFile` (`bzlib.c:892-902`):

| Private field | Meaning |
|---|---|
| `FILE* handle` | the caller's file; never closed by `BZ2_bzRead*`/`BZ2_bzWrite*` (only `BZ2_bzclose` and the failure path of `BZ2_bzopen`/`BZ2_bzdopen` close it). |
| `Char buf[BZ_MAX_UNUSED]`, `Int32 bufN` | 5000-byte staging buffer for compressed data. |
| `Bool writing` | `True` for handles from `BZ2_bzWriteOpen`, `False` from `BZ2_bzReadOpen`; checked to produce `BZ_SEQUENCE_ERROR`. |
| `bz_stream strm` | embedded stream, default allocators. |
| `Int32 lastErr` | last code stored by `BZ_SETERR` (`bzlib.c:886-890`); read by `BZ2_bzReadGetUnused`, `BZ2_bzWriteClose64`, `BZ2_bzread`, `BZ2_bzerror`. |
| `Bool initialisedOk` | whether the embedded stream was initialised. |

Lifetime: created by `BZ2_bzReadOpen` / `BZ2_bzWriteOpen` (or `BZ2_bzopen`/`BZ2_bzdopen`), freed
by `BZ2_bzReadClose` / a successful or abandoning `BZ2_bzWriteClose[64]` (or `BZ2_bzclose`). Using
a handle after it was freed is undefined. A handle must be used with the matching read or write
functions; the read/write mismatch is detected and reported as `BZ_SEQUENCE_ERROR`.

---

## 4. Macros

All `BZ_*` macros that `bzlib.h` defines or tests.

### 4.1 Action codes (`bzlib.h:38-40`)

| Macro | Value | Meaning |
|---|---|---|
| `BZ_RUN` | 0 | `BZ2_bzCompress`: compress as much as possible, accept more input later. |
| `BZ_FLUSH` | 1 | `BZ2_bzCompress`: end the current block after the input currently in `avail_in`. |
| `BZ_FINISH` | 2 | `BZ2_bzCompress`: compress the remaining `avail_in` bytes and terminate the stream. |

### 4.2 Return codes (`bzlib.h:42-55`)

Non-negative codes are success/progress codes, negative codes are errors. `BZ2_bzerror` maps
`lastErr` to strings with `bzerrorstrings[-code]` after clamping positive codes to 0
(`bzlib.c:1542-1569`).

| Macro | Value | Produced by (when) |
|---|---|---|
| `BZ_OK` | 0 | Init/End success; `BZ2_bzDecompress` needs more input or output space; high-level and buffer functions on success. |
| `BZ_RUN_OK` | 1 | `BZ2_bzCompress` in RUNNING with progress, or a flush that completed. |
| `BZ_FLUSH_OK` | 2 | `BZ2_bzCompress`: flush still in progress. |
| `BZ_FINISH_OK` | 3 | `BZ2_bzCompress`: finish still in progress. |
| `BZ_STREAM_END` | 4 | `BZ2_bzCompress` finish complete; `BZ2_bzDecompress` end of stream reached with good combined CRC; stored in `*bzerror` by `BZ2_bzRead` at end of stream. |
| `BZ_SEQUENCE_ERROR` | -1 | call illegal in the current state ([§2](#2-the-stream-api-as-a-state-machine)); high-level read/write handle mismatch; `BZ2_bzReadGetUnused` before end of stream. |
| `BZ_PARAM_ERROR` | -2 | argument out of range or `NULL`; also `BZ2_bzCompress(BZ_RUN)` making no progress and unknown actions in RUNNING (`bzlib.c:425`, `440`). |
| `BZ_MEM_ERROR` | -3 | allocation failed (`bzalloc`, or `malloc` for `bzFile`). |
| `BZ_DATA_ERROR` | -4 | corrupt compressed data or CRC mismatch. |
| `BZ_DATA_ERROR_MAGIC` | -5 | first four stream bytes are not `BZh1`..`BZh9`. |
| `BZ_IO_ERROR` | -6 | `ferror()` set on the `FILE*`, short `fwrite`, or `fflush` failure (high-level API only). |
| `BZ_UNEXPECTED_EOF` | -7 | input ended before the end-of-stream marker (`BZ2_bzRead`, `BZ2_bzBuffToBuffDecompress`). |
| `BZ_OUTBUFF_FULL` | -8 | buffer utilities: output did not fit in `*destLen`. |
| `BZ_CONFIG_ERROR` | -9 | the platform's `int`/`short`/`char` sizes are not 4/2/1 (`bzlib.c:90-97`). |

### 4.3 Limit

| Macro | Value | Meaning |
|---|---|---|
| `BZ_MAX_UNUSED` | 5000 | Size of the high-level API's staging buffer (`bzlib.c:895`); upper bound for `nUnused` in `BZ2_bzReadOpen` (`bzlib.c:1107`) and therefore for what `BZ2_bzReadGetUnused` returns; chunk size for `fread`/`fwrite` in `BZ2_bzRead`/`BZ2_bzWrite` (`bzlib.c:988`, `1194`). Defined only without `BZ_NO_STDIO` (`bzlib.h:137-138`). |

### 4.4 Configuration macros

| Macro | Kind | Effect |
|---|---|---|
| `BZ_NO_STDIO` | defined by the user when compiling the library *and* client code | `bzlib.h` does not include `<stdio.h>` (`bzlib.h:25-28`) and does not declare `BZ_MAX_UNUSED`, `BZFILE` or the high-level and zlib-style functions (`bzlib.h:137-202`, `240-275`); `bzlib.c` does not define them (`bzlib.c:881-1242`, `1375-1570`) nor `BZ2_bz__AssertH__fail` (`bzlib.c:40-86`). `AssertH` then calls an external `void bz_internal_error(int errcode)` that the user must supply (link error otherwise), and all verbosity output is compiled out (`bzlib_private.h:86-99`). Remaining library functions: the six stream functions, the two buffer utilities, `BZ2_bzlibVersion`, plus the internals of [§6](#6-exported-internals) **(verified** with `nm`). |
| `BZ_IMPORT` | defined by client code that loads a Windows DLL dynamically (as `dlltest.c:10` does) | If not defined, `bzlib.h` defines `BZ_EXPORT` (`bzlib.h:78-80`). Only matters under `_WIN32`. |
| `BZ_EXPORT` | defined by `bzlib.h` itself unless `BZ_IMPORT` is defined (it may also be defined by the user) | Under `_WIN32`: if defined, `BZ_API(f)` is `WINAPI f` and `BZ_EXTERN` is `extern` (ordinary `__stdcall` declarations); if not defined, `BZ_API(f)` is `(WINAPI * f)` and `BZ_EXTERN` is empty, so every "declaration" in `bzlib.h` becomes a definition of a function-pointer variable to be filled with `GetProcAddress` (`bzlib.h:82-94`, `dlltest.c:36-56`). Not used on other platforms. |
| `BZ_API(func)` | function-like macro wrapping each public function name | Non-Windows: expands to `func` (`bzlib.h:96`). Windows: `WINAPI func` or `(WINAPI * func)` as above. Used in both the declarations and the definitions in `bzlib.c`, so the library itself must be compiled without `BZ_IMPORT`. |
| `BZ_EXTERN` | storage-class prefix of each declaration | `extern` except on Windows with `BZ_IMPORT` (empty) (`bzlib.h:89`, `93`, `97`). |

Other configuration knobs that are not in `bzlib.h` (so not part of the client-facing macro set):
`BZ_DEBUG` enables `AssertD` checks that print and `exit(1)` (`bzlib_private.h:62-71`);
`BZ_STRICT_ANSI` makes `BZ2_bzdopen` always fail (`bzlib.c:1431-1435`); `_WIN32` additionally
`#undef`s `small` (`bzlib.h:82-86`) and includes `<windows.h>` (`bzlib.h:30-32`). The version
string macro `BZ_VERSION` is private (`bzlib_private.h:39`).

---

## 5. Public functions

Conventions: "stdio" = absent under `BZ_NO_STDIO`. "Never" for thread safety refers to the same
stream/handle; see [§1](#1-overview) for distinct streams. None of the public functions touches
global mutable state. All signatures are copied from `bzlib.h` with `BZ_EXTERN`/`BZ_API`
expanded as on non-Windows platforms.

### 5.1 Low-level compression

#### `BZ2_bzCompressInit`

```c
int BZ2_bzCompressInit ( bz_stream* strm, int blockSize100k, int verbosity, int workFactor );
```
Declared `bzlib.h:103-108`, defined `bzlib.c:148-211`. Built under `BZ_NO_STDIO`: yes.

Prepares `*strm` for compression.

| Parameter | Meaning | Valid |
|---|---|---|
| `strm` | caller-owned stream. `bzalloc`/`bzfree`/`opaque` must be set (or `NULL`) beforehand; other fields need not be initialised. Must stay at the same address until `BZ2_bzCompressEnd`. | non-`NULL` |
| `blockSize100k` | block size in units of 100000 bytes; also written into the stream header (`compress.c:627`). | 1..9 |
| `verbosity` | diagnostic level for `stderr`. **Not range-checked** (`bzlib.c:159-162`): any `int` is accepted and compared with `>=` thresholds **(verified** with 99**)**. | meaningful 0..4 |
| `workFactor` | effort before switching from the main to the fallback sorting algorithm. 0 means 30 (`bzlib.c:164`). Inside `BZ2_blockSort` values above 100 behave as 100 (`blocksort.c:1063-1064`); the compressed output is the same whichever sorting algorithm runs (`blocksort.c:1056-1062`, `manual.xml:1161-1163`). | 0..250 |

Returns:

| Code | When |
|---|---|
| `BZ_CONFIG_ERROR` | `bz_config_ok()` fails (`bzlib.c:157`). Checked first. |
| `BZ_PARAM_ERROR` | `strm == NULL`, `blockSize100k` outside 1..9, or `workFactor` outside 0..250 (`bzlib.c:159-162`). |
| `BZ_MEM_ERROR` | `bzalloc` returned `NULL` for the `EState` (`bzlib.c:169`) or for any of the three work arrays (`bzlib.c:181-187`; arrays already obtained and the `EState` are freed). |
| `BZ_OK` | success. |

Postconditions on `BZ_OK`: `strm->state` points to a new `EState` in RUNNING/input state;
`total_in_*`/`total_out_*` are 0 (`bzlib.c:203-207`); block number, CRCs and RLE state are
initialised (`bzlib.c:189-209`). `next_in`, `avail_in`, `next_out`, `avail_out` are not touched.
On any return after the parameter check, `strm->bzalloc`/`strm->bzfree` have been replaced by
the defaults if they were `NULL` (`bzlib.c:165-166`). On failure `strm->state` is unchanged.

Side effects: four `bzalloc` calls (sizes in [§3](#bz_stream)); no I/O; no output even with high
`verbosity`; no assertion paths. Thread safety: safe on distinct streams.

#### `BZ2_bzCompress`

```c
int BZ2_bzCompress ( bz_stream* strm, int action );
```
Declared `bzlib.h:110-113`, defined `bzlib.c:407-464`. Built under `BZ_NO_STDIO`: yes.

Consumes bytes from `next_in[0..avail_in-1]` and produces compressed bytes into
`next_out[0..avail_out-1]`, and requests mode changes. The full transition table is in
[§2.1](#21-compression).

| Parameter | Meaning | Valid |
|---|---|---|
| `strm` | stream initialised by `BZ2_bzCompressInit`, not ended. `next_in`/`avail_in`/`next_out`/`avail_out` describe caller buffers valid for the duration of the call. | non-`NULL`, `state` valid |
| `action` | `BZ_RUN`, `BZ_FLUSH` or `BZ_FINISH`. | see table |

Returns: `BZ_RUN_OK`, `BZ_FLUSH_OK`, `BZ_FINISH_OK`, `BZ_STREAM_END`, `BZ_SEQUENCE_ERROR`,
`BZ_PARAM_ERROR` exactly as in [§2.1](#21-compression). The final `return BZ_OK` at
`bzlib.c:463` is unreachable. `BZ_MEM_ERROR`/`BZ_DATA_ERROR` cannot occur: all memory is
allocated in `Init`.

Postconditions: `next_in`/`avail_in`/`total_in_*` advanced by the bytes consumed, `next_out`/
`avail_out`/`total_out_*` by the bytes produced. Consumed input may be held inside the current
block; output lags input by up to a block.

Side effects: no allocation, no I/O. With `verbosity >= 2` prints per-block progress to
`stderr` from `BZ2_compressBlock` and `BZ2_blockSort` ([§1](#1-overview)). May end in
`BZ2_bz__AssertH__fail` through internal assertions 1001-1007 (`blocksort.c`), 2001-2002
(`huffman.c:98`, `112`) and 3001-3007 (`compress.c:272`, `455-458`, `488-489`, `552`, `594`). They
check internal invariants; whether any is reachable is not established ([§10](#10-open-questions)). Thread safety: not on the same
stream.

#### `BZ2_bzCompressEnd`

```c
int BZ2_bzCompressEnd ( bz_stream* strm );
```
Declared `bzlib.h:115-117`, defined `bzlib.c:468-484`. Built under `BZ_NO_STDIO`: yes.

Releases all memory of a compression stream, in any state (RUNNING, FLUSHING, FINISHING or
IDLE).

| Parameter | Meaning | Valid |
|---|---|---|
| `strm` | stream initialised by `BZ2_bzCompressInit`. | non-`NULL`, `state` valid |

Returns `BZ_PARAM_ERROR` if `strm == NULL`, `strm->state == NULL` or `state->strm != strm`
(`bzlib.c:471-474`); otherwise `BZ_OK`. A second `End` on the same stream therefore returns
`BZ_PARAM_ERROR` **(verified)**.

Postconditions: the three work arrays and the `EState` are passed to `bzfree`
(`bzlib.c:476-479`); `strm->state = NULL` (`bzlib.c:481`). Totals and buffer fields are left
as they were. Pending compressed output is discarded.

### 5.2 Low-level decompression

#### `BZ2_bzDecompressInit`

```c
int BZ2_bzDecompressInit ( bz_stream *strm, int verbosity, int small );
```
Declared `bzlib.h:119-123`, defined `bzlib.c:492-528`. Built under `BZ_NO_STDIO`: yes.

| Parameter | Meaning | Valid |
|---|---|---|
| `strm` | caller-owned stream; allocator fields set or `NULL`. Must not move until `End`. | non-`NULL` |
| `verbosity` | diagnostic level. | 0..4 (checked) |
| `small` | 1 selects the low-memory decoder (2.5 bytes per block byte, `decompress.c:212-216`, slower); 0 the fast decoder (4 bytes per block byte). | exactly 0 or 1 |

Returns:

| Code | When |
|---|---|
| `BZ_CONFIG_ERROR` | `bz_config_ok()` fails (`bzlib.c:499`). |
| `BZ_PARAM_ERROR` | `strm == NULL`, `small` not 0/1, or `verbosity` outside 0..4 (`bzlib.c:501-503`) **(verified)**. |
| `BZ_MEM_ERROR` | `bzalloc` for the `DState` failed (`bzlib.c:509`). |
| `BZ_OK` | success. |

Postconditions on `BZ_OK`: `strm->state` points to a new `DState` in `BZ_X_MAGIC_1`;
totals zeroed (`bzlib.c:510-525`). The block arrays are not allocated yet; their size is known
only after the header is read, so a later `BZ2_bzDecompress` may return `BZ_MEM_ERROR`.
`bzalloc`/`bzfree` defaults are stored when `NULL` (`bzlib.c:505-506`).

Side effects: one `bzalloc`. No I/O. Thread safety: safe on distinct streams.

#### `BZ2_bzDecompress`

```c
int BZ2_bzDecompress ( bz_stream* strm );
```
Declared `bzlib.h:125-127`, defined `bzlib.c:808-858`. Built under `BZ_NO_STDIO`: yes.

Consumes compressed bytes from `next_in` and writes decompressed bytes to `next_out`, for one
stream. Transition table in [§2.2](#22-decompression).

| Parameter | Meaning | Valid |
|---|---|---|
| `strm` | stream initialised by `BZ2_bzDecompressInit`, not ended. | non-`NULL`, `state` valid |

Returns:

| Code | When |
|---|---|
| `BZ_PARAM_ERROR` | `strm == NULL`, `state == NULL`, `state->strm != strm` (`bzlib.c:812-815`). There is no check of `avail_out`. |
| `BZ_SEQUENCE_ERROR` | stream already ended (`bzlib.c:818`). |
| `BZ_DATA_ERROR_MAGIC` | bad stream header (`decompress.c:198-208`). |
| `BZ_MEM_ERROR` | block arrays could not be allocated after reading the header (`decompress.c:216`, `219`). |
| `BZ_DATA_ERROR` | any format violation listed in [§8.6](#86-validation-performed-by-the-decoder), block CRC mismatch (`bzlib.c:830-831`), combined CRC mismatch (`bzlib.c:847-848`), or a corrupt inverse-BWT walk (`bzlib.c:823`). |
| `BZ_STREAM_END` | end-of-stream marker read and combined CRC matches; all output for the stream has been delivered (`bzlib.c:843-849`). |
| `BZ_OK` | needs more input or more output space. |

Postconditions: input/output pointers, counts and totals advanced. On `BZ_STREAM_END`,
`next_in`/`avail_in` describe the bytes after the stream (not consumed). Output is written only
after a whole block has been decoded and is CRC-checked only after the whole block has been
written, so bytes of a corrupt block may already be in `next_out` when `BZ_DATA_ERROR` is
returned (`bzlib.c:819-831`).

Side effects: may `bzalloc` block arrays once per stream on reading the header
(`decompress.c:211-220`); with `verbosity >= 2` prints per-block progress, with `>= 3` CRC
values (`bzlib.c:826-829`, `844-846`, `decompress.c:238-239`, `528`). Assertion paths:
`AssertH(False, 4001)` if the saved state is not a valid parser state (`decompress.c:614`) and
unreachable checks 4002 (`decompress.c:617`) and 6001 (`bzlib.c:855`). Thread safety: not on the
same stream.

#### `BZ2_bzDecompressEnd`

```c
int BZ2_bzDecompressEnd ( bz_stream *strm );
```
Declared `bzlib.h:129-131`, defined `bzlib.c:862-878`. Built under `BZ_NO_STDIO`: yes.

Releases all memory of a decompression stream in any state, including after errors.
Returns `BZ_PARAM_ERROR` if `strm == NULL`, `state == NULL` or `state->strm != strm`
(`bzlib.c:865-868`), else `BZ_OK`. Postconditions: `tt`, `ll16`, `ll4` (whichever are non-`NULL`)
and the `DState` are passed to `bzfree`; `strm->state = NULL` (`bzlib.c:870-875`).

### 5.3 High-level `BZFILE` API (stdio)

Common rules, all from `bzlib.c:886-1241`:

- `bzerror` may be `NULL`; if not, every function stores its outcome there. The outcome is also
  stored in the handle's `lastErr` whenever the handle pointer is known (`BZ_SETERR`,
  `bzlib.c:886-890`).
- The library never closes the `FILE*`.
- Handles and their internal buffers are allocated with `malloc` and freed with `free`, not
  through `bzalloc`.
- After an error the manual says only `Close` is allowed (`manual.xml:1661-1679`). The code does
  not enforce this: `BZ2_bzRead`/`BZ2_bzWrite` do not consult `lastErr`.
- Not thread-safe on the same handle. They perform stdio I/O; the `FILE*` should be in binary
  mode (`manual.xml:1681-1687`).

#### `BZ2_bzReadOpen`

```c
BZFILE* BZ2_bzReadOpen ( int* bzerror, FILE* f, int verbosity, int small, void* unused, int nUnused );
```
Declared `bzlib.h:142-149`, defined `bzlib.c:1090-1142`. stdio only.

Creates a read handle that decompresses one bzip2 stream from `f`, first consuming `nUnused`
bytes copied from `unused`.

| Parameter | Meaning | Valid |
|---|---|---|
| `bzerror` | out: status. | may be `NULL` |
| `f` | open for reading, `ferror(f) == 0`. Borrowed: must stay open until `BZ2_bzReadClose`. | non-`NULL` |
| `verbosity` | as `BZ2_bzDecompressInit`. | 0..4 |
| `small` | as `BZ2_bzDecompressInit`. | 0 or 1 |
| `unused` | bytes to decompress before reading `f` (typically the output of `BZ2_bzReadGetUnused` of a previous stream). Copied into the handle (`bzlib.c:1127-1131`), so the caller's buffer may be reused on return. if `NULL`, `nUnused` must be 0 |
| `nUnused` | number of bytes at `unused`. | 0..`BZ_MAX_UNUSED` |

`*bzerror` (return value `NULL` unless `BZ_OK`):

| Code | When |
|---|---|
| `BZ_PARAM_ERROR` | `f == NULL`; `small` not 0/1; `verbosity` outside 0..4; `unused == NULL && nUnused != 0`; `unused != NULL && (nUnused < 0 or > 5000)` (`bzlib.c:1103-1108`) **(verified)**. `unused != NULL` with `nUnused == 0` is accepted. |
| `BZ_IO_ERROR` | `ferror(f)` (`bzlib.c:1110-1111`). |
| `BZ_MEM_ERROR` | `malloc` of the handle failed (`bzlib.c:1113-1115`), or `BZ2_bzDecompressInit` returned it. |
| `BZ_CONFIG_ERROR` | from `BZ2_bzDecompressInit` (`bzlib.c:1133-1135`). |
| `BZ_OK` | success; handle returned. |

Side effects: `malloc`, one `bzalloc` (default allocator). No I/O on `f` yet.

#### `BZ2_bzRead`

```c
int BZ2_bzRead ( int* bzerror, BZFILE* b, void* buf, int len );
```
Declared `bzlib.h:163-168`, defined `bzlib.c:1164-1220`. stdio only.

Decompresses up to `len` bytes into `buf`, reading `f` in chunks of up to 5000 bytes when the
internal buffer is empty (`bzlib.c:1192-1200`).

| Parameter | Meaning | Valid |
|---|---|---|
| `bzerror` | out | may be `NULL` |
| `b` | handle from `BZ2_bzReadOpen` | non-`NULL`, read handle |
| `buf` | destination, `len` bytes | non-`NULL` |
| `len` | bytes wanted | ≥ 0 |

| `*bzerror` | Return value | When |
|---|---|---|
| `BZ_PARAM_ERROR` | 0 | `b`, `buf` `NULL` or `len < 0` (`bzlib.c:1175-1176`). |
| `BZ_SEQUENCE_ERROR` | 0 | write handle (`bzlib.c:1178-1179`); or the stream already ended (from `BZ2_bzDecompress`, `bzlib.c:1204-1205`) **(verified)**. |
| `BZ_OK` | 0 | `len == 0` (`bzlib.c:1181-1182`). |
| `BZ_IO_ERROR` | 0 | `ferror(f)` before or after an `fread` (`bzlib.c:1189-1190`, `1195-1196`). |
| `BZ_UNEXPECTED_EOF` | 0 | `BZ2_bzDecompress` returned `BZ_OK`, `f` is at EOF, no buffered input and `buf` not full (`bzlib.c:1207-1209`). This includes an empty file. |
| `BZ_DATA_ERROR`, `BZ_DATA_ERROR_MAGIC`, `BZ_MEM_ERROR` | 0 | passed through from `BZ2_bzDecompress` (`bzlib.c:1204-1205`). |
| `BZ_STREAM_END` | bytes stored (0..`len`) | end of stream reached (`bzlib.c:1211-1213`). |
| `BZ_OK` | `len` | `buf` filled (`bzlib.c:1214-1215`). |

On errors after decompression started, bytes may already have been written into `buf` though 0
is returned. Side effects: `fread`, and `fgetc`/`ungetc` to probe EOF (`myfeof`,
`bzlib.c:906-912`); may allocate the block arrays; verbosity output. Reads only one stream: it
returns `BZ_STREAM_END` at the first end-of-stream marker and keeps the over-read bytes in the
handle.

#### `BZ2_bzReadGetUnused`

```c
void BZ2_bzReadGetUnused ( int* bzerror, BZFILE* b, void** unused, int* nUnused );
```
Declared `bzlib.h:156-161`, defined `bzlib.c:1224-1241`. stdio only.

Returns the bytes read from `f` but not consumed by the stream.

| `*bzerror` | When |
|---|---|
| `BZ_PARAM_ERROR` | `b == NULL` (`bzlib.c:1231-1232`); or `unused`/`nUnused` `NULL` (`bzlib.c:1235-1236`, checked *after* the sequence check). |
| `BZ_SEQUENCE_ERROR` | `b->lastErr != BZ_STREAM_END` (`bzlib.c:1233-1234`): end of stream not yet signalled, write handle, or a previous call of this function already succeeded (it resets `lastErr` to `BZ_OK`) **(verified)**. |
| `BZ_OK` | `*unused = next_in`, `*nUnused = avail_in` (0..5000) (`bzlib.c:1238-1240`). |

`*unused` points into the handle's internal buffer: valid until the next call on `b` and
invalidated by `BZ2_bzReadClose`, so it must be copied first (as `bzip2.c:475-478` does).
No I/O, no allocation.

#### `BZ2_bzReadClose`

```c
void BZ2_bzReadClose ( int* bzerror, BZFILE* b );
```
Declared `bzlib.h:151-154`, defined `bzlib.c:1146-1160`. stdio only.

Frees a read handle in any state (including after errors). `b == NULL`: `BZ_OK`, nothing done
(`bzlib.c:1151-1152`). Write handle: `BZ_SEQUENCE_ERROR`, nothing freed (`bzlib.c:1154-1155`).
Otherwise ends the embedded stream and `free`s the handle; `*bzerror = BZ_OK` (set at
`bzlib.c:1150`). Does not close `f`.

#### `BZ2_bzWriteOpen`

```c
BZFILE* BZ2_bzWriteOpen ( int* bzerror, FILE* f, int blockSize100k, int verbosity, int workFactor );
```
Declared `bzlib.h:170-176`, defined `bzlib.c:916-959`. stdio only.

| Parameter | Meaning | Valid |
|---|---|---|
| `bzerror` | out | may be `NULL` |
| `f` | open for writing, `ferror(f) == 0`; borrowed until close | non-`NULL` |
| `blockSize100k` | as `BZ2_bzCompressInit` | 1..9 |
| `verbosity` | as `BZ2_bzCompressInit`, but range-checked here | 0..4 |
| `workFactor` | as `BZ2_bzCompressInit` (0 → 30, `bzlib.c:950`) | 0..250 |

| `*bzerror` | When |
|---|---|
| `BZ_PARAM_ERROR` | `f == NULL` or any of the three ranges violated (`bzlib.c:928-932`) **(verified)**. |
| `BZ_IO_ERROR` | `ferror(f)` (`bzlib.c:934-935`). |
| `BZ_MEM_ERROR` | `malloc` of the handle failed, or from `BZ2_bzCompressInit`. |
| `BZ_CONFIG_ERROR` | from `BZ2_bzCompressInit` (`bzlib.c:951-954`). |
| `BZ_OK` | handle returned (all compression memory allocated now). |

Nothing is written to `f` until the first block is complete or the handle is closed.

#### `BZ2_bzWrite`

```c
void BZ2_bzWrite ( int* bzerror, BZFILE* b, void* buf, int len );
```
Declared `bzlib.h:178-183`, defined `bzlib.c:964-1005`. stdio only.

Compresses `len` bytes from `buf` (all of them are consumed before it returns `BZ_OK`), writing
whatever compressed output becomes available to `f` with `fwrite`.

| `*bzerror` | When |
|---|---|
| `BZ_PARAM_ERROR` | `b`/`buf` `NULL` or `len < 0` (`bzlib.c:974-975`). |
| `BZ_SEQUENCE_ERROR` | read handle (`bzlib.c:976-977`) **(verified)**. |
| `BZ_IO_ERROR` | `ferror(f)` on entry (`bzlib.c:978-979`) or a short/failed `fwrite` (`bzlib.c:996-999`). |
| other codes from `BZ2_bzCompress` | any result other than `BZ_RUN_OK` (`bzlib.c:990-992`). Reachable at least as `BZ_SEQUENCE_ERROR` when the embedded stream has left RUNNING, e.g. after a `BZ2_bzWriteClose` that failed part-way left it FINISHING (`bzlib.c:452-453`). With the stream in RUNNING, `avail_out = 5000` and `avail_in > 0`, every `BZ_RUN` call should make progress, so `BZ_PARAM_ERROR` from line 425 is not expected (**uncertain**). |
| `BZ_OK` | `len == 0` (`bzlib.c:981-982`) or all input consumed (`bzlib.c:1002-1003`). |

#### `BZ2_bzWriteClose`

```c
void BZ2_bzWriteClose ( int* bzerror, BZFILE* b, int abandon, unsigned int* nbytes_in, unsigned int* nbytes_out );
```
Declared `bzlib.h:185-191`, defined `bzlib.c:1009-1018`. stdio only.

Exactly `BZ2_bzWriteClose64(bzerror, b, abandon, nbytes_in, NULL, nbytes_out, NULL)`: identical
behaviour, reporting only the low 32 bits of the counts.

#### `BZ2_bzWriteClose64`

```c
void BZ2_bzWriteClose64 ( int* bzerror, BZFILE* b, int abandon,
                          unsigned int* nbytes_in_lo32, unsigned int* nbytes_in_hi32,
                          unsigned int* nbytes_out_lo32, unsigned int* nbytes_out_hi32 );
```
Declared `bzlib.h:193-201`, defined `bzlib.c:1021-1086`. stdio only.

Finishes the stream (unless abandoning), flushes `f`, reports byte counts and frees the handle.
Each count pointer may be `NULL`.

Behaviour, in order:

1. `b == NULL`: `BZ_OK`, nothing else (`bzlib.c:1033-1034`).
2. Read handle: `BZ_SEQUENCE_ERROR`, handle **not** freed (`bzlib.c:1035-1036`).
3. `!abandon && ferror(f)`: `BZ_IO_ERROR`, handle **not** freed (`bzlib.c:1040-1041`).
4. Non-`NULL` counts are set to 0 (`bzlib.c:1043-1046`).
5. If `!abandon && lastErr == BZ_OK`: repeatedly `BZ2_bzCompress(BZ_FINISH)` into the 5000-byte
   buffer and `fwrite` it until `BZ_STREAM_END` (`bzlib.c:1048-1066`). A result other than
   `BZ_FINISH_OK`/`BZ_STREAM_END` returns that code; a short write returns `BZ_IO_ERROR`; in both
   cases the handle is **not** freed and `f` may hold a partial stream.
6. If `!abandon && !ferror(f)`: `fflush(f)`; if that sets the error flag, `BZ_IO_ERROR`, handle
   **not** freed (`bzlib.c:1068-1072`).
7. Counts are set from the embedded stream's totals (`bzlib.c:1074-1081`), `*bzerror = BZ_OK`,
   the stream is ended and the handle `free`d (`bzlib.c:1083-1085`).

Consequences: with `abandon != 0` the call always frees the handle and reports `BZ_OK`, writes
no trailer and does not `fflush`. With `abandon == 0` after an earlier `BZ2_bzWrite` error
(`lastErr != BZ_OK`) no trailer is written but `f` is still flushed and the result is `BZ_OK`.
Whenever the handle was not freed, the caller must call again with `abandon = 1` to release it
(this is what `BZ2_bzclose` does, `bzlib.c:1525-1528`). Side effects: `fwrite`, `fflush`, `free`,
`bzfree`; verbosity output while finishing.

### 5.4 Buffer utilities

#### `BZ2_bzBuffToBuffCompress`

```c
int BZ2_bzBuffToBuffCompress ( char* dest, unsigned int* destLen, char* source, unsigned int sourceLen,
                               int blockSize100k, int verbosity, int workFactor );
```
Declared `bzlib.h:207-215`, defined `bzlib.c:1250-1298`. Built under `BZ_NO_STDIO`: yes.

Compresses `source[0..sourceLen-1]` into one complete stream in `dest[0..*destLen-1]`.

| Parameter | Meaning | Valid |
|---|---|---|
| `dest` | output buffer, `*destLen` bytes; never written at or beyond `dest[*destLen]` | non-`NULL` |
| `destLen` | in: capacity; out (only on `BZ_OK`): compressed size (`bzlib.c:1287`) | non-`NULL` |
| `source`, `sourceLen` | input | `source` non-`NULL` (even if `sourceLen == 0`) |
| `blockSize100k` | 1..9 | checked |
| `verbosity` | 0..4 (checked here, unlike `BZ2_bzCompressInit`) | checked |
| `workFactor` | 0..250, 0 → 30 | checked |

| Code | When |
|---|---|
| `BZ_PARAM_ERROR` | any pointer `NULL` or range violated (`bzlib.c:1262-1267`). |
| `BZ_CONFIG_ERROR`, `BZ_MEM_ERROR` | from `BZ2_bzCompressInit` (`bzlib.c:1273-1275`). |
| `BZ_OUTBUFF_FULL` | `BZ2_bzCompress(BZ_FINISH)` returned `BZ_FINISH_OK`, i.e. output did not fit (`bzlib.c:1283`, `1291-1293`) **(verified)**. `*destLen` unchanged. |
| `BZ_SEQUENCE_ERROR` | `BZ2_bzCompress` made no progress: happens when `sourceLen == 0` and `*destLen == 0` (`bzlib.c:1284`, `1295-1297`, `457`) **(verified)**. |
| `BZ_OK` | stream complete; `*destLen` = compressed size. |

Side effects: stack `bz_stream` with default allocators, freed before return in every path
after `Init`. Thread-safe on distinct buffers.

#### `BZ2_bzBuffToBuffDecompress`

```c
int BZ2_bzBuffToBuffDecompress ( char* dest, unsigned int* destLen, char* source, unsigned int sourceLen,
                                 int small, int verbosity );
```
Declared `bzlib.h:217-224`, defined `bzlib.c:1302-1351`. Built under `BZ_NO_STDIO`: yes.

Decompresses the **first** stream found in `source[0..sourceLen-1]` with a single
`BZ2_bzDecompress` call.

| Parameter | Meaning | Valid |
|---|---|---|
| `dest`, `destLen` | as above; `*destLen` set to the decompressed size only on `BZ_OK` | non-`NULL` |
| `source`, `sourceLen` | compressed input | `source` non-`NULL` |
| `small` | 0 or 1 | checked |
| `verbosity` | 0..4 | checked |

| Code | When |
|---|---|
| `BZ_PARAM_ERROR` | pointer `NULL` or range violated (`bzlib.c:1313-1317`). |
| `BZ_CONFIG_ERROR`, `BZ_MEM_ERROR` | from `BZ2_bzDecompressInit` (`bzlib.c:1322-1323`), or `BZ_MEM_ERROR` from the block allocation. |
| `BZ_DATA_ERROR`, `BZ_DATA_ERROR_MAGIC` | from `BZ2_bzDecompress` (`bzlib.c:1332`, `1348-1350`) **(verified)**. |
| `BZ_UNEXPECTED_EOF` | `BZ2_bzDecompress` returned `BZ_OK` and output space remains, i.e. input ended early (`bzlib.c:1340-1342`) **(verified)**. |
| `BZ_OUTBUFF_FULL` | `BZ2_bzDecompress` returned `BZ_OK` with output space exhausted (`bzlib.c:1343-1345`) **(verified)**. This is also the result for truncated input when `*destLen` happens to be filled exactly (or is 0). |
| `BZ_OK` | first stream decoded. Bytes after its end are ignored **(verified)**. |

Bytes may have been written to `dest` on error returns.

### 5.5 zlib-style compatibility functions

`bzlib.h:227-234` says these are "not _officially_ part of libbzip2 (yet)" and not reviewed for
thread safety. All except `BZ2_bzlibVersion` are stdio only.

#### `BZ2_bzlibVersion`

```c
const char * BZ2_bzlibVersion ( void );
```
Declared `bzlib.h:236-238`, defined `bzlib.c:1369-1372`. Built under `BZ_NO_STDIO`: **yes**.

Returns a pointer to the static string `BZ_VERSION` = `"1.0.8, 13-Jul-2019"`
(`bzlib_private.h:39`) **(verified)**. The caller must not modify or free it. Pure, thread-safe.

#### `BZ2_bzopen`

```c
BZFILE * BZ2_bzopen ( const char *path, const char *mode );
```
Declared `bzlib.h:241-244`, defined `bzlib.c:1463-1468` via `bzopen_or_bzdopen` (`bzlib.c:1385-1454`). stdio only.

Opens a file for compressed reading or writing.

| Parameter | Meaning |
|---|---|
| `path` | file name passed to `fopen`; `NULL` or `""` means `stdin` (reading) / `stdout` (writing) (`bzlib.c:1424-1426`). |
| `mode` | scanned character by character (`bzlib.c:1405-1419`): `'r'` read, `'w'` write (the last of them wins; default read); `'s'` small decompression; a decimal digit sets `blockSize100k` (the last digit wins, default 9; when writing it is clamped to 1..9, so `'0'` means 1, `bzlib.c:1441-1442`; ignored when reading); every other character is ignored. `mode == NULL` → return `NULL` (`bzlib.c:1404`). |

The `FILE*` is opened with `"rb"` or `"wb"` (`bzlib.c:1420-1421`). Fixed parameters: `verbosity
0`, `workFactor 30`, no unused bytes (`bzlib.c:1394-1402`). Returns the handle, or `NULL` if
`mode` is `NULL`, `fopen` fails, or `BZ2_bzReadOpen`/`BZ2_bzWriteOpen` fails; in the last case the
`FILE*` is closed unless it is `stdin`/`stdout` (`bzlib.c:1449-1452`). No error code is
available. Digits are recognised with `isdigit` (`bzlib.c:1414`).

#### `BZ2_bzdopen`

```c
BZFILE * BZ2_bzdopen ( int fd, const char *mode );
```
Declared `bzlib.h:246-249`, defined `bzlib.c:1472-1477`. stdio only.

As `BZ2_bzopen` but uses `fdopen(fd, "rb"/"wb")` (`bzlib.c:1434`). With `BZ_STRICT_ANSI` defined
it always returns `NULL` (`bzlib.c:1431-1432`). Ownership: on failure after `fdopen` succeeded,
the `FILE*` is `fclose`d, which closes `fd` (`bzlib.c:1450`); on success `BZ2_bzclose` will close
`fd` (`bzlib.c:1532-1534`).

#### `BZ2_bzread`

```c
int BZ2_bzread ( BZFILE* b, void* buf, int len );
```
Declared `bzlib.h:251-255`, defined `bzlib.c:1481-1491`. stdio only.

Returns 0 immediately if the handle's `lastErr` is `BZ_STREAM_END` (`bzlib.c:1484`); otherwise
calls `BZ2_bzRead` and returns its byte count if the status is `BZ_OK` or `BZ_STREAM_END`, else
-1. Precondition: `b` non-`NULL` (dereferenced unchecked at `bzlib.c:1484`) and a read handle
(a write handle yields -1). Only the first stream of a file is read.

#### `BZ2_bzwrite`

```c
int BZ2_bzwrite ( BZFILE* b, void* buf, int len );
```
Declared `bzlib.h:257-261`, defined `bzlib.c:1495-1505`. stdio only.

Calls `BZ2_bzWrite`; returns `len` if the status is `BZ_OK` (including `len == 0`), else -1.
`NULL` arguments yield -1 (via `BZ_PARAM_ERROR`).

#### `BZ2_bzflush`

```c
int BZ2_bzflush ( BZFILE* b );
```
Declared `bzlib.h:263-265`, defined `bzlib.c:1509-1513`. stdio only.

Does nothing and returns 0 (`bzlib.c:1511-1512`). It neither flushes the compressor nor the
`FILE*`.

#### `BZ2_bzclose`

```c
void BZ2_bzclose ( BZFILE* b );
```
Declared `bzlib.h:267-269`, defined `bzlib.c:1517-1535`. stdio only.

`b == NULL`: no-op (`bzlib.c:1522`). Write handle: `BZ2_bzWriteClose(&e, b, 0, NULL, NULL)`; if
that did not return `BZ_OK`, `BZ2_bzWriteClose(NULL, b, 1, NULL, NULL)` to free the handle
(`bzlib.c:1524-1528`). Read handle: `BZ2_bzReadClose` (`bzlib.c:1530`). Then `fclose` of the
`FILE*` unless it is `stdin` or `stdout` (`bzlib.c:1532-1534`). Errors are discarded; the
`fclose` result is ignored.

#### `BZ2_bzerror`

```c
const char * BZ2_bzerror ( BZFILE *b, int *errnum );
```
Declared `bzlib.h:271-274`, defined `bzlib.c:1562-1569`. stdio only.

Reads the handle's `lastErr`, maps every positive value to 0, stores the result in `*errnum` and
returns the static string `bzerrorstrings[-err]` (`bzlib.c:1542-1559`): `"OK"`,
`"SEQUENCE_ERROR"`, `"PARAM_ERROR"`, `"MEM_ERROR"`, `"DATA_ERROR"`, `"DATA_ERROR_MAGIC"`,
`"IO_ERROR"`, `"UNEXPECTED_EOF"`, `"OUTBUFF_FULL"`, `"CONFIG_ERROR"`. So after `BZ_STREAM_END`
it reports `"OK"`/0 **(verified)**. Preconditions: `b` and `errnum` non-`NULL` (both dereferenced
unchecked) and `b` still open.

---

## 6. Exported internals

These are global symbols defined by the library objects (`nm -g --defined-only` on the seven
objects, **verified**) but not declared in `bzlib.h`. They are declared in the private
`bzlib_private.h`, which is not installed. They are **not part of the public API**: they take
pointers to private structures (`EState`, `DState`) whose layout is not exported, carry no
compatibility promise, and are not listed in `libbz2.def` (Windows DLL exports,
`libbz2.def:1-27`). A program can still link against them in the static library (and in the
shared library built by `Makefile-libbz2_so`, which has no export map) and could collide with
them by name. All are present under `BZ_NO_STDIO` except `BZ2_bz__AssertH__fail`.

| Symbol | Kind | Defined | What it is |
|---|---|---|---|
| `BZ2_blockSort` | function | `blocksort.c:1031-1089` | Burrows-Wheeler sort of the current block. |
| `BZ2_compressBlock` | function | `compress.c:602-667` | Emits one block (and stream header/trailer) into the output bit buffer. |
| `BZ2_bsInitWrite` | function | `compress.c:37-41` | Resets the compressor's bit buffer. |
| `BZ2_hbMakeCodeLengths` | function | `huffman.c:63-148` | Length-limited Huffman code lengths from frequencies. |
| `BZ2_hbAssignCodes` | function | `huffman.c:152-166` | Canonical code assignment from lengths. |
| `BZ2_hbCreateDecodeTables` | function | `huffman.c:170-200` | Canonical decode tables (`limit`, `base`, `perm`). |
| `BZ2_decompress` | function | `decompress.c:106-647` | Resumable parser/decoder for one stream up to each decoded block. |
| `BZ2_indexIntoF` | function | `bzlib.c:687-698` | Binary search in the cumulative frequency table (small decoder). |
| `BZ2_bz__AssertH__fail` | function | `bzlib.c:40-86` (stdio builds only) | Fatal internal-error handler. |
| `BZ2_crc32Table` | data | `crctable.c:31-99` | CRC-32 lookup table. |
| `BZ2_rNums` | data | `randtable.c:26-79` | Pseudo-random table for randomised blocks. |

### `BZ2_blockSort`
`void BZ2_blockSort ( EState* s );` (decl `bzlib_private.h:272-273`). Pre: `s->nblock > 0`
block bytes in `((UChar*)s->arr2)[0..nblock-1]`, work arrays as allocated by
`BZ2_bzCompressInit` (`blocksort.c:1019-1030`). Effect: `s->arr1[0..nblock-1]` (`s->ptr`) holds
the sorted rotation order, `s->origPtr` the index of rotation 0; `ftab` and the rest of `arr2`
beyond the block are clobbered. Uses `fallbackSort` when `nblock < 10000` or when the main sort
exceeds its budget `nblock * ((wfact-1)/3)` with `wfact` clamped to 1..100
(`blocksort.c:1044-1080`). Verbosity output at levels 2-4. Assertions 1001-1007; `1003` if
no rotation 0 was found (`blocksort.c:1088`). No allocation.

### `BZ2_compressBlock`
`void BZ2_compressBlock ( EState* s, Bool is_last_block );` (decl `bzlib_private.h:275-276`).
If `s->nblock > 0`: finalises the block CRC, folds it into the combined CRC, sorts the block,
writes the block header, CRC, randomised bit (always 0), `origPtr`, mapping table, selectors,
code tables and Huffman-coded symbols. If `s->blockNo == 1` it first resets the bit buffer and
writes the stream header. If `is_last_block` it appends the end-of-stream marker and combined
CRC and pads to a byte boundary. Output goes to `s->zbits`/`s->numZ` (`compress.c:602-667`).
Assertions 3001-3007, 2001-2002, 1001-1007. Verbosity output at 2 and 3.

### `BZ2_bsInitWrite`
`void BZ2_bsInitWrite ( EState* s );` (decl `bzlib_private.h:278-279`). Sets `s->bsLive = 0`,
`s->bsBuff = 0` (`compress.c:39-40`). No other effect.

### `BZ2_hbMakeCodeLengths`
`void BZ2_hbMakeCodeLengths ( UChar *len, Int32 *freq, Int32 alphaSize, Int32 maxLen );` (decl
`bzlib_private.h:284-285`). Pre: `alphaSize` ≤ `BZ_MAX_ALPHA_SIZE` (258), arrays of that size.
Writes Huffman code lengths into `len[0..alphaSize-1]` with every length ≤ `maxLen`; zero
frequencies count as 1; when a length exceeds `maxLen` all weights are halved (`1 + w/2`) and
the tree is rebuilt (`huffman.c:79-147`). Termination requires `maxLen` to be large enough for
`alphaSize`; this is not checked (**uncertain** what the exact bound is). The library calls it
with `maxLen = 17` and `alphaSize` ≤ 258 (`compress.c:450-451`). Assertions 2001, 2002. `freq`
is read only.

### `BZ2_hbAssignCodes`
`void BZ2_hbAssignCodes ( Int32 *code, UChar *length, Int32 minLen, Int32 maxLen, Int32 alphaSize );`
(decl `bzlib_private.h:281-282`). Assigns canonical codes: in increasing length, then increasing
symbol index, consecutive integers, shifting left by one between lengths (`huffman.c:160-165`).

### `BZ2_hbCreateDecodeTables`
`void BZ2_hbCreateDecodeTables ( Int32 *limit, Int32 *base, Int32 *perm, UChar *length, Int32 minLen, Int32 maxLen, Int32 alphaSize );`
(decl `bzlib_private.h:490-492`). Builds `perm` (symbols sorted by length), `base` and `limit`
for canonical decoding (`huffman.c:180-199`). Pre: every `length[i]` in `minLen..maxLen` and
≤ 21, because only the first `BZ_MAX_CODE_LEN` (23) entries of `base`/`limit` are cleared and
summed (`huffman.c:185-190`); `perm` has room for `alphaSize` entries. The decoder guarantees
lengths 1..20 (`decompress.c:327`). No validation of its own.

### `BZ2_decompress`
`Int32 BZ2_decompress ( DState* s );` (decl `bzlib_private.h:487-488`). Resumable state
machine (a `switch` over `s->state` with `case` labels inside `GET_BITS`, `decompress.c:43-65`,
`195`) that reads the stream header, block headers, tables and Huffman data, and builds the
inverse-BWT vector. Returns `BZ_OK` (needs input, or block ready with `s->state = BZ_X_OUTPUT`),
`BZ_STREAM_END` (with `s->state = BZ_X_IDLE`), `BZ_DATA_ERROR_MAGIC` (bad `BZh` or block-size
byte, `decompress.c:198-208`), `BZ_MEM_ERROR` (block buffer allocation fails,
`decompress.c:211-220`), `BZ_DATA_ERROR` (bad block or end-of-stream magic, `225-235`,
`591-599`; `origPtr` out of range, `261-264`, `497-498`; no symbols in use, `283`; bad
`nGroups`/`nSelectors`/selector, `288-297`; code length outside 1..20, `327`; Huffman decoding
errors in `GET_MTF_VAL`, `75-101`; run too long or block overflow, `396`, `410`, `417`, `427`;
bad `unzftab`/`cftab`, `502-522`). Local variables are saved in `s->save_*` on every return
(`decompress.c:619-646`); the exception is the `return True;` inside `BZ_GET_FAST`/`BZ_GET_SMALL`
used at `decompress.c:557`, `560`, `576`, `579` (`bzlib_private.h:446`, `477`), which returns 1
without saving, after `s->state` is already `BZ_X_OUTPUT`; the preceding `cftab` checks
(`decompress.c:497-522`) appear to make it unreachable (**uncertain**), and `BZ2_bzDecompress`
would not pass the 1 on (`bzlib.c:851`). Allocates `tt` or `ll16`/`ll4` through `bzalloc`. Assertions 4001,
4002. Does **not** check CRCs; `BZ2_bzDecompress` does.

### `BZ2_indexIntoF`
`Int32 BZ2_indexIntoF ( Int32 indx, Int32 *cftab );` (decl `bzlib_private.h:484-485`). Returns
the largest `nb` in 0..255 with `cftab[nb] <= indx`, by binary search over `cftab[0..256]`
(`bzlib.c:687-698`). Pure. Defined `__inline__` but has external linkage because of the
`extern` declaration.

### `BZ2_bz__AssertH__fail`
`void BZ2_bz__AssertH__fail ( int errcode );` (decl `bzlib_private.h:58`; only without
`BZ_NO_STDIO`). Prints a bug-report message with `errcode` and `BZ2_bzlibVersion()` to
`stderr`, an extra note for `errcode == 1007`, and calls `exit(3)` (`bzlib.c:40-86`). Never
returns; terminates the whole process (unsafe for libraries embedded in long-running programs;
no cleanup). Known error codes: 1001-1007 (`blocksort.c:646`, `1003`, `1088`, `111`, `328`, `909`,
`937`), 2001-2002 (`huffman.c:98`, `112`), 3001-3007 (`compress.c:272`, `455`, `456`, `488`,
`489`, `552`, `594`), 4001-4002 (`decompress.c:614`, `617`), 6001 (`bzlib.c:855`).

### `BZ2_crc32Table`
`UInt32 BZ2_crc32Table[256]` (decl `bzlib_private.h:155`, def `crctable.c:31-99`). Table for the
MSB-first CRC-32 with polynomial `0x04C11DB7` (entry 1 is `0x04c11db7`); used by `BZ_UPDATE_CRC`
(`bzlib_private.h:167-172`). Not `const`; writing to it would corrupt every CRC.

### `BZ2_rNums`
`Int32 BZ2_rNums[512]` (decl `bzlib_private.h:131`, def `randtable.c:26-79`). Run lengths used
to de-randomise blocks whose randomised bit is set (`BZ_RAND_UPD_MASK`,
`bzlib_private.h:143-149`). The compressor never sets the bit, so the table is only read when
decoding old streams. Not `const`.

---

## 7. Programs

`make install` puts these in `$(PREFIX)/bin` (default `/usr/local`, `Makefile:27`,
`Makefile:72-109`): `bzip2`; `bunzip2` and `bzcat` (separate *copies* of the `bzip2` binary,
`Makefile:79-80`); `bzip2recover`; `bzgrep` with symlinks `bzegrep`, `bzfgrep`; `bzmore` with
symlink `bzless`; `bzdiff` with symlink `bzcmp` (`Makefile:92-101`). It also installs
`bzlib.h`, `libbz2.a` and man pages (`Makefile:86-109`).

### 7.1 `bzip2`, `bunzip2`, `bzcat`

One program, `bzip2.c`. Its behaviour depends on the base name of `argv[0]` (text after the last
`/`, `bzip2.c:1828-1835`):

- contains `unzip` or `UNZIP` → decompress (`bzip2.c:1870-1872`) — `bunzip2`;
- contains `z2cat`, `Z2CAT`, `zcat` or `ZCAT` → decompress to standard output
  (`bzip2.c:1874-1880`) — `bzcat`;
- otherwise compress — `bzip2`.

**Arguments.** Tokens from environment variable `BZIP2`, then `BZIP`, are split on whitespace
(each truncated to 1024 characters) and placed *before* `argv[1..]` (`bzip2.c:1757-1780`,
`1841-1845`). They are treated exactly like command-line tokens, so a non-flag token in these
variables is taken as a file name **(verified)**. A token `--` ends option processing; later
tokens are file names. Any other token starting with `-` is an option; everything else is a
file name (`bzip2.c:1852-1858`). The lone token `-` is an option with no letters, i.e. ignored;
it does not mean standard input **(verified)**. Options are processed in two passes over the
whole argument list, first all short flags, then all long flags (`bzip2.c:1884-1948`). Within
each pass the last conflicting flag wins (`-d -z` compresses, `-z -d` decompresses), and the
long-flag pass always overrides the short-flag pass whatever the positions (`--decompress -z`
decompresses, `-9 --fast` gives block size 1) (`bzip2.c:1890-1891`, `1923-1940`). An invalid
flag or `-h` stops processing at its position in its pass.

**Options.**

| Option | Effect | Source |
|---|---|---|
| `-c`, `--stdout` | write to standard output (source mode F2O) | `bzip2.c:1889`, `1925` |
| `-d`, `--decompress` | decompress | `1890`, `1926` |
| `-z`, `--compress` | compress | `1891`, `1927` |
| `-t`, `--test` | test integrity, no output | `1893`, `1929` |
| `-f`, `--force` | overwrite existing output (it is `remove`d first, `1211-1213`, `1397-1399`); allow non-regular-file input and inputs with hard links; when decompressing, copy data that is not bzip2 through unchanged (see below) | `1892`, `1928` |
| `-k`, `--keep` | do not delete input files | `1894`, `1930` |
| `-s`, `--small` | small-memory decompression; when compressing, caps block size at 2 | `1895`, `1931`, `1951-1952` |
| `-q`, `--quiet` | suppress non-critical messages (`noisy = False`) | `1896`, `1932` |
| `-v`, `--verbose` | `verbosity++`, capped at 4 | `1908`, `1940`, `1950` |
| `-1`…`-9` | block size 100k…900k (default 9) | `1897-1905` |
| `--fast` / `--best` | `-1` / `-9` | `1938-1939` |
| `-L`, `--license`, `-V`, `--version` | print version and license to `stderr` and **continue** | `1906-1907`, `1933-1934` |
| `-h`, `--help` | print usage to `stderr`, exit 0 | `1909-1911`, `1941` |
| `--exponential` | `workFactor = 1` (undocumented) | `1935` |
| `--repetitive-best`, `--repetitive-fast` | print "redundant" warning, no effect | `1936-1937` |
| any other `-x` or `--xxx` | "Bad flag", usage, exit 1 | `1912-1916`, `1943-1947` |

Short flags can be combined (`-vk9`). `-c` together with `-t` is rejected with exit 1
(`bzip2.c:1954-1958`). Defaults: compress, block size 9, `workFactor` 30, verbosity 0
(`bzip2.c:1801-1814`).

**Source modes** (`bzip2.c:191-194`, `1862-1863`, `1960-1961`): no file names → stdin to stdout
(I2O); file names with `-c` (or as `bzcat`) → each file to stdout (F2O); otherwise file to file
(F2F).

**Files read and written.**

- Compression F2F: input `name`, output `name.bz2` (`bzip2.c:1160-1164`). Decompression F2F:
  output name by suffix mapping `.bz2`→``, `.bz`→``, `.tbz2`→`.tar`, `.tbz`→`.tar`, otherwise
  `name.out` with a warning (`bzip2.c:1112-1117`, `1344-1352`).
- Refusals (each sets exit status 1 and skips the file): input missing or unreadable; input is a
  directory; F2F input not a regular file per `lstat` (so symlinks too) unless `-f`; F2F output
  exists unless `-f`; F2F input has other hard links unless `-f`; compressing a file that already
  ends in `.bz2`, `.bz`, `.tbz2` or `.tbz` (even with `-c` or `-f`, **verified**); compressed
  output to a terminal; compressed input from a terminal (`bzip2.c:1171-1227`, `1237-1263`,
  `1360-1413`, `1426-1434`, `1540-1575`). File names longer than 1024 bytes abort with exit 1
  (`bzip2.c:929-945`).
- F2F output is created with `open(O_WRONLY|O_CREAT|O_EXCL, 0600)` (`bzip2.c:970-983`); after
  writing, its mode and owner are copied from the input with `fchmod`/`fchown` (ownership errors
  ignored) and, after closing, its access/modification times with `utime`
  (`bzip2.c:1059-1088`, `1309-1310`, `1486-1488`). Then the input is deleted unless `-k`
  (`bzip2.c:1312-1315`, `1490-1493`).
- Decompression handles concatenated streams: after each `BZ_STREAM_END` the unused bytes are
  fed to a new `BZ2_bzReadOpen` until EOF (`bzip2.c:454-482`). Without `-f`, if a later stream
  has a bad magic number the rest is reported as "trailing garbage after EOF ignored" and the
  file counts as success (`bzip2.c:533-544`, `626-637`). With `-f`, a bad magic number in a later
  stream instead jumps to `trycat` (`bzip2.c:465`, `506-517`), which rewinds the input and appends
  *all* of it, including the already-decompressed streams, to the output; see
  [§9 item 18](#9-discrepancies-between-the-documentation-and-the-code).
- If the *first* stream has a bad magic number: without `-f` the file is reported as "not a
  bzip2 file", its F2F output is removed and exit status 2 is recorded, and processing continues
  with the next file (`bzip2.c:1495-1515`); with `-f` the whole input is copied unchanged to the
  output (`trycat`, `bzip2.c:465`, `506-517`) and treated as success.
- `-t` reads only; it writes nothing.

**Exit status** (`setExit` keeps the maximum, `bzip2.c:652-656`; man page `bzip2.1:180-183`):

| Code | Cause |
|---|---|
| 0 | success; also `-h`/`--help` |
| 1 | environmental: bad flag, `-c` with `-t`, per-file refusals listed above (processing continues), I/O error (`ioError`, immediate exit after cleanup), out of memory (`outOfMemory`), over-long file name, `SIGINT`/`SIGTERM`/`SIGHUP` in F2F mode (`bzip2.c:791-813`, `880-889`, `1965-1971`; in I2O/F2O modes no handler is installed and the default signal action applies) |
| 2 | corrupt or non-bzip2 input: CRC/data error or unexpected EOF while decompressing (immediate exit, `bzip2.c:762-788`); "not a bzip2 file" (recorded, continues); any `-t` failure (recorded, continues, `bzip2.c:2020-2030`); `SIGSEGV`/`SIGBUS` while decompressing or testing (`bzip2.c:875`) |
| 3 | internal error: `panic` (`bzip2.c:747-758`); `BZ_CONFIG_ERROR` (`bzip2.c:893-904`); `SIGSEGV`/`SIGBUS` while compressing (`bzip2.c:875`); library assertion (`exit(3)` in `BZ2_bz__AssertH__fail`, without the program's cleanup) |

On fatal errors in F2F mode `cleanUpAndFail` deletes the partial output file, but only if the
input still exists (`bzip2.c:688-743`). The `SIGSEGV`/`SIGBUS` handler calls `_exit` without
cleanup (`bzip2.c:872-876`).

**Environment:** `BZIP2`, `BZIP` (extra arguments, as above). No other variables are read.
Output on `stderr`: messages, and with `-v` a per-file ratio line (`bzip2.c:383-407`); `-vv` and
above add library diagnostics.

### 7.2 `bzip2recover`

`bzip2recover.c`, standalone (does not use `libbz2`). Usage: `bzip2recover damaged_file_name`
(exactly one argument, else usage message and exit 1, `bzip2recover.c:354-376`).

- Prints a banner to `stderr` always (`bzip2recover.c:351-352`).
- Pass 1 scans the input bit by bit for the 48-bit block magic `0x314159265359` and end-of-stream
  magic `0x177245385090` (`bzip2recover.c:316-320`, `403-447`) and records candidate blocks of at
  least 130 bits (`bzip2recover.c:431-440`). It aborts with exit 1 on the 50000th
  magic-pattern match (recorded or not): `currBlock` starts at 0 (`bzip2recover.c:398`) and the
  check `currBlock >= BZ_MAX_HANDLED_BLOCKS - 1` runs before `currBlock++`
  (`bzip2recover.c:326`, `441-443`), so 49999 matches are accepted and the 50000th aborts with
  "appears to contain more than 50000 blocks" (`tooManyBlocks`, `bzip2recover.c:129-140`).
- Pass 2 writes each block as a separate single-block stream `rec%05d<basename>` in the
  directory of the input, with `.bz2` appended unless the name already ends in `.bz2`
  (`bzip2recover.c:507-527`). Each file is `BZh9` + block magic + the block bits + end-of-stream
  magic + the block's own CRC as the combined CRC, padded to a byte (`bzip2recover.c:497-501`,
  `539-545`, `226-246`). The header always says block size 9.
- Output files are created with `O_EXCL` and mode 0600; an existing file or symlink makes it fail
  (`bzip2recover.c:282-302`, `532-537`) — rerunning in the same directory exits 1
  **(verified)**.
- Exit status: 0 on success; 1 for usage errors, names of 1980+ characters
  (`bzip2recover.c:378-383`), unreadable input, no block found, too many blocks, read/write or
  `malloc` failures (`bzip2recover.c:91-141`, `453-458`, `533-537`).
- Environment: none.

### 7.3 `bzgrep`, `bzegrep`, `bzfgrep`

`/bin/sh` script `bzgrep` (`bzgrep:1-85`); the other two names are symlinks to it.

- Prepends `/usr/bin` to `PATH` (`bzgrep:9`).
- Chooses the matcher by invocation name: `*egrep` → `${EGREP-egrep}`, `*fgrep` →
  `${FGREP-fgrep}`, otherwise `${GREP-grep}` (`bzgrep:11-16`). With `-e`/`-f` and plain `grep`
  it switches to `egrep` (`bzgrep:20-23`).
- Options before the pattern are passed to grep; `-A`/`-B` take an argument (`bzgrep:18-33`).
  No pattern → usage on stdout, exit 1 (`bzgrep:35-39`).
- With no files: `bzip2 -cdfq | grep` on stdin (`bzgrep:51-54`). Otherwise for each file (if it
  does not exist but `file.bz2` does, uses that, `bzgrep:58`) runs `bzip2 -cdfq file | grep`,
  prefixing lines with `file:` when more than one file is given and `-h` is not (`bzgrep:57-84`).
  Because of `-f`, non-bzip2 files are searched as plain text.
- Exit status: grep's status for stdin; otherwise the last non-zero grep status, or 0
  (`bzgrep:56`, `83-85`).
- Environment: `GREP`, `EGREP`, `FGREP`, `PATH`; and `BZIP2`/`BZIP` affect the `bzip2` it runs.

### 7.4 `bzmore`, `bzless`

`/bin/sh` script `bzmore` (`bzmore:1-61`); `bzless` is a symlink. Pager is `less` if the name
ends in `less`, else `more` (`bzmore:8-12`); `PATH` gets `/usr/bin` prepended (`bzmore:6`). With
no arguments and stdin not a terminal, pages `bzip2 -cdfq` of stdin; with no arguments on a
terminal prints usage. With files, pages `bzip2 -cdfq FILE` for each, prompting
between files (`e`/`q` quits, `s` skips) using `stty`/`dd` on the terminal (`bzmore:33-60`).
Restores terminal settings on exit via `trap` (`bzmore:20-31`). Exit status: that of the trap's
`exit`, i.e. the last command (**uncertain**: not otherwise defined). Environment: `PATH`;
`BZIP2`/`BZIP` affect `bzip2`.

### 7.5 `bzdiff`, `bzcmp`

`/bin/sh` script `bzdiff` (`bzdiff:1-76`); `bzcmp` is a symlink. Comparator is `${CMP-cmp}` if
the name ends in `cmp`, else `${DIFF-diff}` (`bzdiff:16-20`). Arguments starting with `-` are
options for the comparator; others must be existing regular files, else "not found" and exit 1
(`bzdiff:22-35`).

- One file `F`: compares `bzip2 -cd F.bz2` (with a trailing `.bz2` removed from `F` first) with
  `F` (`bzdiff:41-44`).
- Two files: each `*.bz2` operand is decompressed (`bzip2 -cdfq`); if both are, the second goes
  to a `mktemp` file under `${TMPDIR:-/tmp}` that is removed afterwards (`bzdiff:46-71`).
- Zero or more than two files: usage, exit 1. Otherwise exits with the comparator's status
  (`bzdiff:72-76`).
- Environment: `CMP`, `DIFF`, `TMPDIR`, `PATH` (gets `/usr/bin:/bin` prepended, `bzdiff:15`);
  `BZIP2`/`BZIP` affect `bzip2`.

---

## 8. The .bz2 format

Described as `compress.c` writes it and `decompress.c` reads it. Bits are written and read
most-significant bit first: the compressor accumulates bits at the top of a 32-bit word and emits
its high byte (`compress.c:58-78`); the decoder takes bits from the top of its buffer
(`decompress.c:43-53`). Multi-bit fields are big-endian. Only the stream header starts on a byte
boundary; block headers and the end-of-stream marker follow the previous block's last bit with no
padding; the stream is zero-padded to a byte boundary only after the combined CRC
(`compress.c:46-54`, `609`, `622-628`, `665`). A file may contain several streams back to back;
each library decoder instance reads one.

### 8.1 Stream header (4 bytes, byte-aligned)

| Field | Value | Write | Read/check |
|---|---|---|---|
| magic | `0x42 0x5A 0x68` (`"BZh"`) | `compress.c:624-626` | `decompress.c:197-204`; mismatch → `BZ_DATA_ERROR_MAGIC` |
| block size | `'1'..'9'` (`0x31..0x39`) = `blockSize100k` | `compress.c:627` | `decompress.c:206-209`; other → `BZ_DATA_ERROR_MAGIC` |

The decoder allocates its block arrays from this digit (`decompress.c:211-220`) and rejects any
block with more than `100000 * blockSize100k` symbols (`decompress.c:358`, `410`, `417`, `427`).

### 8.2 Block (repeated 0 or more times)

| Field | Bits | Content |
|---|---|---|
| block magic | 48 | `0x314159265359` (`compress.c:632-634`; `decompress.c:224-235`, mismatch → `BZ_DATA_ERROR`). The first byte decides block vs end-of-stream: `0x31` block, `0x17` end (`decompress.c:224-225`). |
| block CRC | 32 | CRC of this block's original bytes ([§8.5](#85-crcs)) (`compress.c:637`; `decompress.c:241-249`). |
| randomised | 1 | always 0 when written (`compress.c:639-648`); 1 makes the decoder XOR the BWT output with a mask driven by `BZ2_rNums` (`decompress.c:251`, `bzlib.c:540-587`, `710-757`, `bzlib_private.h:133-149`). |
| origPtr | 24 | row of the original string in the sorted rotations (`compress.c:650`; `decompress.c:253-264`). |
| used map | 16 + 16·k | 16 bits, bit *i* set iff any byte in `16i..16i+15` occurs; then for each set bit *i*, 16 bits for bytes `16i+j` (`compress.c:494-511`; `decompress.c:267-282`). `nInUse` = number of bytes marked. |
| nGroups | 3 | number of Huffman tables, 2..6 (`compress.c:273-277`, `519`; `decompress.c:287-288`). |
| nSelectors | 15 | number of 50-symbol groups (`compress.c:520`; `decompress.c:289-290`). |
| selectors | nSelectors × unary | MTF-coded table index *j* written as *j* one-bits then a zero (`compress.c:461-478`, `521-524`; `decompress.c:291-320`). |
| code lengths | per table | 5-bit starting length, then for each of `alphaSize = nInUse + 2` symbols: `10` = +1, `11` = −1, repeated, then `0` = next symbol (`compress.c:531-539`; `decompress.c:323-335`). |
| data | variable | Huffman-coded symbols, table chosen per group of 50 by the selectors, ending with EOB (`compress.c:544-593`; `decompress.c:357-492`). |

Block contents, at the level the code implements them:

1. **Initial run-length encoding (RLE1)** of the input bytes: runs of 1-3 equal bytes are copied;
   runs of 4..255 become four copies followed by one byte `run_length - 4` (0..251)
   (`bzlib.c:216-247`, `260-284`). The compressor stops adding input to a block once it holds
   `100000*blockSize100k - 19` RLE1 bytes (`bzlib.c:194`, `298`, `314`); the margin absorbs the
   bytes still added for runs in progress, keeping blocks under the decoder's limit. The decoder undoes this: after four equal bytes the next byte is
   a repeat count (0..255 accepted) (`bzlib.c:536-804`).
2. **Burrows-Wheeler transform** of the RLE1 block (`BZ2_blockSort`), giving the last column
   and `origPtr`.
3. **Move-to-front** over the alphabet of used bytes (in increasing byte order), with **zero-run
   coding**: a run of *n* MTF zeros is written as the bijective base-2 digits of *n*, least
   significant first, `RUNA` (=0) for digit 1 and `RUNB` (=1) for digit 2; a non-zero MTF index
   *k* is written as symbol *k+1*; the block ends with `EOB = nInUse + 1` (`compress.c:120-231`;
   decoded at `decompress.c:381-492`).
4. **Huffman coding** with up to 6 canonical tables, code lengths 1..17 as written
   (`compress.c:449-451`, `488-489`), 1..20 accepted (`decompress.c:327`, `91`); codes assigned
   by `BZ2_hbAssignCodes`.

### 8.3 End-of-stream marker and trailer

| Field | Bits | Content |
|---|---|---|
| end magic | 48 | `0x177245385090` (`compress.c:659-661`; `decompress.c:588-599`, mismatch → `BZ_DATA_ERROR`) |
| combined CRC | 32 | ([§8.5](#85-crcs)) (`compress.c:662`; `decompress.c:601-609`) |
| padding | 0-7 | zero bits to the next byte boundary (`compress.c:46-54`, `665`). The decoder does not check them. |

An empty input produces the 14-byte stream `42 5A 68 39 17 72 45 38 50 90 00 00 00 00`
(for block size 9) **(verified)**.

### 8.4 Concatenated streams

Streams may follow each other directly. `bzip2` decodes all of them; `BZ2_bzDecompress`,
`BZ2_bzRead`, `BZ2_bzread` and `BZ2_bzBuffToBuffDecompress` stop after the first
([§5](#5-public-functions)).

### 8.5 CRCs

- Block CRC: CRC-32 with polynomial `0x04C11DB7`, not reflected, initial value `0xFFFFFFFF`,
  final complement (`bzlib_private.h:157-172`, `crctable.c`), over the block's original input
  bytes before RLE1 (`bzlib.c:220-222`, `267`) — the "CRC-32/BZIP2" variant; check value for
  `"123456789"` is `0xFC891918` **(verified)**. The decoder computes it over its output bytes
  (`bzlib.c:548`, `616`, `627`, `718`, `767`) and compares when the block is exhausted
  (`bzlib.c:824-831`).
- Combined CRC: starts at 0; for each block `combined = rotl32(combined, 1) ^ blockCRC`
  (`compress.c:606-608`; `bzlib.c:832-835`). Checked at end of stream (`bzlib.c:847`).

### 8.6 Validation performed by the decoder

Each of these returns `BZ_DATA_ERROR` (from `decompress.c` unless noted): bad block or end magic
(`225-235`, `591-599`); `origPtr > 10 + 100000*blockSize100k` (`261-264`) and later
`origPtr >= nblock` (`497-498`); no byte in use (`283`); `nGroups` outside 2..6 (`288`);
`nSelectors < 1` (`290`); a selector index `>= nGroups` (`297`); a code length leaving 1..20 (`327`);
more groups than selectors (`78-79`); a code longer than 20 bits (`91-92`); a decoded symbol
index outside 0..257 (`98-100`); a zero-run with `N >= 2*1024*1024` (`396`); more than
`100000*blockSize100k` symbols (`410`, `417`, `427`); symbol frequency or cumulative table out of
range or decreasing (`502-522`); inverse-BWT position out of range or overrun during output
(`bzlib_private.h:446`, `453`, `477`, `bzlib.c:560-561`, `633-634`, `730-731`, `779-780`); block
CRC mismatch (`bzlib.c:830`); combined CRC mismatch (`bzlib.c:847`). More than
`BZ_MAX_SELECTORS` (18002) selectors are accepted but the excess ignored (`299-306`).

---

## 9. Discrepancies between the documentation and the code

`manual.xml` is the library manual, `bzip2.1` the man page. In each case the code is
authoritative.

1. **`BZ2_bzCompressInit` and `verbosity`.** Manual: `BZ_PARAM_ERROR` if `verbosity` is outside
   0..4 (`manual.xml:1176-1180`). Code: not checked (`bzlib.c:159-162`) **(verified)**.
   `BZ2_bzWriteOpen`, `BZ2_bzBuffToBuffCompress` do check it.
2. **Unknown action in RUNNING.** Manual: other actions give `BZ_SEQUENCE_ERROR`
   (`manual.xml:1252-1256`). Code: `BZ_PARAM_ERROR` (`bzlib.c:439-440`) **(verified)**.
3. **`BZ_RUN` without progress.** Manual table: RUNNING/`BZ_RUN` returns `BZ_RUN_OK`
   (`manual.xml:1330-1333`). Code: `BZ_PARAM_ERROR` when nothing was consumed or produced
   (`bzlib.c:425`) **(verified)**.
4. **Entering flush/finish.** Manual table: RUNNING/`BZ_FLUSH` returns `BZ_FLUSH_OK`,
   RUNNING/`BZ_FINISH` returns `BZ_FINISH_OK` (`manual.xml:1335-1345`). Code: the request is
   processed as FLUSHING/FINISHING in the same call and can return `BZ_RUN_OK` or
   `BZ_STREAM_END` immediately (`bzlib.c:428-438`) **(verified)**.
5. **`BZ_FINISH` without progress.** Not in the manual. Code returns `BZ_SEQUENCE_ERROR`
   (`bzlib.c:457`) **(verified)**; hence `BZ2_bzBuffToBuffCompress` with empty input and
   `*destLen == 0` returns `BZ_SEQUENCE_ERROR`, not `BZ_OUTBUFF_FULL`.
6. **What is remembered.** Manual: "Remember current value of next_in" (`manual.xml:1336`,
   `1342`). Code remembers and compares `avail_in` (`bzlib.c:429`, `435`, `444`, `454`).
7. **`BZ2_bzDecompress` and `avail_out`.** Manual: `BZ_PARAM_ERROR` if `avail_out < 1`
   (`manual.xml:1574-1576`). Code has no such check (`bzlib.c:812-815`) **(verified)**.
8. **`strm->s`.** The manual's error lists say `strm->s` (`manual.xml:1417`, `1436`, `1575`,
   `1618`); the field is `state` (`bzlib.h:69`).
9. **`BZ2_bzReadOpen` parameter checks.** Manual omits that `verbosity` outside 0..4 gives
   `BZ_PARAM_ERROR` (`manual.xml:1746-1758`; code `bzlib.c:1105`).
10. **`BZ2_bzWriteOpen` parameter checks.** Manual lists only `f` and `blockSize100k`
    (`manual.xml:1987-1989`); code also rejects `workFactor` outside 0..250 and `verbosity`
    outside 0..4 (`bzlib.c:928-932`) **(verified)**.
11. **`BZ2_bzWriteClose` after an error.** Manual: the only action is to release memory; no
    `fflush` (`manual.xml:2075-2083`). Code: with `abandon == 0` it still calls `fflush`
    (`bzlib.c:1068-1072`); it skips only the trailer. Manual also does not mention that
    `b == NULL` gives `BZ_OK` (`bzlib.c:1033-1034`), nor that the handle stays allocated when
    `BZ_IO_ERROR` is returned (`bzlib.c:1040-1041`, `1060-1061`, `1070-1071`).
12. **`BZ2_bzReadGetUnused` twice.** Not in the manual: a successful call resets `lastErr` to
    `BZ_OK`, so a second call returns `BZ_SEQUENCE_ERROR` (`bzlib.c:1233-1238`) **(verified)**.
13. **Typos naming non-existent identifiers.** `BZ_SEQUENCE_END` (`manual.xml:1819-1821`,
    `1868`; means `BZ_STREAM_END`); `BZ2_bzOpenWrite` (`manual.xml:1940`; means
    `BZ2_bzWriteOpen`); `BZ2_bzClose` as the next action after a failed `BZ2_bzReadOpen`
    (`manual.xml:1775`; there is nothing to close, the handle is `NULL`). The manual's sample
    code calls `BZ2_bzWriteOpen`, `BZ2_bzWriteClose` and `BZ2_bzReadOpen` with too few arguments
    (`manual.xml:2187-2189`, `2202`, `2222`). The `BZ2_bzBuffToBuffCompress` section says "BZ2_bzBuffToBuffDecompress will not write data at or
    beyond dest[*destLen]" (`manual.xml:2293-2296`), a copy-paste of the decompress text.
14. **`source == NULL`.** Both buffer utilities return `BZ_PARAM_ERROR` for `source == NULL`
    (`bzlib.c:1263`, `1314`); the manual lists only `dest`/`destLen` (`manual.xml:2303-2307`,
    `2371-2374`).
15. **`BZ_NO_STDIO` function list.** Manual: the library then contains "only the following
    eight functions" (`manual.xml:2471-2482`). Code also keeps `BZ2_bzlibVersion`
    (`bzlib.c:1369`, outside the guard) and all internals of [§6](#6-exported-internals)
    **(verified)**.
16. **`small` "nonzero".** Manual: "If small is nonzero" (`manual.xml:1469`); code accepts only 0
    and 1 (`bzlib.c:502`); the manual's own error list agrees with the code.
17. **Memory figures for `-s`.** `bzip2 --help` says "at most 2500k" (`bzip2.c:1655`); the man
    page and manual say 2300k (`bzip2.1`, `-s` entry; `manual.xml:1473`). By the code the
    small decoder needs `2.5 * 100000 * blockSize100k` bytes for the block (`decompress.c:212-215`)
    plus `sizeof(DState)`; neither figure is derived in the source.
18. **`-f` and trailing garbage.** `bzip2.1` (`-f` entry) says forced decompression passes files
    without the magic header through unmodified, and elsewhere that trailing garbage is ignored.
    Code: under `-f`, a bad magic number in a *later* stream also jumps to `trycat`, which
    `rewind`s the input and appends the **entire** input file to the output after the data
    already decompressed (`bzip2.c:465`, `506-517`) **(verified** with `bzip2 -dcf`; on an
    unseekable input the `rewind` fails silently and only the rest is copied, **uncertain**).
19. **`-V`/`-L` continue.** `bzip2.1` says these "Display the software version, license terms
    and conditions"; the code then continues processing the remaining arguments (it does not
    exit) (`bzip2.c:1906-1907`, `1933-1934`) **(verified)**.
20. **`--exponential`** sets `workFactor = 1` (`bzip2.c:1935`) and is not documented.
21. **Header comment of `bzdiff`.** Says the one-file form compares with "file1.gz"
    (`bzdiff:10`); the code uses `file1.bz2` (`bzdiff:42-43`).
22. **`bzip2recover` write errors** print "I/O error reading" (`bzip2recover.c:104-113`).
23. **Meaning of IDLE.** The manual's table says compression IDLE "only exists after
    BZ2_bzCompressEnd or before BZ2_bzCompressInit" and gives `BZ_SEQUENCE_ERROR`
    (`manual.xml:1325-1328`). In the code IDLE is entered after `BZ_STREAM_END`
    (`bzlib.c:460`); after `End` `strm->state` is `NULL` and the result is `BZ_PARAM_ERROR`
    (`bzlib.c:411-414`, `481`). Before `Init` the result depends on whatever the caller left in
    `strm->state` (`BZ_PARAM_ERROR` only if it is `NULL`).
24. **`BZ_FLUSH` decodability.** The manual presents `BZ_FLUSH` as terminating the current
    block "for error control purposes" (`manual.xml:1299-1314`). It does not say that up to 31
    bits of the flushed block stay in the bit buffer until the next block or the finish
    (`compress.c:657-666`), so the emitted bytes are not independently decodable **(verified)**.

---

## 10. Open questions

1. **Calls after an error.** After `BZ_DATA_ERROR`/`BZ_DATA_ERROR_MAGIC`/`BZ_MEM_ERROR`, the
   decoder state is left at the failing step (`decompress.c:40-41`, `619-646`), not in a
   terminal error state. A further `BZ2_bzDecompress` call resumes from there; for a block-CRC
   failure it would even re-complement `calculatedBlockCRC` (`bzlib.c:824-825`). The manual
   only allows `End` after an error. The exact behaviour of further calls is not characterised
   here (**uncertain**). Similarly `BZ2_bzRead`/`BZ2_bzWrite` keep working on a handle whose
   `lastErr` is an error.
2. **Thread safety** is inferred from the absence of shared mutable state; the source makes no
   promise, and `bzlib.h:227-234` explicitly disclaims it for the zlib-style functions.
3. **`BZ2_bzWrite` error codes.** It passes through anything `BZ2_bzCompress` returns besides
   `BZ_RUN_OK` (`bzlib.c:990-992`). Only `BZ_SEQUENCE_ERROR` (stream no longer RUNNING) was
   identified as reachable; whether `BZ_PARAM_ERROR` (no progress) can occur is not established
   (**uncertain**).
4. **Assertion reachability.** Assertions 1001-1007, 2001-2002, 3001-3007 guard compressor
   invariants and 4001/4002/6001 guard impossible states; whether any is reachable from the
   public API with valid arguments is not established here. 1007 is documented as typically a
   hardware fault (`bzlib.c:56-82`).
5. **Windows.** The `_WIN32` paths of `bzlib.h`, `bzlib.c:1378-1381` and the `BZ_LCCWIN32`
   paths of `bzip2.c` were read but not built or tested.
6. **`bzmore` exit status** is whatever the shell's `trap ... exit` yields (**uncertain**).
