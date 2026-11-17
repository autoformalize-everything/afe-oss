import Bzip2.Oracle.Error
import Bzip2.Oracle.Decompress.Stream

/-!
The oracle's decompression API, over the parts in `Bzip2.Oracle.Decompress.*`.

`decompressStream` is one stream (`Decompress.Stream.decode`), with the result classes of
`BZ2_bzBuffToBuffDecompress` (`bzlib.c:1302-1351`), the library's one-call decompressor:
`Error.magic` for `BZ_DATA_ERROR_MAGIC`, `Error.data` for `BZ_DATA_ERROR`, `Error.eof` for
`BZ_UNEXPECTED_EOF` (`bzlib.c:1339-1342`), checked in the order `BZ2_bzDecompress` checks them.
The byte count it returns is the input size less the `avail_in` that call leaves, which is
also what `BZ2_bzReadGetUnused` reports as unused (`bzlib.c:1239`).

`decompress` is `bzip2 -d`, the program, over a whole input: the loop of `uncompressStream`
(`bzip2.c:454-482`) that decodes one stream after another. Where it differs from a single
`BZ2_bzBuffToBuffDecompress` call on the input:
* Concatenated streams: after a stream, `bzip2` decodes the bytes that follow as the next
  stream, until none are left (`bzip2.c:472-481`). `BZ2_bzBuffToBuffDecompress` returns at the
  end of the first stream and ignores what follows (`bzlib.c:1330-1337`).
* Trailing garbage: a later stream whose header is wrong (`Error.magic`) ends the input, and
  the result is the output of the streams before it (`bzip2.c:465`, `bzip2.c:533-543`). Only
  the first stream's `Error.magic` is an error. Anything else wrong in a later stream is the
  error it is in a first stream (`bzip2.c:527-532`): garbage that starts like a header, such as
  `BZ` (`Error.eof`) or `BZh9` followed by a byte other than `0x17` and `0x31` (`Error.data`),
  is not ignored.
* Errors: `bzip2` has written the output of the earlier streams and blocks when it finds an
  error (`bzip2.c:466-467`), and `BZ2_bzBuffToBuffDecompress` has written into the caller's
  buffer; here an error gives only the error. This holds for `decompressStream` too.
* Output size: `BZ2_bzBuffToBuffDecompress` writes into a buffer of a given size and fails
  with `BZ_OUTBUFF_FULL` when the output does not fit (`bzlib.c:1343-1345`). Neither function
  here has a limit, so neither has that error; for a buffer filled exactly by a stream that is
  cut off, the C call gives `BZ_OUTBUFF_FULL` where these give `Error.eof` (`bzlib.c:1340`).
* Not modelled: `bzip2 -f`, which at a bad header in any stream rewinds the input and copies
  all of it to the output (`bzip2.c:465`, `bzip2.c:506-517`); I/O errors; `BZ_MEM_ERROR`; the
  `small` mode, which gives the same results.
-/

namespace Bzip2.Oracle

/-- Decompresses the one stream at the start of `input`; returns its output and how many bytes
of `input` the stream occupied. Bytes after the stream are not examined. -/
def decompressStream (input : ByteArray) : Except Error (ByteArray × Nat) :=
  Decompress.Stream.decode input

/-- The streams of `input` from byte `start` on, appended to `out`, the output of the
streams before; `first` says whether the stream at `start` is the first of the input. -/
def decompressFrom (input : ByteArray) (start : Nat) (out : ByteArray) (first : Bool)
    (fuel : Nat) : Except Error ByteArray :=
  match fuel with
  | 0 => .ok out
  | fuel + 1 =>
    match Decompress.Stream.decode input start with
    | .ok (bytes, used) =>
      let out := out ++ bytes
      if start + used ≥ input.size then .ok out
      else decompressFrom input (start + used) out false fuel
    | .error .magic => if first then .error .magic else .ok out
    | .error e => .error e

/-- Decompresses `input` as `bzip2 -d` does: one or more concatenated streams. -/
def decompress (input : ByteArray) : Except Error ByteArray :=
  -- Every stream takes at least one byte, so `input.size + 1` passes are enough.
  decompressFrom input 0 ByteArray.empty true (input.size + 1)

end Bzip2.Oracle
