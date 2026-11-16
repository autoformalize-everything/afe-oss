import Bzip2.Oracle

/-!
`bzip2-oracle`: the oracle as a filter from standard input to standard output.

    bzip2-oracle -z [-1 .. -9]    compress (default -9)
    bzip2-oracle -d               decompress (concatenated streams)

Exit status as bzip2's: 0 success, 1 usage error, 2 corrupt or truncated input,
3 internal error (including a part not implemented yet).
-/

open Bzip2.Oracle

partial def readAll (stream : IO.FS.Stream) (acc : ByteArray := .empty) : IO ByteArray := do
  let chunk ← stream.read 65536
  if chunk.isEmpty then return acc else readAll stream (acc ++ chunk)

def usage : String := "usage: bzip2-oracle (-z [-1..-9] | -d) < input > output\n"

def errorExit (e : Error) : IO UInt32 := do
  let (msg, code) : String × UInt32 := match e with
    | .magic => ("not a bzip2 stream", 2)
    | .data d => (s!"data integrity error: {d}", 2)
    | .eof => ("compressed input ended unexpectedly", 2)
    | .param d => (s!"bad parameter: {d}", 1)
    | .unimplemented w => (s!"not implemented: {w}", 3)
  IO.eprintln s!"bzip2-oracle: {msg}"
  return code

def run (decompressing : Bool) (level : Nat) : IO UInt32 := do
  let input ← readAll (← IO.getStdin)
  let result := if decompressing then decompress input else compress level input
  match result with
  | .ok out =>
    let stdout ← IO.getStdout
    stdout.write out
    stdout.flush
    return 0
  | .error e => errorExit e

def main (args : List String) : IO UInt32 := do
  match args with
  | ["-d"] => run true 0
  | ["-z"] => run false 9
  | ["-z", l] | [l, "-z"] =>
    match l.toList with
    | ['-', c] =>
      if '1' ≤ c ∧ c ≤ '9' then run false (c.toNat - '0'.toNat)
      else IO.eprint usage; return 1
    | _ => IO.eprint usage; return 1
  | _ => IO.eprint usage; return 1
