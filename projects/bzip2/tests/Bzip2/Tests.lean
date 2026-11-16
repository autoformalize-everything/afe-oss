import Bzip2.Oracle

/-!
`lake test`: runs the oracle on the golden vectors in `tests/vectors` (format: see
`tests/vectors/README.md`).

* `decompress/<case>`: `Oracle.decompress input` must equal `expected`, or fail with the error
  class named in `error`.
* `compress/<case>`: for levels 1 and 9, `Oracle.compress` must succeed, and its output must
  decompress to `input` both through the oracle and through the vendored `bzip2 -d`.

A check whose oracle function returns `Error.unimplemented` is skipped, not failed. Any other
mismatch fails; the exit status is non-zero iff something failed.

Run from the project root (as `lake test` does), or set `BZIP2_VECTORS` to the vectors directory.
The vendored bzip2 comes from `tests/vectors/build-bzip2.sh` (built out of tree, on first use).
-/

open Bzip2.Oracle

inductive Outcome where
  | pass
  | skip (why : String)
  | fail (why : String)

structure Counts where
  passed : Nat := 0
  skipped : Nat := 0
  failed : Nat := 0

def errorClass : Error → String
  | .magic => "magic"
  | .data _ => "data"
  | .eof => "eof"
  | .param _ => "param"
  | .unimplemented _ => "unimplemented"

def isUnimplemented : Error → Bool
  | .unimplemented _ => true
  | _ => false

/-- The oracle's `decompress` against a case directory. -/
def checkDecompress (dir : System.FilePath) : IO Outcome := do
  let input ← IO.FS.readBinFile (dir / "input")
  let result := decompress input
  if let .error e := result then
    if isUnimplemented e then return .skip "decompress unimplemented"
  if ← (dir / "expected").pathExists then
    let expected ← IO.FS.readBinFile (dir / "expected")
    match result with
    | .ok out =>
      if out == expected then return .pass
      else return .fail s!"output differs ({out.size} bytes, expected {expected.size})"
    | .error e => return .fail s!"expected success, got error {errorClass e}"
  else
    let cls := (← IO.FS.readFile (dir / "error")).trimAscii.toString
    match result with
    | .ok out => return .fail s!"expected error {cls}, got ok ({out.size} bytes)"
    | .error e =>
      if errorClass e == cls then return .pass
      else return .fail s!"expected error {cls}, got {errorClass e}"

/-- Path of the vendored `bzip2` binary, building it out of tree if needed. -/
def vendoredBzip2 (vectors : System.FilePath) : IO System.FilePath := do
  let out ← IO.Process.output
    { cmd := "sh", args := #[(vectors / "build-bzip2.sh").toString] }
  if out.exitCode != 0 then
    throw <| IO.userError s!"building the vendored bzip2 failed: {out.stderr}"
  return (System.FilePath.mk out.stdout.trimAscii.toString) / "bzip2"

/-- `bzip2 -dc` of `data`, through a temporary file. -/
def vendoredDecompress (bzip2 : System.FilePath) (data : ByteArray) :
    IO (Except String ByteArray) := do
  let (h, path) ← IO.FS.createTempFile
  h.write data
  h.flush
  let child ← IO.Process.spawn
    { cmd := bzip2.toString, args := #["-dc", "--", path.toString]
      stdout := .piped, stderr := .piped }
  let out ← child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  IO.FS.removeFile path
  return if code == 0 then .ok out else .error s!"bzip2 -d exited {code}: {err.trimAscii}"

/-- Roundtrip of one level through the oracle and the vendored bzip2. -/
def checkCompress (vectors : System.FilePath) (input : ByteArray) (level : Nat) : IO Outcome := do
  match compress level input with
  | .error e =>
    if isUnimplemented e then return .skip "compress unimplemented"
    else return .fail s!"level {level}: compress failed with {errorClass e}"
  | .ok z =>
    match decompress z with
    | .error e =>
      if !isUnimplemented e then
        return .fail s!"level {level}: oracle cannot decompress its own output: {errorClass e}"
    | .ok back =>
      if back != input then return .fail s!"level {level}: oracle roundtrip differs"
    match ← vendoredDecompress (← vendoredBzip2 vectors) z with
    | .error msg => return .fail s!"level {level}: {msg}"
    | .ok back =>
      if back == input then return .pass
      else return .fail s!"level {level}: vendored bzip2 -d output differs"

def caseDirs (dir : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← dir.readDir
  let names : Array String := entries.map (·.fileName) |>.qsort (· < ·)
  return names.map fun (n : String) => dir / n

def report (counts : Counts) (name : String) : Outcome → IO Counts
  | .pass => do
    IO.println s!"PASS {name}"
    return { counts with passed := counts.passed + 1 }
  | .skip why => do
    IO.println s!"SKIP {name}: {why}"
    return { counts with skipped := counts.skipped + 1 }
  | .fail why => do
    IO.println s!"FAIL {name}: {why}"
    return { counts with failed := counts.failed + 1 }

def main : IO UInt32 := do
  let vectors : System.FilePath :=
    System.FilePath.mk ((← IO.getEnv "BZIP2_VECTORS").getD "tests/vectors")
  let mut counts : Counts := {}
  for dir in ← caseDirs (vectors / "decompress") do
    let name := s!"decompress/{dir.fileName.getD ""}"
    counts ← report counts name (← checkDecompress dir)
  for dir in ← caseDirs (vectors / "compress") do
    let input ← IO.FS.readBinFile (dir / "input")
    for level in [1, 9] do
      let name := s!"compress/{dir.fileName.getD ""}/level{level}"
      counts ← report counts name (← checkCompress vectors input level)
  IO.println s!"bzip2-tests: {counts.passed} passed, {counts.skipped} skipped, {counts.failed} failed"
  return if counts.failed == 0 then 0 else 1
