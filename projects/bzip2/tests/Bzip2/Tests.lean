import Bzip2.Oracle

/-!
`lake test`: runs the oracle on the golden vectors in `tests/vectors`.

No vectors exist yet; the `bzip2/tests/golden` task adds them and the runner. Until then this
only checks that the oracle's API links.
-/

open Bzip2.Oracle

def main : IO UInt32 := do
  match decompress .empty with
  | .error _ => pure ()
  | .ok _ => pure ()
  IO.println "bzip2-tests: no golden vectors yet"
  return 0
