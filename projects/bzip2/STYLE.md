# bzip2 formalization: style

Hard rules. `tools/verify.sh` checks what a machine can check (the stage is named in brackets);
reviewers check the rest and should not ask for anything beyond these rules and the task.

## Files and names

- One module per part. A module's declarations live in the namespace named after it:
  `spec/Bzip2/Spec/Bwt.lean` declares in `Bzip2.Spec.Bwt`. The exceptions are the oracle's API
  modules (`Oracle/Error.lean`, `Oracle/Decompress.lean`, `Oracle/Compress.lean`), which declare
  in `Bzip2.Oracle`. [style]
- Add your own files; do not edit a file another task owns, and never the root modules
  `Bzip2/Spec.lean`, `Bzip2/Oracle.lean`, `Bzip2/Proofs.lean`. [sources] Import the modules you
  need directly.
- Names follow Mathlib: `lowerCamelCase` for definitions and functions, `UpperCamelCase` for
  types, structures and `Prop`-valued definitions, `snake_case` for theorems, with the
  conclusion first (`decode_encode`, `crc32_eq_spec`). Name things after the C code where one
  exists (`origPtr`, `nInUse`), so the two can be read side by side.
- Every module starts with a module doc (`/-! ... -/`): what it defines, which part of the C
  source it follows, and the edge cases it settles. [style]
- Every definition, structure and inductive has a doc string saying what it is, not how it is
  computed. [lint]

## Claims about the C code

- The vendored source (`upstream/`) is the only authority. Cite it as `` `decompress.c:283` `` or
  `` `bzlib.c:825-847` ``: exactly that form, so the citation can be checked. [sources: the file
  exists and has those lines]
- Before you write a citation, read those lines. A citation says "this is where the code does
  it", not "somewhere around here". Cite the place a value is computed or a check is made, not
  where it is merely read or stored.
- Say which behaviour is whose: `BZ2_bzDecompress`'s (the library's), `BZ2_bzBuffToBuffDecompress`'s
  (a wrapper's) or `bzip2`'s (the program's). They differ, for instance on input that ends
  early.
- Where the task leaves a choice (a type, a representation), make it, and say in the module doc
  what you chose and why.

## Lean

- No `sorry`, `admit` or `axiom`. [sources, build] Proofs rest on `propext`,
  `Classical.choice` and `Quot.sound` only: no `native_decide`. [axioms, style]
- No `set_option maxHeartbeats`, and no linter switched off: make the proof cheaper, or fix
  what the linter reports. [style] The build must be free of warnings in our sources. [style]
- Lines of at most 100 characters, no tabs, no trailing whitespace. [style]
- `spec/` imports Mathlib and other `Bzip2.Spec` modules only; `oracle/` imports Lean core, `Std`
  and other `Bzip2.Oracle` modules only; `proofs/` imports both. [sources]
- Spec definitions are written to be reasoned about: structural recursion on lists, `Option`
  or an error type for failure, no arrays or machine words unless the C arithmetic is the
  point. Oracle definitions are written to run: `ByteArray`, `Array`, `UInt32`, tail
  recursion, no `List` on hot paths.
- Examples in the spec are `example ... := by decide` (or `decide +kernel`), small enough to
  check in seconds. Unit tests of the oracle are `#guard`s in
  `tests/Bzip2/Test/<Part>.lean`. [build]

## Running Lean code

How to check things while you work; reviewers do not hold changes to this section.

- `lean --run`, `#eval` and `#guard` run the interpreter, which is around 50 to 100 times
  slower than compiled code. Keep what you run that way small: inputs of a few kilobytes, a
  few hundred cases, seconds in all. A `#guard` also runs in every build.
- For large blocks (bzip2 allows 900 kB) or timing, run compiled code: `lake build
  bzip2-oracle`, then `.lake/build/bin/bzip2-oracle -z < input` (or `-d`), and the golden
  vectors with `lake test`. Do not time anything under the interpreter.
- A scratch check (outside the repository, e.g. `/tmp/scratch/`) should finish in about a
  minute. If it does not, shrink it; do not rerun it with a longer timeout.
- Randomized cross-checks against a naive reference: a few hundred small cases, and keep the
  naive side naive but small (`n` up to a hundred or so).

## Changes

- A change does one task. Everything it touches is in the task's `paths`; nothing else is
  created, not even temporarily committed (result files, logs, build output). [the fleet's
  scope check]
- `checks/<task>.lean` states what the task must provide: the declarations other tasks will
  import, under these names, and the examples that must hold. `tools/check-task.sh <task>`
  runs it. Do not edit it; if it is wrong, say so in your result's `debug`.
- When your branch is behind `origin/master`, merge it; resolve conflicts minimally and take
  `origin/master`'s version of any file you do not own.
- Commit messages: `<task id>: <what changed>`, one line, then why if it is not obvious.
