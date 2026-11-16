#!/usr/bin/env python3
"""Whole-project Lean audits that need every library module loaded at once.

    lean_audit.py axioms    every declaration in Bzip2.* depends only on the allowed axioms
                            (propext, Classical.choice, Quot.sound): no sorryAx, no native_decide
    lean_audit.py lint      Batteries' environment linters on Bzip2.*: missing doc strings,
                            unused arguments and `have`s, syntactic tautologies

Writes a Lean file importing all library modules (everything Lake builds by glob; not the
executables' roots) under .lake/audit/ and runs it with `lake env lean`. Run from projects/bzip2
after `lake build`.
"""

import subprocess
import sys
from pathlib import Path

LIBS = {"spec": "Bzip2/Spec", "oracle": "Bzip2/Oracle", "proofs": "Bzip2/Proofs", "tests": "Bzip2/Test"}

AXIOMS = """
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ours := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some idx => if (`Bzip2).isPrefixOf env.header.moduleNames[idx.toNat]! then acc.push n else acc
    | none => acc
  let mut bad : Array String := #[]
  for n in ours do
    let extra := (← collectAxioms n).filter (!allowed.contains ·)
    if !extra.isEmpty && !n.isInternal then
      bad := bad.push s!"{n}: {extra.toList}"
  if bad.isEmpty then
    logInfo m!"axioms: ok ({ours.size} declarations use only {allowed})"
  else
    throwError "axioms: declarations depending on axioms outside {allowed}:\\n{String.intercalate "\\n" bad.toList}"
"""

LINT = """
#lint only docBlame unusedArguments unusedHavesSuffices synTaut in Bzip2
"""


def modules() -> list[str]:
    out = []
    for src, sub in LIBS.items():
        base = Path(src)
        for f in sorted((base / sub).rglob("*.lean")) + ([base / f"{sub}.lean"] if (base / f"{sub}.lean").exists() else []):
            out.append(".".join(f.relative_to(base).with_suffix("").parts))
    return sorted(set(out))


def main() -> int:
    kind = sys.argv[1] if len(sys.argv) > 1 else ""
    if kind not in ("axioms", "lint"):
        print(__doc__)
        return 2
    imports = "".join(f"import {m}\n" for m in modules())
    head = "import Lean\n" if kind == "axioms" else "import Batteries.Tactic.Lint\n"
    out = Path(".lake/audit")
    out.mkdir(parents=True, exist_ok=True)
    path = out / f"{kind.capitalize()}.lean"
    path.write_text(head + imports + (AXIOMS if kind == "axioms" else LINT))
    p = subprocess.run(["lake", "env", "lean", str(path)], capture_output=True, text=True)
    sys.stdout.write(p.stdout + p.stderr)
    return p.returncode


if __name__ == "__main__":
    sys.exit(main())
