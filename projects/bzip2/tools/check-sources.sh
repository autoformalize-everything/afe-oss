#!/bin/sh
# Source rules lake build cannot check. Works from any directory.
set -eu
cd "$(dirname "$0")/.."
fail=0
lean_files() { find "$@" -name '*.lean' 2>/dev/null; }

# No proof holes or new axioms (comments and strings ignored).
holes=$(lean_files spec oracle proofs tests fuzz | xargs -r python3 tools/lean_holes.py || true)
[ -z "$holes" ] || { echo "sorry/admit/axiom:"; echo "$holes"; fail=1; }

# The oracle stays independent of Mathlib and the spec; the spec of the oracle.
bad=$(lean_files oracle | xargs -r grep -nE '^import\s+(Mathlib|Bzip2\.Spec|Bzip2\.Proofs)' || true)
[ -z "$bad" ] || { echo "the oracle imports Mathlib, the spec or the proofs:"; echo "$bad"; fail=1; }
bad=$(lean_files spec | xargs -r grep -nE '^import\s+Bzip2\.(Oracle|Proofs|Cli)' || true)
[ -z "$bad" ] || { echo "the spec imports the oracle or the proofs:"; echo "$bad"; fail=1; }

exit $fail
