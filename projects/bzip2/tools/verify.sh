#!/bin/sh
# The checks every bzip2 formalization task must leave passing; the fleet runs this as the
# task's verify. Works from any directory.
#
#   tools/verify.sh             every stage, in order
#   tools/verify.sh STAGE...    only these (after a failure, rerun the stage that failed)
#
#   packages  the Lake packages: the image's prebuilt copy, or `lake exe cache get` outside it
#   sources   no sorry/admit/axiom, the import rules, untouched root modules, citations that exist
#   build     lake build: everything by glob, unit tests (#guard) included
#   style     STYLE.md's source rules, and no warning from any linter in the build
#   axioms    every declaration rests on propext, Classical.choice and Quot.sound only
#   lint      environment linters: doc strings, unused arguments and haves, tautologies
#   test      lake test: the golden vectors
#
# Each stage ends with a line `verify: STAGE: ok` or `verify: STAGE: FAILED`; quote them when
# you report.
set -eu
cd "$(dirname "$0")/.."
mkdir -p .lake
log=.lake/verify.log
build_log=.lake/verify-build.log

run() {  # run STAGE COMMAND...: the command's output only if it fails
  stage=$1; shift
  if "$@" > "$log" 2>&1; then
    echo "verify: $stage: ok"
  else
    cat "$log"
    echo "verify: $stage: FAILED ($*)"
    exit 1
  fi
}

packages() {
  sh tools/use-image-packages.sh
  if [ -L .lake/packages ]; then echo "verify: packages: ok"; else run packages lake exe cache get; fi
}

sources() {
  run sources sh -c 'tools/check-sources.sh && python3 tools/check_citations.py'
}

build() {
  if ! lake build > "$build_log" 2>&1; then
    cat "$build_log"
    echo "verify: build: FAILED (lake build)"
    exit 1
  fi
  if grep -n "declaration uses 'sorry'" "$build_log"; then
    echo "verify: build: FAILED (sorry)"
    exit 1
  fi
  echo "verify: build: ok"
}

style() {
  [ -f "$build_log" ] || build
  if ! python3 tools/lint_style.py > "$log" 2>&1; then
    cat "$log"
    echo "verify: style: FAILED (tools/lint_style.py)"
    exit 1
  fi
  # Every warning about our own sources, except Lake's notice that Mathlib prefers the module system.
  if grep -E "^warning: (spec|oracle|proofs|tests|fuzz)/" "$build_log" | grep -v "module system" > "$log"; then
    grep -A6 -E "^warning: (spec|oracle|proofs|tests|fuzz)/" "$build_log" | grep -v "module system" | head -200
    echo "verify: style: FAILED ($(wc -l < "$log") linter warning(s) in the build; fix them, do not silence them)"
    exit 1
  fi
  echo "verify: style: ok"
}

axioms() { run axioms python3 tools/lean_audit.py axioms; }
lint() { run lint python3 tools/lean_audit.py lint; }
test_() { run test lake test; tail -3 "$log"; }

[ $# -gt 0 ] || set -- packages sources build style axioms lint test
for stage in "$@"; do
  case "$stage" in
    packages|sources|build|style|axioms|lint) "$stage" ;;
    test) test_ ;;
    *) echo "verify: unknown stage '$stage'"; exit 2 ;;
  esac
done
echo "verify: ok"
