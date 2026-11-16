#!/bin/sh
# The checks that say a task is done: checks/<task>.lean elaborates (required declarations
# exist under the names other tasks will use, required examples hold). A task's verify runs
# this after verify.sh:   tools/check-task.sh spec/rle1
set -eu
cd "$(dirname "$0")/.."
f="checks/$1.lean"
[ -f "$f" ] || { echo "check-task: no $f"; exit 1; }
if lake env lean "$f"; then
  echo "check-task: $1: ok"
else
  echo "check-task: $1: FAILED (see checks/$1.lean for what the task must provide)"
  exit 1
fi
