# bzip2 formalization: notes for agents (and people)

Everything for this project is under `projects/bzip2/`. Before changing anything, read
"The Lean formalization" in `README.md` and all of `STYLE.md`: they are the rules a change is
reviewed against. `upstream/` is the vendored C source (read it, never edit it), and it decides
every unclear detail; `tools/` and `checks/` are not edited by tasks.

- `tools/verify.sh` runs the checks in named stages; rerun one with `tools/verify.sh build style`.
  `tools/check-task.sh <task>` runs a task's acceptance check (`checks/<task>.lean`).
- `lean --run`, `#eval` and `#guard` are interpreted and slow: small inputs only. For large
  blocks or timing, use the compiled `bzip2-oracle` (`lake build bzip2-oracle`) or `lake test`.
  See "Running Lean code" in `STYLE.md`.
- Keep each scratch check to about a minute, outside the repository; shrink it rather than
  raising its timeout.
