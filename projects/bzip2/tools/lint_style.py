#!/usr/bin/env python3
"""Source style rules for the Lean files (STYLE.md), beyond what Lean's own linters report.

Per file: lines of at most 100 characters, no tabs, no trailing whitespace, a final newline; a
module doc (`/-! ... -/`); no `set_option maxHeartbeats`, no linter switched off, no
`native_decide`; and declarations in the namespace named after their module
(`Bzip2/Spec/Crc.lean` declares in `Bzip2.Spec.Crc`). Comments and strings do not count for
the forbidden words. Prints every finding as `file:line: message`; exit status 1 if any.

Usage (from projects/bzip2): lint_style.py [FILE...]   (default: every library and test file)
"""

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from lean_holes import code_only  # noqa: E402

SRC_DIRS = ("spec", "oracle", "proofs", "tests", "fuzz")
MAX_LINE = 100
FORBIDDEN = [
    (re.compile(r"\bset_option\s+maxHeartbeats\b"), "set_option maxHeartbeats: make the proof cheaper instead"),
    (re.compile(r"\bset_option\s+linter\.[\w.]+\s+false\b"), "a linter is switched off: fix what it reports"),
    (re.compile(r"\bnative_decide\b"), "native_decide trusts the compiler: use decide, or #guard in a test"),
]
# The oracle's API modules declare in Bzip2.Oracle; executables' roots and tests declare freely.
NAMESPACE_OF = {"oracle/Bzip2/Oracle/Error.lean": "Bzip2.Oracle", "oracle/Bzip2/Oracle/Decompress.lean": "Bzip2.Oracle",
                "oracle/Bzip2/Oracle/Compress.lean": "Bzip2.Oracle"}
FREE = re.compile(r"^(oracle/Bzip2/Cli\.lean|tests/|fuzz/)")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                  r"(def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque)\b")


def module_of(path: str) -> str:
    return ".".join(Path(path).with_suffix("").parts[1:])


def namespace_findings(path: str, code: str) -> list[tuple[int, str]]:
    want = NAMESPACE_OF.get(path, module_of(path))
    stack: list[tuple[str, str]] = []  # (kind, name)
    out = []
    for i, line in enumerate(code.splitlines(), 1):
        if m := re.match(r"^(namespace|section)\b\s*(\S*)", line):
            stack.append((m.group(1), m.group(2)))
        elif re.match(r"^end\b", line):
            if stack:
                stack.pop()
        elif m := DECL.match(line):
            ns = ".".join(n for kind, n in stack if kind == "namespace")
            if not (ns == want or ns.startswith(want + ".")):
                out.append((i, f"{m.group(1)} declared in namespace `{ns or '(root)'}`, not `{want}`"))
    return out


def findings(path: str) -> list[tuple[int, str]]:
    raw = Path(path).read_text(encoding="utf-8")
    out = []
    for i, line in enumerate(raw.split("\n")[:-1] if raw.endswith("\n") else raw.split("\n"), 1):
        if len(line) > MAX_LINE:
            out.append((i, f"line is {len(line)} characters, over {MAX_LINE}"))
        if "\t" in line:
            out.append((i, "tab character"))
        if line != line.rstrip():
            out.append((i, "trailing whitespace"))
    if raw and not raw.endswith("\n"):
        out.append((raw.count("\n") + 1, "no newline at the end of the file"))
    if "/-!" not in raw:
        out.append((1, "no module doc (`/-! ... -/`) saying what the module is and what it follows"))
    code = code_only(raw)
    for pat, msg in FORBIDDEN:
        for m in pat.finditer(code):
            out.append((code.count("\n", 0, m.start()) + 1, msg))
    if not FREE.match(path):
        out += namespace_findings(path, code)
    return sorted(out)


def main() -> int:
    files = sys.argv[1:] or sorted(str(f) for d in SRC_DIRS for f in Path(d).rglob("*.lean"))
    bad = 0
    for f in files:
        for line, msg in findings(f):
            print(f"{f}:{line}: {msg}")
            bad += 1
    print(f"style: {'ok' if not bad else f'{bad} finding(s)'} in {len(files)} files")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
