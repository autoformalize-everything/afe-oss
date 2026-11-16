"""Prints every `sorry`, `admit` or `axiom` declaration in the given Lean files, ignoring
comments (line, block, nested, doc) and string literals. Exit status 1 if there is any."""

import re
import sys


def code_only(text: str) -> str:
    """The text with comments and string literals blanked out, line structure kept."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        c, two = text[i], text[i:i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if two == "/-":
            depth, i = 1, i + 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            out.append('""')
        else:
            out.append(c)
            i += 1
    return "".join(out)


PATTERN = re.compile(r"(?<![\w.'])(sorry|admit)(?![\w'])|^\s*(?:private\s+|protected\s+)?axiom\b", re.M)
found = 0
for path in sys.argv[1:]:
    code = code_only(open(path, encoding="utf-8").read())
    for m in PATTERN.finditer(code):
        line = code.count("\n", 0, m.start()) + 1
        print(f"{path}:{line}: {m.group(0).strip()}")
        found += 1
sys.exit(1 if found else 0)
