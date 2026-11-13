#!/usr/bin/env python3
"""Check that projects/bzip2/docs covers the whole external surface of bzip2.

The surface is derived from the vendored source, not from a hand-written list:

* public functions:  every `BZ_API(<name>)` declaration in upstream/bzlib.h
* exported symbols:  every global symbol defined in libbz2's object files (`nm`), which
                     includes internal functions and tables that are linkable but not in the
                     header; functions go in "functions", data in "data"
* macros:            every `BZ_*` macro bzlib.h defines or tests (#ifdef/#ifndef/defined())
* types:             bz_stream and BZFILE
* programs:          everything `make install` puts in $(PREFIX)/bin

Both docs/surface-area.json (machine-readable) and docs/surface-area.md (prose) must cover
all of it. Prints every gap and exits 1, or prints a summary and exits 0.

Usage: python3 projects/bzip2/tools/check_surface.py [--only-docs [BASE]]

With --only-docs, also fail if the branch changes anything outside projects/bzip2/docs/
relative to BASE (default origin/master), including uncommitted and untracked files.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PROJECT = Path(__file__).resolve().parent.parent
UPSTREAM = PROJECT / "upstream"
DOCS = PROJECT / "docs"
LIB_SOURCES = ["blocksort", "huffman", "crctable", "randtable", "compress", "decompress", "bzlib"]
TYPES = ["bz_stream", "BZFILE"]
FUNCTION_FIELDS = ["name", "signature", "public", "summary", "parameters", "returns"]


def public_functions(header: str) -> list[str]:
    return re.findall(r"^BZ_EXTERN\b[^;#]*?BZ_API\((\w+)\)", header, flags=re.M)


def macros(header: str) -> list[str]:
    found = re.findall(r"^\s*#\s*define\s+(BZ_\w+)", header, flags=re.M)
    found += re.findall(r"^\s*#\s*if(?:n?def)?\s+(BZ_\w+)", header, flags=re.M)
    found += re.findall(r"defined\s*\(?\s*(BZ_\w+)", header)
    return sorted(set(found))


def programs(makefile: str) -> list[str]:
    return sorted(set(re.findall(r"\$\(PREFIX\)/bin/([A-Za-z0-9_]+)", makefile)))


def exported_symbols() -> dict[str, str]:
    """name -> "function" | "data"."""
    cc = shutil.which("cc") or shutil.which("gcc") or shutil.which("clang")
    nm = shutil.which("nm")
    if not cc or not nm:
        sys.exit("check_surface: needs a C compiler (cc) and nm on PATH")
    with tempfile.TemporaryDirectory() as tmp:  # never build inside the repository
        objs = []
        for name in LIB_SOURCES:
            obj = Path(tmp) / f"{name}.o"
            p = subprocess.run([cc, "-c", "-O0", "-w", "-I", str(UPSTREAM), str(UPSTREAM / f"{name}.c"),
                                "-o", str(obj)], capture_output=True, text=True)
            if p.returncode != 0:
                sys.exit(f"check_surface: compiling {name}.c failed:\n{p.stderr}")
            objs.append(str(obj))
        out = subprocess.run([nm, "-g", "--defined-only", *objs], capture_output=True, text=True,
                             check=True).stdout
    syms = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] in "TDRBCGS":
            syms[parts[2]] = "function" if parts[1] == "T" else "data"
    return dict(sorted(syms.items()))


def entries(doc: dict, key: str) -> dict[str, dict]:
    items = doc.get(key)
    if not isinstance(items, list):
        return {}
    return {e["name"]: e for e in items if isinstance(e, dict) and isinstance(e.get("name"), str)}


def outside_docs(base: str) -> list[str]:
    root = PROJECT.parent.parent
    git = ["git", "-C", str(root)]
    mb = subprocess.run([*git, "merge-base", "HEAD", base], capture_output=True, text=True)
    if mb.returncode != 0:
        return [f"--only-docs: cannot find the merge base with {base}: {mb.stderr.strip()}"]
    changed = subprocess.run([*git, "diff", "--name-only", mb.stdout.strip()], capture_output=True, text=True,
                             check=True).stdout.split()
    changed += subprocess.run([*git, "ls-files", "--others", "--exclude-standard"], capture_output=True,
                              text=True, check=True).stdout.split()
    docs = DOCS.relative_to(root).as_posix() + "/"
    return [f"changes outside {docs}: {p}" for p in sorted(set(changed)) if not p.startswith(docs)]


def main() -> int:
    header = (UPSTREAM / "bzlib.h").read_text()
    public = public_functions(header)
    exported = exported_symbols()
    want_macros = macros(header)
    want_programs = programs((UPSTREAM / "Makefile").read_text())
    gaps: list[str] = []

    jpath, mpath = DOCS / "surface-area.json", DOCS / "surface-area.md"
    doc: dict = {}
    if not jpath.exists():
        gaps.append(f"missing {jpath.relative_to(PROJECT.parent.parent)}")
    else:
        try:
            doc = json.loads(jpath.read_text())
        except json.JSONDecodeError as e:
            gaps.append(f"{jpath.name} is not valid JSON: {e}")
    md = mpath.read_text() if mpath.exists() else ""
    if not md:
        gaps.append(f"missing or empty {mpath.relative_to(PROJECT.parent.parent)}")

    funcs = entries(doc, "functions")
    data = entries(doc, "data")
    for name in sorted(set(public) | {s for s, k in exported.items() if k == "function"}):
        is_public = name in public
        e = funcs.get(name)
        if e is None:
            gaps.append(f"functions: no entry for {name} ({'public' if is_public else 'exported, not in bzlib.h'})")
            continue
        for f in FUNCTION_FIELDS:
            if f not in e or e[f] in ("", None):
                gaps.append(f"functions: {name}: missing field '{f}'")
        if e.get("public") is not None and e.get("public") != is_public:
            gaps.append(f"functions: {name}: 'public' should be {str(is_public).lower()}")
    for name in (s for s, k in exported.items() if k == "data"):
        if name not in data:
            gaps.append(f"data: no entry for {name} (exported, not in bzlib.h)")
        elif not data[name].get("summary"):
            gaps.append(f"data: {name}: missing field 'summary'")
    for key, wanted in (("macros", want_macros), ("types", TYPES), ("programs", want_programs)):
        have = entries(doc, key)
        for name in wanted:
            if name not in have:
                gaps.append(f"{key}: no entry for {name}")
            elif not have[name].get("summary"):
                gaps.append(f"{key}: {name}: missing field 'summary'")

    for name in sorted(set(public) | set(want_macros) | set(TYPES) | set(want_programs)):
        if md and not re.search(rf"(?<![A-Za-z0-9_]){re.escape(name)}(?![A-Za-z0-9_])", md):
            gaps.append(f"surface-area.md never mentions {name}")

    if "--only-docs" in sys.argv:
        i = sys.argv.index("--only-docs")
        base = sys.argv[i + 1] if len(sys.argv) > i + 1 else "origin/master"
        gaps += outside_docs(base)

    if gaps:
        print(f"check_surface: {len(gaps)} gap(s) in the bzip2 surface documentation:")
        for g in gaps:
            print(f"  - {g}")
        return 1
    print(f"check_surface: ok: {len(public)} public functions, {len(exported)} exported symbols, "
          f"{len(want_macros)} macros, {len(TYPES)} types, {len(want_programs)} programs documented")
    return 0


if __name__ == "__main__":
    sys.exit(main())
