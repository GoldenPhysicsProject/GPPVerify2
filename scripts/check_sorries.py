#!/usr/bin/env python3
"""Fail if any Lean source in GppVerify/ contains a live sorry/sorryAx token.

This complements Lean build-log diagnostics. Cached Lake modules may emit no warning,
so a whole-tree invariant must inspect the source tree directly. Comments and string
literals are stripped before token matching to avoid doc/test false positives.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

SORRY = re.compile(r"(?<![A-Za-z0-9_.])sorry(?:Ax)?(?![A-Za-z0-9_'])")
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def strip_comments(src: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    n = len(src)
    while i < n:
        if depth == 0 and i + 1 < n and src[i:i+2] == "--":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if i + 1 < n and src[i:i+2] == "/-":
            depth += 1
            out.extend("  ")
            i += 2
            continue
        if depth > 0 and i + 1 < n and src[i:i+2] == "-/":
            depth -= 1
            out.extend("  ")
            i += 2
            continue
        ch = src[i]
        if depth > 0:
            out.append("\n" if ch == "\n" else " ")
        else:
            out.append(ch)
        i += 1
    return "".join(out)


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    root = repo / "GppVerify"
    hits: list[str] = []
    for path in sorted(root.rglob("*.lean")):
        src = strip_comments(path.read_text())
        src = STRING.sub(lambda m: " " * len(m.group(0)), src)
        for lineno, line in enumerate(src.splitlines(), start=1):
            if SORRY.search(line):
                hits.append(f"{path.relative_to(repo)}:{lineno}: {line.strip()[:100]}")
    if hits:
        print(f"::error::{len(hits)} live sorry token(s) in GppVerify/.")
        for hit in hits:
            print(f"  {hit}")
        return 1
    print("No live sorry tokens in GppVerify/ (source-level, cache-independent).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
