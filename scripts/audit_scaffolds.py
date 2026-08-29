#!/usr/bin/env python3
"""Audit explicit Lean axioms and honest vacuous scaffolds.

This script is intentionally syntactic. It does not decide whether a theorem is
mathematically deep or whether an axiom is justified. It gives a reproducible
inventory for the continuing GPPVerify2 axiom/stub-retirement campaign.

Usage:
    python3 scripts/audit_scaffolds.py
    python3 scripts/audit_scaffolds.py --json

It scans GppVerify/**/*.lean and reports, per file:
  * top-level `axiom` declarations;
  * `: True := trivial` scaffolds;
  * `∀ (_ : True), True`-style scaffolds;
  * executable `sorry` / `admit` tokens outside comments (conservative scan).

The text report is ranked by a simple pressure score so dense files rise to the
top. JSON output is suitable for CI artifacts and downstream prioritization.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "GppVerify"

AXIOM_RE = re.compile(r"^\s*axiom\s+([A-Za-z0-9_'.]+)", re.MULTILINE)
TRUE_TRIVIAL_RE = re.compile(
    r"^\s*(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,400}?:\s*True\s*:=\s*trivial\b",
    re.MULTILINE,
)
VACUOUS_FORALL_RE = re.compile(
    r"^\s*(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}?:[\s\S]{0,160}?"
    r"(?:∀|forall)\s*\([^)]*:\s*True\)[^:]{0,120}?True\s*:=\s*(?:by\s+)?trivial\b",
    re.MULTILINE,
)
SORRY_RE = re.compile(r"\b(?:sorry|admit)\b")


@dataclass
class FileAudit:
    path: str
    axioms: list[str]
    true_trivial: list[str]
    vacuous_forall: list[str]
    sorry_or_admit_hits: int

    @property
    def scaffold_count(self) -> int:
        return len(set(self.true_trivial) | set(self.vacuous_forall))

    @property
    def pressure_score(self) -> int:
        # Axioms get extra weight because removing one strengthens every theorem
        # downstream of it. Sorries should normally be zero and rank highest.
        return 10 * self.sorry_or_admit_hits + 4 * len(self.axioms) + self.scaffold_count


def strip_comments(text: str) -> str:
    """Remove Lean line and nested block comments conservatively."""
    out: list[str] = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
        elif text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def audit_file(path: Path) -> FileAudit:
    raw = path.read_text(encoding="utf-8")
    code = strip_comments(raw)
    axioms = AXIOM_RE.findall(code)
    true_trivial = TRUE_TRIVIAL_RE.findall(code)
    vacuous_forall = VACUOUS_FORALL_RE.findall(code)
    sorry_hits = len(SORRY_RE.findall(code))
    return FileAudit(
        path=str(path.relative_to(ROOT)),
        axioms=axioms,
        true_trivial=true_trivial,
        vacuous_forall=vacuous_forall,
        sorry_or_admit_hits=sorry_hits,
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit JSON instead of text")
    args = parser.parse_args()

    audits = [audit_file(p) for p in sorted(LEAN_ROOT.rglob("*.lean"))]
    audits = [
        a
        for a in audits
        if a.axioms or a.scaffold_count or a.sorry_or_admit_hits
    ]
    audits.sort(key=lambda a: (-a.pressure_score, a.path))

    totals = {
        "files_with_findings": len(audits),
        "axioms": sum(len(a.axioms) for a in audits),
        "scaffolds": sum(a.scaffold_count for a in audits),
        "sorry_or_admit_hits": sum(a.sorry_or_admit_hits for a in audits),
    }

    if args.json:
        payload = {
            "totals": totals,
            "files": [
                {**asdict(a), "scaffold_count": a.scaffold_count,
                 "pressure_score": a.pressure_score}
                for a in audits
            ],
        }
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 1 if totals["sorry_or_admit_hits"] else 0

    print("GPPVerify2 axiom/scaffold audit")
    print(
        f"totals: axioms={totals['axioms']} scaffolds={totals['scaffolds']} "
        f"sorry/admit={totals['sorry_or_admit_hits']} "
        f"files={totals['files_with_findings']}"
    )
    print()
    for a in audits:
        print(
            f"[{a.pressure_score:3d}] {a.path}: "
            f"axioms={len(a.axioms)} scaffolds={a.scaffold_count} "
            f"sorry/admit={a.sorry_or_admit_hits}"
        )
        if a.axioms:
            print("      axioms: " + ", ".join(a.axioms))
        scaffolds = sorted(set(a.true_trivial) | set(a.vacuous_forall))
        if scaffolds:
            print("      scaffolds: " + ", ".join(scaffolds))

    return 1 if totals["sorry_or_admit_hits"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
