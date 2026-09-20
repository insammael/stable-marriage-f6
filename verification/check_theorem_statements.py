#!/usr/bin/env python3
"""Compare theorem-like LaTeX statement blocks before their proofs."""

from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

KINDS = "theorem|lemma|proposition|corollary|definition"
PATTERN = re.compile(
    rf"\\begin\{{(?P<kind>{KINDS})\}}(?P<body>.*?)(?=\\begin\{{proof\}})",
    re.DOTALL,
)


def statements(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    return [match.group(0).strip() for match in PATTERN.finditer(text)]


def digest(items: list[str]) -> str:
    return hashlib.sha256("\n\n".join(items).encode()).hexdigest()


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: check_theorem_statements.py BASELINE CANDIDATE", file=sys.stderr)
        return 2
    baseline = statements(Path(sys.argv[1]))
    candidate = statements(Path(sys.argv[2]))
    print(f"baseline_statements={len(baseline)}")
    print(f"candidate_statements={len(candidate)}")
    print(f"baseline_sha256={digest(baseline)}")
    print(f"candidate_sha256={digest(candidate)}")
    if baseline != candidate:
        print("THEOREM_STATEMENT_DIFF=FAIL")
        return 1
    print("THEOREM_STATEMENT_DIFF=PASS_IDENTICAL")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
