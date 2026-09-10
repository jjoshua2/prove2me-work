#!/usr/bin/env python3
"""Audit complete, possibly line-wrapped #print axioms reports.
Run only after a successful Lean build; use shell set -euo pipefail.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import re

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
REPORT = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.S)
NO_AXIOMS = re.compile(r"'([^']+)' does not depend on any axioms")

def audit(text: str, required: list[str]) -> dict[str, set[str]]:
    if 'sorryAx' in text:
        raise ValueError('log contains sorryAx')
    reports: dict[str, set[str]] = {}
    for name, raw in REPORT.findall(text):
        axioms = {x.strip() for x in raw.split(',') if x.strip()}
        extra = axioms - ALLOWED
        if extra:
            raise ValueError(f'{name}: nonstandard axioms: {sorted(extra)}')
        reports[name] = axioms
    for name in NO_AXIOMS.findall(text):
        reports[name] = set()
    missing = set(required) - reports.keys()
    if missing:
        raise ValueError(f'missing axiom reports: {sorted(missing)}')
    return reports

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('declarations', nargs='+')
    args = parser.parse_args()
    try:
        reports = audit(args.log.read_text(encoding='utf-8'), args.declarations)
    except (OSError, ValueError) as exc:
        parser.exit(1, f'Axiom audit failed: {exc}\n')
    print(f'Axiom audit passed: {len(args.declarations)} required declarations; '
          f'{len(reports)} reports checked; only standard logical axioms.')
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
