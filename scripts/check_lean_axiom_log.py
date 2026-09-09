#!/usr/bin/env python3
"""Audit complete, possibly line-wrapped #print axioms reports."""
from __future__ import annotations
import argparse
from pathlib import Path
import re

ALLOWED=frozenset({'propext','Classical.choice','Quot.sound'})
REPORT=re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",re.S)
NO_AXIOMS=re.compile(r"'([^']+)' does not depend on any axioms")

def audit(text:str, required:list[str]):
    if 'sorryAx' in text: raise ValueError('log contains sorryAx')
    reports={}
    for name,raw in REPORT.findall(text):
        axioms={x.strip() for x in raw.split(',') if x.strip()}
        extra=axioms-ALLOWED
        if extra: raise ValueError(f'{name}: nonstandard axioms: {sorted(extra)}')
        reports[name]=axioms
    for name in NO_AXIOMS.findall(text): reports[name]=set()
    missing=set(required)-reports.keys()
    if missing: raise ValueError(f'missing axiom reports: {sorted(missing)}')
    return reports

def main():
    p=argparse.ArgumentParser(); p.add_argument('log',type=Path); p.add_argument('declarations',nargs='+'); a=p.parse_args()
    try: reports=audit(a.log.read_text(encoding='utf-8'),a.declarations)
    except (OSError,ValueError) as e: p.exit(1,f'Axiom audit failed: {e}\n')
    print(f'Axiom audit passed: {len(a.declarations)} required declarations; {len(reports)} reports checked; only standard logical axioms.')
    return 0
if __name__=='__main__': raise SystemExit(main())
