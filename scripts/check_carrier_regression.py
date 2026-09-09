#!/usr/bin/env python3
"""Check the complete exact output against the independently executed receipt."""
from pathlib import Path
import hashlib
import json
import sys

if len(sys.argv) != 2:
    raise SystemExit('usage: python3 scripts/check_carrier_regression.py OUTPUT.json')
path = Path(sys.argv[1])
expected = json.loads(Path('research/cone_carrier_expected.json').read_text())
raw = path.read_bytes()
actual = json.loads(raw)
if hashlib.sha256(raw).hexdigest() != expected['sha256']:
    raise SystemExit('FAIL: full deterministic output hash differs')
if actual['totals'] != expected['totals'] or actual['strict_apex_obstruction'] != expected['strict_apex_obstruction']:
    raise SystemExit('FAIL: expected coverage differs')
print('Exact carrier regression matched byte-for-byte:', actual['totals'])
print('Five apex-removal obstructions verified; this is not a Lean hull proof.')
