#!/usr/bin/env python3
"""Require byte-identical exact regression output; do not bless new output."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
expected = json.loads((root / 'research/exterior_cap_expected.json').read_text())
packet = root / 'exterior_cap_offline_packet'
for name, wanted in expected.items():
    content = (packet / name).read_bytes()
    assert len(content) == wanted['bytes'], name + ': byte length changed'
    assert hashlib.sha256(content).hexdigest() == wanted['sha256'], name + ': output changed'
    if 'totals' in wanted:
        assert json.loads(content)['totals'] == wanted['totals'], name + ': totals changed'
print('Both exact regression outputs matched the saved SHA-256 certificates.')
