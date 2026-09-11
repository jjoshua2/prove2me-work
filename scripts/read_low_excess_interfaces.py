#!/usr/bin/env python3
"""Read exact already-Proved dependency types; no platform writes or Lean runs."""
import json
import os
import types
from pathlib import Path
from publish_affine_diameter_transport import read_blob, CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB

OUT = Path('low_excess_interfaces')
TARGETS = {
    'facet_reduction': '11b3500a-b9f8-4b44-94aa-d71354441ddb',
    'subbalanced_sections': '0e4f233c-418a-4884-bbfb-dbfc7f76bc76',
    'dimension_three': 'cf588038-4ee8-4c90-b034-348c28d0da21',
    'common_face_transport': 'd7b5f979-eb85-47c4-8c1d-a53aff0bccbe',
}
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'


def main():
    key = os.environ.get('PROVE2ME_API_KEY', '').strip()
    if not key:
        raise RuntimeError('Prove2Me credential absent')
    text = read_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB).decode()
    client = types.ModuleType('reviewed_low_excess_read_client')
    exec(compile(text, CLIENT_PATH, 'exec'), client.__dict__)
    client.VERSION = '0.10.1'
    api = client.API(key)
    OUT.mkdir(exist_ok=True)
    for label, tid in TARGETS.items():
        theorem = api.request('/theorems/' + tid)
        if theorem.get('status') != 'Proved' or theorem.get('mathlib_rev') != PIN:
            raise RuntimeError('Dependency no longer Proved on the expected pin: ' + label)
        (OUT / (label + '.json')).write_text(json.dumps(theorem, indent=2) + '\n')
        fields = {k: theorem.get(k) for k in ['theorem_id', 'theorem_name', 'status', 'mathlib_rev', 'preamble', 'formal_statement']}
        print('\nDEPENDENCY ' + label + '\n' + json.dumps(fields, ensure_ascii=False, indent=2), flush=True)
    query = '/theorems?env=' + PIN + '&q=low_excess&limit=100&offset=0'
    existing = api.request(query)
    (OUT / 'existing-low-excess.json').write_text(json.dumps(existing, indent=2) + '\n')
    print('EXISTING_LOW_EXCESS ' + json.dumps(existing, ensure_ascii=False), flush=True)
    print('READ_ONLY_COMPLETE', flush=True)


if __name__ == '__main__':
    main()
