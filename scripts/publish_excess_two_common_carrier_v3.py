#!/usr/bin/env python3
"""Retry the audited excess-two carrier proof with a root-level `solution`.

The first server submission used `namespace Hirsch; theorem solution`, while the
Prove2Me verifier expects the submitted declaration to be named exactly
`solution` at the root.  This changes only that wrapper shape.  It reuses the
same registered theorem and the same kernel-audited compact driver.
"""
from __future__ import annotations

import argparse
import publish_excess_two_common_carrier as p

p.SOURCE = 'd85e9ff15194bd413c5f7e71e6f1f10e2b98697c'
p.DRIVER_BLOB = 'ef4aadf8672a49d399238a1c80c306111a0afc23'


def root_solution() -> bytes:
    imports = '\n'.join(
        'import Theorems.Thm_' + name.replace('.', '_') for name in p.DEPENDENCIES
    )
    wrapper = '''

theorem solution
''' + p.BINDERS + ''' := by
  exact HirschExcessTwoPublic.excess_two_common_carrier_from_proved_inputs
    Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three
    Hirsch.common_face_diamLE_of_coord_diamLE
    a b u v hbd hu hrows
'''
    return (imports + '\n' + p.driver_body() + wrapper).encode('utf-8')


p.expected_solution = root_solution

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode', choices=['prepare', 'publish'])
    args = ap.parse_args()
    p.prepare() if args.mode == 'prepare' else p.publish()
