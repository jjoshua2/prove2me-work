#!/usr/bin/env python3
"""Publish the audited arbitrary-checkpoint excess-two common-carrier theorem.

The local compact driver treats the two public Prove2Me results as explicit
premises. The submitted solution replaces only those premises by tracked imports
of the exact already-Proved theorems after authenticated statement/status/pin
checks. No Open theorem is imported and no sketch/decomposition is created.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import types
from pathlib import Path

from publish_affine_diameter_transport import (
    read_blob, CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB,
)

SOURCE = '4f10bdf6feca34d6a41deab32d84a18a61a82be4'
DRIVER_PATH = 'Solutions/PolynomialExcessTwoCarrierPublicDriver.lean'
DRIVER_BLOB = 'd11c2bc195810e85662fdec5de82f00d7d829055'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
PACKET = Path('/tmp/excess-two-common-carrier-public')
OUT = Path('excess_two_common_carrier_publication_receipts')
NAME = 'Hirsch.common_face_diameter_two_of_rows_le_dim_add_two'
TITLE = 'Every common carrier has diameter two at ambient row excess at most two'
PREAMBLE = (
    'import Mathlib\n'
    'import Definitions.Def_Hirsch_model\n'
    'import Definitions.Def_Hirsch_common_face_geometry\n'
    'open scoped RealInnerProductSpace InnerProduct\n'
    'open Set Hirsch'
)
BINDERS = '''    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b) (hrows : n ≤ d + 2) :
    DiamLE (HirschCommonFace.commonFace a b u v) 2'''
FORMAL = (
    'namespace Hirsch\n'
    'theorem common_face_diameter_two_of_rows_le_dim_add_two\n' + BINDERS +
    ' := by sorry\nend Hirsch'
)
NATURAL = '''Let P={x in R^d : <a_i,x> <= b_i for i=1,...,n} be bounded and let u be any feasible point of P. If n<=d+2, then for every point v (not necessarily feasible or a vertex), the face of P cut out by all nonzero describing rows that are tight at both u and v has intrinsic padded vertex-edge graph diameter at most 2. Empty or lower-dimensional carriers, redundant rows, and zero-normal tautologies are allowed. The result is a low-excess carrier theorem, not a statement that arbitrary Polynomial Hirsch carriers have row excess at most two.'''
EXPLANATION = '''## Structure

Let C be the nonzero rows active at both checkpoints and W their common kernel. The canonical common-face coordinates have dimension h=dim W. Rows from C restrict to zero. Among all original rows, the number whose restricted coordinate normal is nonzero is at most n-d+h: rank-nullity gives rank(C) = d-h up to redundant rows, and those common rows are disjoint from the rows that remain effective. Hence n<=d+2 leaves at most h+2 effective coordinate inequalities.

Delete every zero restricted row. Feasibility of u makes every deleted zero-normal inequality a tautology, so the resulting h-dimensional H-presentation is exactly equivalent to the full common-face coordinate polyhedron. Parent boundedness implies boundedness of this coordinate polyhedron because the common-face lift is an isometry and its affine image lies in P.

The already-Proved small-excess theorem `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three` gives a graph walk of length m-h<=2 in the reduced coordinate presentation. Pad it to length two, identify it with the full coordinate presentation, and use the already-Proved `Hirsch.common_face_diamLE_of_coord_diamLE` to transport the actual vertex-edge walk to the intrinsic common carrier.

The source driver proves all row counting, deletion, boundedness, and padding with the two public inputs represented only as explicit logical premises. The submitted proof replaces those premises by tracked imports of their exact Prove2Me-Proved statements. No Open theorem, conjectural child, or circuit-to-edge refinement assumption is used.'''

DEPENDENCIES = {
    'Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three': {
        'id': '12426807-9602-4014-bd5e-c69fb43f4cb6',
        'formal': '''namespace Hirsch
 theorem hpoly_diameter_le_excess_of_rows_le_dim_add_three
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + 3) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by sorry
end Hirsch''',
    },
    'Hirsch.common_face_diamLE_of_coord_diamLE': {
        'id': 'd7b5f979-eb85-47c4-8c1d-a53aff0bccbe',
        'formal': '''namespace Hirsch

theorem common_face_diamLE_of_coord_diamLE
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hcoord : DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x)) B) :
    DiamLE (HirschCommonFace.commonFace a b u x) B := by sorry

end Hirsch''',
    },
}


def driver_bytes() -> bytes:
    return read_blob(SOURCE, DRIVER_PATH, DRIVER_BLOB)


def driver_body() -> str:
    text = driver_bytes().decode('utf-8')
    rows=[]
    for line in text.splitlines():
        if line.strip().startswith('import '):
            continue
        if line.strip().startswith('#print axioms '):
            continue
        rows.append(line)
    return '\n'.join(rows) + '\n'


def expected_solution() -> bytes:
    imports = '\n'.join(
        'import Theorems.Thm_' + name.replace('.', '_') for name in DEPENDENCIES
    )
    wrapper = '''
namespace Hirsch

theorem solution
''' + BINDERS + ''' := by
  exact HirschExcessTwoPublic.excess_two_common_carrier_from_proved_inputs
    Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three
    Hirsch.common_face_diamLE_of_coord_diamLE
    a b u v hbd hu hrows

end Hirsch
'''
    return (imports + '\n' + driver_body() + wrapper).encode('utf-8')


def prepare() -> None:
    driver = driver_bytes()
    solution = expected_solution()
    PACKET.mkdir(parents=True, exist_ok=True)
    (PACKET / 'driver.lean').write_bytes(driver)
    (PACKET / 'solution.lean').write_bytes(solution)
    manifest={
        'source_commit': SOURCE,
        'driver_path': DRIVER_PATH,
        'driver_git_blob': DRIVER_BLOB,
        'driver_sha256': hashlib.sha256(driver).hexdigest(),
        'solution_sha256': hashlib.sha256(solution).hexdigest(),
        'target': NAME,
        'dependencies': {k:v['id'] for k,v in DEPENDENCIES.items()},
        'evidence_boundary': 'driver is locally kernel/axiom audited; unconditional tracked composition is verified by Prove2Me',
    }
    (PACKET / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2), flush=True)


def publish() -> None:
    driver = driver_bytes()
    solution = expected_solution()
    for name, expected in [('driver.lean', driver), ('solution.lean', solution)]:
        p=PACKET / name
        if not p.is_file() or p.read_bytes()!=expected:
            raise RuntimeError('frozen packet mismatch: '+name)
    audit=PACKET/'driver-audit-passed.sha256'
    dh=hashlib.sha256(driver).hexdigest()
    if not audit.is_file() or audit.read_text().strip()!=dh:
        raise RuntimeError('compact driver kernel/axiom audit receipt missing')
    text=read_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB).decode('utf-8')
    slot='"Normalized two-moment slices have graph diameter at most two"'
    if text.count(slot)!=1:
        raise RuntimeError('reviewed client title slot changed')
    client=types.ModuleType('reviewed_excess_two_carrier_publisher')
    exec(compile(text.replace(slot, repr(TITLE), 1), CLIENT_PATH, 'exec'), client.__dict__)
    client.VERSION='0.10.1'
    client.SOURCE=SOURCE
    client.SOURCE_RUN=os.environ.get('GITHUB_RUN_ID','unknown')
    client.THEOREM_NAME=NAME
    client.SOLUTION=PACKET/'solution.lean'
    client.SOLUTION_SHA256=hashlib.sha256(solution).hexdigest()
    client.OUT=OUT
    client.PREAMBLE=PREAMBLE
    client.FORMAL=FORMAL
    client.NATURAL=NATURAL
    client.EXPLANATION=EXPLANATION
    api=client.API(os.environ.get('PROVE2ME_API_KEY',''))
    for name, expected in DEPENDENCIES.items():
        rec=api.request('/theorems/'+expected['id'])
        if (rec.get('theorem_name')!=name or rec.get('status')!='Proved'
                or rec.get('mathlib_rev')!=PIN
                or client.norm(rec.get('formal_statement'))!=client.norm(expected['formal'])):
            raise RuntimeError('Proved dependency identity/type/status mismatch: '+name)
        client.save(OUT/(name.replace('.','_')+'.json'),rec)

    def link_mission(api, mission, result):
        mid,tid=mission['id'],result['theorem_id']
        offset=0
        while True:
            page=api.request(f'/missions/{mid}/comments?limit=100&offset={offset}')
            rows=page.get('comments',[])
            for c in rows:
                if any(r.get('type')=='theorem' and r.get('id')==tid for r in c.get('references',[])):
                    client.save(OUT/'mission-comment.json',c); return c
            offset += len(rows)
            if not rows or offset >= int(page.get('total',offset+1)): break
        body=(f'Published [excess-two arbitrary-checkpoint carrier diameter](p2m:theorem/{tid})'
          + (f' with [accepted proof](p2m:solution/{result["submission_id"]})' if result.get('submission_id') else '')
          + ': in any bounded n-row H-polyhedron with n<=d+2, every common carrier based at a feasible checkpoint has intrinsic padded graph diameter <=2, even when the second checkpoint is nonvertex or infeasible. The proof combines effective-row deletion/rank-nullity with the already-Proved small-excess diameter theorem and common-face graph transport. This closes the low-ambient-excess carrier routing case, not general whole-walk edge refinement: arbitrary Polynomial Hirsch carriers need not have excess <=2. The d>=4 edge-refinement frontier remains Open.')
        c=api.request(f'/missions/{mid}/comments',{'body_md':body,'tags':['reference','strategy']},'POST')
        client.save(OUT/'mission-comment.json',c)
        return c
    client.link_mission=link_mission
    client.main()


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode',choices=['prepare','publish'])
    args=ap.parse_args()
    prepare() if args.mode=='prepare' else publish()
