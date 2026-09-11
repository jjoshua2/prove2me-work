#!/usr/bin/env python3
"""Publish the audited common-face small-carrier-excess theorem.

The compact local driver represents two existing public theorems as explicit
premises.  Before any write, this publisher authenticates and checks their exact
name, formal statement, status=Proved and Mathlib pin.  The submitted proof uses
tracked theorem imports and exposes a ROOT-LEVEL declaration named `solution`.
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

SOURCE = '732a3d13258662977d110642e093fdf94aea9528'
DRIVER_PATH = 'Solutions/PolynomialCommonFaceSmallCarrierPublicDriver.lean'
DRIVER_BLOB = 'cc3d70bb2eeea0a9cd4a1fe7931a263bac1836ec'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
PACKET = Path('/tmp/common-face-small-carrier-public')
OUT = Path('common_face_small_carrier_publication_receipts')
NAME = 'Hirsch.common_face_diameter_of_subpresentation_excess_le_three'
TITLE = 'Common-face diameter equals its small presentation excess up to three'
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
    (r : ℕ) (hr : r ≤ 3)
    (hsub : HirschCommonFace.HasSubpresentationAtMost
      (HirschCommonFace.commonFaceA a b u v)
      (HirschCommonFace.commonFaceB a b u v)
      (HirschCommonFace.commonFaceDim a b u v + r)) :
    DiamLE (HirschCommonFace.commonFace a b u v) r'''
FORMAL = (
    'namespace Hirsch\n'
    'theorem common_face_diameter_of_subpresentation_excess_le_three\n' +
    BINDERS + ' := by sorry\nend Hirsch'
)
NATURAL = '''Let P={x in R^d : <a_i,x> <= b_i} be a bounded finite H-polyhedron and let u,v be arbitrary points. Write F for the common carrier cut out by the nonzero describing rows tight at both u and v, and let h be its canonical coordinate dimension. Suppose the coordinate H-polyhedron of F has an equivalent subpresentation using at most h+r original coordinate rows, where r<=3. Then the intrinsic padded vertex-edge graph diameter of F is at most r. Neither checkpoint is required to be a vertex or feasible. The ambient parent may have arbitrary row excess. This is a local carrier-cost theorem, not an assertion that every Polynomial Hirsch carrier has r<=3.'''
EXPLANATION = '''## Exact local carrier cost

Let the canonical common-face coordinate H-polyhedron have dimension h. The hypothesis supplies an equivalent m-row subpresentation with m<=h+r and r<=3. Parent boundedness transfers to the coordinate polyhedron because the common-face lift is isometric.

The already-Proved small-excess theorem `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three` applies to the equivalent m-row coordinate presentation: m<=h+3, so its graph diameter is at most m-h. Since m-h<=r, pad the resulting graph walk to length r. Equality of presentations transfers that diameter bound to the full common-face coordinate H-polyhedron.

Finally use the already-Proved `Hirsch.common_face_diamLE_of_coord_diamLE` to transport the genuine vertex-edge walk into the intrinsic common carrier. No ambient edge outside the carrier is used.

The proof does not assume endpoint extremality, strict feasibility, irredundancy, circuit structure, or a global diameter bound. It only converts an explicit small carrier-presentation excess certificate into its exact ordinary graph-routing cost. The general d>=4 edge-refinement problem remains the task of controlling/amortizing such carrier costs across a whole walk.'''

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
    return '\n'.join(rows)+'\n'


def expected_solution() -> bytes:
    imports='\n'.join('import Theorems.Thm_'+name.replace('.','_') for name in DEPENDENCIES)
    wrapper='''

theorem solution
''' + BINDERS + ''' := by
  exact HirschSmallCarrierPublic.common_face_diameter_of_subpresentation_excess_le_three_from_proved_inputs
    Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three
    Hirsch.common_face_diamLE_of_coord_diamLE
    a b u v hbd r hr hsub
'''
    return (imports+'\n'+driver_body()+wrapper).encode('utf-8')


def prepare() -> None:
    driver=driver_bytes(); solution=expected_solution()
    PACKET.mkdir(parents=True,exist_ok=True)
    (PACKET/'driver.lean').write_bytes(driver)
    (PACKET/'solution.lean').write_bytes(solution)
    manifest={
        'source_commit':SOURCE,
        'driver_git_blob':DRIVER_BLOB,
        'driver_sha256':hashlib.sha256(driver).hexdigest(),
        'solution_sha256':hashlib.sha256(solution).hexdigest(),
        'target':NAME,
        'dependencies':{k:v['id'] for k,v in DEPENDENCIES.items()},
        'root_level_solution':True,
    }
    (PACKET/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2),flush=True)


def publish() -> None:
    driver=driver_bytes(); solution=expected_solution()
    for name,expected in [('driver.lean',driver),('solution.lean',solution)]:
        p=PACKET/name
        if not p.is_file() or p.read_bytes()!=expected:
            raise RuntimeError('frozen packet mismatch: '+name)
    audit=PACKET/'driver-audit-passed.sha256'
    dh=hashlib.sha256(driver).hexdigest()
    if not audit.is_file() or audit.read_text().strip()!=dh:
        raise RuntimeError('compact driver audit receipt missing')
    text=read_blob(CLIENT_COMMIT,CLIENT_PATH,CLIENT_BLOB).decode('utf-8')
    slot='"Normalized two-moment slices have graph diameter at most two"'
    if text.count(slot)!=1:
        raise RuntimeError('reviewed client title slot changed')
    client=types.ModuleType('reviewed_small_carrier_publisher')
    exec(compile(text.replace(slot,repr(TITLE),1),CLIENT_PATH,'exec'),client.__dict__)
    client.VERSION='0.10.1'; client.SOURCE=SOURCE
    client.SOURCE_RUN=os.environ.get('GITHUB_RUN_ID','unknown')
    client.THEOREM_NAME=NAME; client.SOLUTION=PACKET/'solution.lean'
    client.SOLUTION_SHA256=hashlib.sha256(solution).hexdigest()
    client.OUT=OUT; client.PREAMBLE=PREAMBLE; client.FORMAL=FORMAL
    client.NATURAL=NATURAL; client.EXPLANATION=EXPLANATION
    api=client.API(os.environ.get('PROVE2ME_API_KEY',''))
    for name,expected in DEPENDENCIES.items():
        rec=api.request('/theorems/'+expected['id'])
        if (rec.get('theorem_name')!=name or rec.get('status')!='Proved'
                or rec.get('mathlib_rev')!=PIN
                or client.norm(rec.get('formal_statement'))!=client.norm(expected['formal'])):
            raise RuntimeError('Proved dependency identity/type/status mismatch: '+name)
        client.save(OUT/(name.replace('.','_')+'.json'),rec)

    def link_mission(api,mission,result):
        mid,tid=mission['id'],result['theorem_id']
        body=(f'Published [small common-carrier presentation excess gives the same graph-diameter cost](p2m:theorem/{tid})'
          + (f' with [accepted proof](p2m:solution/{result["submission_id"]})' if result.get('submission_id') else '')
          + ': if a bounded common carrier of coordinate dimension h has an equivalent original-row subpresentation using at most h+r rows with r<=3, its intrinsic padded graph diameter is <=r. This theorem is independent of endpoint extremality and ambient row excess. It turns an explicit per-carrier presentation certificate into exact ordinary graph-routing cost; it does not assert that arbitrary circuit carriers have r<=3. The general d>=4 edge-refinement frontier remains Open.')
        c=api.request(f'/missions/{mid}/comments',{'body_md':body,'tags':['reference','strategy']},'POST')
        client.save(OUT/'mission-comment.json',c); return c
    client.link_mission=link_mission
    client.main()


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode',choices=['prepare','publish'])
    args=ap.parse_args()
    prepare() if args.mode=='prepare' else publish()
