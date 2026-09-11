#!/usr/bin/env python3
"""Publish the standalone common-face row-excess monotonicity theorem.

The submitted proof has no Prove2Me theorem dependencies: it contains the exact
kernel-audited source proof plus a ROOT-LEVEL declaration named `solution`.
Before any write, the workflow independently compiles and axiom-audits that
exact standalone file.
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

SOURCE = '8000514edef6b0952f584b99bb0248ed8b37b5ae'
SOURCE_PATH = 'Solutions/PolynomialCommonFaceRowExcessPublic.lean'
SOURCE_BLOB = 'f0e41a15a1327e2030defc851ebb9443f8a26fb8'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
PACKET = Path('/tmp/common-face-row-excess-public')
OUT = Path('common_face_row_excess_publication_receipts')
NAME = 'Hirsch.common_face_has_subpresentation_faceDim_add_row_excess'
TITLE = 'Common-face restriction never increases finite row-presentation excess'
PREAMBLE = (
    'import Mathlib\n'
    'import Definitions.Def_Hirsch_common_face_geometry\n'
    'open scoped RealInnerProductSpace InnerProduct\n'
    'open Set Module Hirsch'
)
BINDERS = '''    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (hdn : d ≤ n) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v
      (HirschCommonFace.commonFaceDim a b u v + (n - d))'''
FORMAL = (
    'namespace Hirsch\n'
    'theorem common_face_has_subpresentation_faceDim_add_row_excess\n' +
    BINDERS + ' := by sorry\nend Hirsch'
)
NATURAL = '''Let P={x in R^d : <a_i,x> <= b_i, i=1,...,n} be any finite H-presentation with d<=n. Let u be any feasible point and v any point. Form the common carrier by making every nonzero describing row that is tight at both u and v into an equality, and let h be its canonical coordinate dimension. Then the canonical coordinate H-polyhedron of that carrier has an equivalent subpresentation using original restricted rows and at most h+(n-d) inequalities. No boundedness, circuit, vertex, strict-feasibility, or irredundancy hypothesis is required.'''
EXPLANATION = '''## Row excess cannot increase under common-face restriction

Let C be the nonzero rows tight at both checkpoints and W their common kernel. The canonical carrier dimension is h=dim W. Every row in C restricts identically to zero on W. Let F be the set of original rows whose restricted normal is nonzero. Thus C and F are disjoint.

The row-evaluation map on C has kernel W. Rank-nullity gives

$$\\operatorname{rank}(C)+h=d.$$

Its rank is at most |C|, while disjointness gives |C|+|F|<=n. Therefore

$$|F|\\le h+(n-d).$$

Delete all rows outside F. A deleted restricted row has zero normal. Feasibility of u implies its coordinate right-hand side is nonnegative, so that zero-normal inequality is a tautology. Hence retaining exactly the rows in F gives an equivalent common-face coordinate H-presentation with at most h+(n-d) rows.

The proof is purely finite-dimensional linear algebra and feasibility. It does not use boundedness, circuit structure, endpoint extremality, strict feasibility, irredundancy, or any unproved Polynomial Hirsch statement. The theorem is structural: it says carrier row-presentation excess cannot exceed ambient row excess; it does not itself bound graph diameter when n-d is large.'''


def source_bytes() -> bytes:
    return read_blob(SOURCE, SOURCE_PATH, SOURCE_BLOB)


def source_body() -> str:
    text = source_bytes().decode('utf-8')
    rows=[]
    for line in text.splitlines():
        if line.strip().startswith('import '):
            continue
        if line.strip().startswith('#print axioms '):
            continue
        rows.append(line)
    return '\n'.join(rows) + '\n'


def expected_solution() -> bytes:
    wrapper = '''

theorem solution
''' + BINDERS + ''' := by
  exact HirschRowExcessPublic.common_face_has_subpresentation_faceDim_add_row_excess
    a b u v hu hdn

#print axioms solution
'''
    return (PREAMBLE + '\n\n' + source_body() + wrapper).encode('utf-8')


def prepare() -> None:
    source=source_bytes(); solution=expected_solution()
    PACKET.mkdir(parents=True,exist_ok=True)
    (PACKET/'source.lean').write_bytes(source)
    (PACKET/'solution.lean').write_bytes(solution)
    manifest={
        'source_commit':SOURCE,
        'source_path':SOURCE_PATH,
        'source_git_blob':SOURCE_BLOB,
        'source_sha256':hashlib.sha256(source).hexdigest(),
        'solution_sha256':hashlib.sha256(solution).hexdigest(),
        'target':NAME,
        'mathlib_rev':PIN,
        'tracked_theorem_dependencies':[],
        'root_level_solution':True,
    }
    (PACKET/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(manifest,indent=2),flush=True)


def publish() -> None:
    source=source_bytes(); solution=expected_solution()
    for name,expected in [('source.lean',source),('solution.lean',solution)]:
        p=PACKET/name
        if not p.is_file() or p.read_bytes()!=expected:
            raise RuntimeError('frozen packet mismatch: '+name)
    audit=PACKET/'solution-audit-passed.sha256'
    sh=hashlib.sha256(solution).hexdigest()
    if not audit.is_file() or audit.read_text().strip()!=sh:
        raise RuntimeError('standalone kernel/axiom audit receipt missing')
    text=read_blob(CLIENT_COMMIT,CLIENT_PATH,CLIENT_BLOB).decode('utf-8')
    slot='"Normalized two-moment slices have graph diameter at most two"'
    if text.count(slot)!=1:
        raise RuntimeError('reviewed client title slot changed')
    client=types.ModuleType('reviewed_common_face_row_excess_publisher')
    exec(compile(text.replace(slot,repr(TITLE),1),CLIENT_PATH,'exec'),client.__dict__)
    client.VERSION='0.10.1'; client.SOURCE=SOURCE
    client.SOURCE_RUN=os.environ.get('GITHUB_RUN_ID','unknown')
    client.THEOREM_NAME=NAME; client.SOLUTION=PACKET/'solution.lean'
    client.SOLUTION_SHA256=sh; client.OUT=OUT
    client.PREAMBLE=PREAMBLE; client.FORMAL=FORMAL
    client.NATURAL=NATURAL; client.EXPLANATION=EXPLANATION

    def link_mission(api,mission,result):
        mid,tid=mission['id'],result['theorem_id']
        body=(f'Published [common-face row-excess monotonicity](p2m:theorem/{tid})'
          + (f' with [accepted proof](p2m:solution/{result["submission_id"]})' if result.get('submission_id') else '')
          + ': for any finite n-row H-presentation with d<=n, any feasible source checkpoint u and arbitrary v, the canonical common carrier has an equivalent original-row coordinate subpresentation using at most h+(n-d) rows. No boundedness, circuit, vertex, strict-feasibility, or irredundancy assumption is needed. Thus common-face restriction cannot increase presentation excess beyond the ambient row excess. This is structural, not a global diameter theorem; the d>=4 edge-refinement frontier remains Open.')
        c=api.request(f'/missions/{mid}/comments',{'body_md':body,'tags':['reference','strategy']},'POST')
        client.save(OUT/'mission-comment.json',c); return c
    client.link_mission=link_mission
    client.main()


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode',choices=['prepare','publish'])
    args=ap.parse_args()
    prepare() if args.mode=='prepare' else publish()
