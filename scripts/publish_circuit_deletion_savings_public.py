#!/usr/bin/env python3
"""Publish the kernel-audited exact circuit-carrier savings identity.

The publication packet is rebuilt from an immutable repository commit. Local
Definitions modules are treated as platform imports; all required Solutions
proof bodies are flattened in dependency order into one standalone file. The
public source theorem is renamed locally and used only to prove a root-level
`solution`. No credential is read until that exact file has independently
compiled and passed the repository axiom audit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import types
from pathlib import Path

from publish_affine_diameter_transport import (
    read_blob, CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB,
)

SOURCE = 'ed33edd69aa9a25129b31a8448ef3303abb29b4e'
SOURCE_RUN = '34639229285'
TARGET_MODULE = 'Solutions.PolynomialCircuitDeletionSavingsPublic'
TARGET_PATH = 'Solutions/PolynomialCircuitDeletionSavingsPublic.lean'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
PACKET = Path('/tmp/circuit-deletion-savings-public')
OUT = Path('circuit_deletion_savings_publication_receipts')
NAME = 'Hirsch.row_circuit_selected_excess_defect_savings_identity'
TITLE = 'Exact deletion-savings identity for a row-circuit common carrier'
LOCAL_TARGET = 'standalone_row_circuit_selected_excess_defect_savings_identity'

EXTERNAL_DEFS = {
    'Definitions.Def_Hirsch_model',
    'Definitions.Def_Hirsch_circuit_model',
    'Definitions.Def_Hirsch_circuit_slack_model',
    'Definitions.Def_Hirsch_common_face_geometry',
}

PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_circuit_slack_model
import Definitions.Def_Hirsch_common_face_geometry
open scoped BigOperators RealInnerProductSpace InnerProduct
open Set Module Hirsch'''

BINDERS = '''    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y)
    (hface : HirschCommonFace.commonFaceDim a b x y ≤ F.card) :
    let h := HirschCommonFace.commonFaceDim a b x y
    let E := HirschCommonFace.commonFaceEffectiveRows a b x y
    let Z := Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0)
    let delta := (h - 1) -
      Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a (F ∩ Z)).domRestrict
          (HirschCommonFace.commonDirection a b x y)).range)
    (F.card - h) + delta +
      (n + h - (E.card + d)) +
      ((E \\ F) \\ Z).card + (((E \\ F) ∩ Z).card - delta) = n - d'''

FORMAL = (
    'namespace Hirsch\n'
    'theorem row_circuit_selected_excess_defect_savings_identity\n' +
    BINDERS + ' := by sorry\nend Hirsch'
)

NATURAL = '''Let P={x in R^d : <a_i,x> <= b_i} be a bounded finite n-row H-polyhedron, let x be feasible, and suppose y-x is a row-circuit direction. For the canonical common carrier of x and y, let h be its coordinate dimension, E the original rows whose restrictions to the carrier are nonzero, Z the nonzero ambient rows neutral on y-x, and F any selected subset of E with |F|>=h. Let delta be the loss of neutral restricted rank after keeping only F∩Z. Then the ambient row excess n-d splits exactly into five nonnegative accounting terms: selected presentation excess |F|-h, neutral-rank defect delta, surplus row disappearance n+h-(|E|+d), omitted nonneutral effective rows |(E\\F)\\Z|, and omitted-neutral redundancy |(E\\F)∩Z|-delta. Their sum is exactly n-d. Neither checkpoint is required to be a vertex. This is an exact one-carrier identity, not a graph-routing theorem.'''

EXPLANATION = '''## Exact accounting rather than a weakened inequality

Write W for the common-direction subspace, E for rows restricting nontrivially to W, and Z for the ambient circuit-neutral rows. Boundedness plus feasibility makes the ambient row map injective and gives the exact circuit-neutral rank on W. Deleting neutral rows from the full effective neutral family can lose at most one rank unit per deleted row, so the selected neutral defect delta is at most |(E\\F)∩Z|.

Three cardinal identities then account for every row. First, effective-row counting gives |E|+d<=n+h; its slack is the disappearance surplus kappa=n+h-(|E|+d). Second, because F⊆E, |E\\F|+|F|=|E|. Third, the discarded effective rows split disjointly into neutral and nonneutral parts. With h<=|F| and d<=n, elementary natural-number arithmetic yields

$$(|F|-h)+\\delta+\\kappa+|(E\\setminus F)\\setminus Z|+(|(E\\setminus F)\\cap Z|-\\delta)=n-d.$$

Thus the usual excess-plus-defect bound loses three explicit nonnegative savings. In particular, saturation of the old bound is a rigid equality case rather than a generic phenomenon. The theorem is local accounting only: it does not assert that the savings telescope along a circuit walk or that a high-excess carrier has small graph diameter. The Polynomial Hirsch edge-refinement frontier therefore remains open.'''


def git_show(path: str) -> bytes:
    return subprocess.run(
        ['git', 'show', SOURCE + ':' + path], check=True, capture_output=True
    ).stdout


def module_bytes(module: str) -> bytes:
    return git_show(module.replace('.', '/') + '.lean')


def build_solution() -> tuple[bytes, list[dict]]:
    seen: set[str] = set()
    order: list[tuple[str, bytes]] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        if module == 'Mathlib' or module.startswith('Mathlib.'):
            return
        if module in EXTERNAL_DEFS:
            return
        if module.startswith('Definitions.'):
            raise RuntimeError('unreviewed external definition import: ' + module)
        if module.startswith('Theorems.'):
            raise RuntimeError('theorem dependency/stub import forbidden: ' + module)
        data = module_bytes(module)
        text = data.decode('utf-8')
        for imp in re.findall(r'^import\s+(\S+)', text, re.M):
            visit(imp)
        order.append((module, data))

    visit(TARGET_MODULE)
    rows: list[str] = [PREAMBLE, '\n\nset_option autoImplicit false\n']
    manifest: list[dict] = []
    for module, data in order:
        text = data.decode('utf-8')
        if module == TARGET_MODULE:
            needle = 'theorem row_circuit_selected_excess_defect_savings_identity\n'
            if text.count(needle) != 1:
                raise RuntimeError('target declaration shape changed')
            text = text.replace(needle, 'theorem ' + LOCAL_TARGET + '\n', 1)
        body: list[str] = []
        balance = 0
        for line in text.splitlines():
            if re.match(r'^import\s', line):
                continue
            if line.startswith('#print axioms'):
                continue
            if re.match(r'^(?:noncomputable\s+)?section(?:\s|$)|^namespace\s', line):
                balance += 1
            if re.match(r'^end(?:\s|$)', line):
                balance -= 1
            if balance < 0:
                raise RuntimeError('unbalanced scopes in ' + module)
            body.append(line)
        rows += ['\n-- BEGIN ' + module + '\nsection\n', '\n'.join(body) + '\n']
        if balance:
            rows.append('end\n' * balance)
        rows.append('end\n')
        manifest.append({
            'module': module,
            'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(
                b'blob ' + str(len(data)).encode() + b'\0' + data
            ).hexdigest(),
        })

    rows.append('\n\ntheorem solution\n' + BINDERS + ''' := by
  exact Hirsch.'''+LOCAL_TARGET+''' a b x y hbd hx hcirc F hF hface

#print axioms solution
''')
    return ''.join(rows).encode('utf-8'), manifest


def prepare() -> None:
    solution, manifest = build_solution()
    PACKET.mkdir(parents=True, exist_ok=True)
    (PACKET / 'solution.lean').write_bytes(solution)
    receipt = {
        'source_commit': SOURCE,
        'source_run': SOURCE_RUN,
        'target_module': TARGET_MODULE,
        'target_path': TARGET_PATH,
        'target': NAME,
        'mathlib_rev': PIN,
        'solution_sha256': hashlib.sha256(solution).hexdigest(),
        'embedded_modules': manifest,
        'external_definitions': sorted(EXTERNAL_DEFS),
        'tracked_theorem_dependencies': [],
        'root_level_solution': True,
    }
    (PACKET / 'manifest.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2), flush=True)


def publish() -> None:
    solution, _manifest = build_solution()
    p = PACKET / 'solution.lean'
    if not p.is_file() or p.read_bytes() != solution:
        raise RuntimeError('frozen solution packet mismatch')
    sh = hashlib.sha256(solution).hexdigest()
    audit = PACKET / 'solution-audit-passed.sha256'
    if not audit.is_file() or audit.read_text().strip() != sh:
        raise RuntimeError('standalone kernel/axiom audit receipt missing')

    text = read_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB).decode('utf-8')
    slot = '"Normalized two-moment slices have graph diameter at most two"'
    if text.count(slot) != 1:
        raise RuntimeError('reviewed client title slot changed')
    client = types.ModuleType('reviewed_circuit_deletion_savings_publisher')
    exec(compile(text.replace(slot, repr(TITLE), 1), CLIENT_PATH, 'exec'), client.__dict__)
    client.VERSION = '0.10.1'
    client.SOURCE = SOURCE
    client.SOURCE_RUN = SOURCE_RUN
    client.THEOREM_NAME = NAME
    client.SOLUTION = p
    client.SOLUTION_SHA256 = sh
    client.OUT = OUT
    client.PREAMBLE = PREAMBLE
    client.FORMAL = FORMAL
    client.NATURAL = NATURAL
    client.EXPLANATION = EXPLANATION

    def link_mission(api, mission, result):
        mid, tid = mission['id'], result['theorem_id']
        offset = 0
        while True:
            page = api.request(f'/missions/{mid}/comments?limit=100&offset={offset}')
            comments = page.get('comments', [])
            for comment in comments:
                if any(r.get('type') == 'theorem' and r.get('id') == tid
                       for r in comment.get('references', [])):
                    client.save(OUT / 'mission-comment.json', comment)
                    return comment
            offset += len(comments)
            if not comments or len(comments) < 100 or offset >= int(page.get('total', offset + 1)):
                break
        body = (
            f'Published [exact row-circuit carrier deletion-savings identity](p2m:theorem/{tid})'
            + (f' with [accepted proof](p2m:solution/{result["submission_id"]})'
               if result.get('submission_id') else '')
            + ': for a bounded parent, feasible source, row-circuit displacement, and any selected effective-row set F with h<=|F|, the full ambient row excess n-d decomposes exactly into selected presentation excess, neutral-rank defect, carrier-row disappearance surplus, omitted nonneutral rows, and redundant omitted-neutral rank. This identifies the equality/saturation structure but does not claim that savings telescope or that high-excess carriers are cheap. The d>=4 edge-refinement frontier remains Open.'
        )
        comment = api.request(f'/missions/{mid}/comments',
                              {'body_md': body, 'tags': ['reference', 'strategy']}, 'POST')
        client.save(OUT / 'mission-comment.json', comment)
        refs = {(r.get('type'), r.get('id')) for r in comment.get('references', [])}
        if ('theorem', tid) not in refs:
            raise RuntimeError('mission theorem reference was not resolved')
        if result.get('submission_id') and ('solution', result['submission_id']) not in refs:
            raise RuntimeError('mission proof reference was not resolved')
        return comment

    client.link_mission = link_mission
    client.main()


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('mode', choices=['prepare', 'publish'])
    args = ap.parse_args()
    prepare() if args.mode == 'prepare' else publish()
