#!/usr/bin/env python3
"""Build review/verification packets only. This script makes no API calls."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'damage_progress_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
TARGETS = {
    'ordered_exact': ('Solutions.Sol_Hirsch_ordered_damage_repair', 'solution'),
    'mixed_regions': ('Solutions.PolynomialMixedRegionRouting', 'solution'),
}
MIXED_SIGNATURE = r'''theorem solution
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (a b : κ → EuclideanSpace ℝ (Fin d)) (hedge : ∀ e, Adj P (a e) (b e))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ P)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))) ∧
        w (k + 1) ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q ((∑ i, B i) + Fintype.card κ) = w L ∧
      ∀ j < (∑ i, B i) + Fintype.card κ,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1))'''


def bundle(label: str, target: str, declaration: str) -> dict:
    seen: set[str] = set()
    imports: set[str] = set()
    bodies: list[str] = []
    files: list[dict[str, str]] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        path = ROOT / (module.replace('.', '/') + '.lean')
        text = path.read_text(encoding='utf-8')
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('Solutions.'):
                        visit(dep)
                    elif dep.startswith('Theorems.'):
                        raise ValueError('Unverified theorem import: ' + dep)
                    else:
                        imports.add(dep)
        body = '\n'.join(line for line in text.splitlines()
                         if not line.startswith(('import ', '#print axioms ')))
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', body, re.M):
            raise ValueError('Forbidden declaration/admission in ' + module)
        count = len(re.findall(r'^noncomputable section\s*$', body, re.M))
        if count != 1:
            raise ValueError('Unexpected section layout: ' + module)
        bodies.append('-- BEGIN ' + module + '\n' + body + '\nend\n')
        files.append({'path': str(path.relative_to(ROOT)),
                      'sha256': hashlib.sha256(text.encode()).hexdigest()})

    visit(target)
    if imports != {'Mathlib', 'Definitions.Def_Hirsch_model'}:
        raise ValueError('Unexpected standalone imports: ' + repr(imports))
    text = '\n'.join('import ' + i for i in sorted(imports)) + '\n\n'
    text += 'set_option maxHeartbeats 8000000\n\n' + '\n'.join(bodies)
    if label == 'mixed_regions':
        text += '\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n\n'
        text += MIXED_SIGNATURE + ' := by\n'
        text += ('  exact HirschRegionRoute.route_of_faces_and_surviving_edges\n'
                 '    P F B hF hD a b hedge w L hverts hcover\n')
    text += '\n#print axioms ' + declaration + '\n'
    output = OUT / (label + '.lean')
    output.write_text(text, encoding='utf-8')
    return {'label': label, 'path': output.name, 'declaration': declaration,
            'bytes': len(text.encode()),
            'sha256': hashlib.sha256(text.encode()).hexdigest(), 'sources': files}


def main() -> None:
    OUT.mkdir(exist_ok=True)
    items = [bundle(label, *spec) for label, spec in TARGETS.items()]
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                                     text=True).strip()
    result = {'mathlib_rev': PIN, 'git_commit': commit, 'published': False,
              'packets': items,
              'note': 'No Prove2Me API calls. Both packets use public-vocabulary '
                      'solution wrappers and import only Mathlib and Def_Hirsch_model.'}
    (OUT / 'manifest.json').write_text(json.dumps(result, indent=2) + '\n')
    header = ('import Mathlib\nimport Definitions.Def_Hirsch_model\n\n'
              'open scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n\n')
    (OUT / 'mixed_regions_statement.lean.txt').write_text(
        header + MIXED_SIGNATURE.replace('theorem solution',
            'theorem Hirsch.route_of_faces_and_surviving_edges', 1)
        + ' := by sorry\n', encoding='utf-8')
    ordered = (ROOT / 'Solutions/Sol_Hirsch_ordered_damage_repair.lean').read_text()
    signature = 'theorem solution' + ordered.split('theorem solution', 1)[1].split(' := by', 1)[0]
    (OUT / 'ordered_exact_statement.lean.txt').write_text(
        header + signature.replace('theorem solution', 'theorem Hirsch.ordered_damage_repair_exact', 1)
        + ' := by sorry\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
