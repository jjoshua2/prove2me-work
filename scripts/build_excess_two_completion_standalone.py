#!/usr/bin/env python3
"""Flatten the audited excess-two dependency chain into one standalone Lean proof.

This performs no compilation or API call. The output must be independently
compiled and axiom-audited before publication.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

MODULES = [
    'Solutions.PolynomialExcessTwoMomentSlice',
    'Solutions.PolynomialExcessTwoPairVertices',
    'Solutions.PolynomialExcessTwoSupportFaces',
    'Solutions.PolynomialExcessTwoConvexity',
    'Solutions.PolynomialExcessTwoSharedAdjacency',
    'Solutions.PolynomialExcessTwoVertexClassification',
    'Solutions.PolynomialExcessTwoSingletonAdjacency',
    'Solutions.PolynomialExcessTwoDiameter',
]
EXTERNAL = {'Mathlib', 'Definitions.Def_Hirsch_model'}
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def mask_comments(text: str) -> str:
    """Mask nested block/line comments while preserving line boundaries."""
    out: list[str] = []
    depth, i = 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            out.extend('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            if end == -1:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        else:
            ch = text[i]
            require(depth > 0 or ch != '"', 'unexpected string in fixed source chain')
            out.append(ch if ch == '\n' or not depth else ' ')
            i += 1
    require(depth == 0, 'unclosed Lean block comment')
    return ''.join(out)


def flatten(repo: Path) -> tuple[str, list[dict[str, str]]]:
    chunks = ['import Mathlib\nimport Definitions.Def_Hirsch_model\n']
    seen: set[str] = set()
    sources: list[dict[str, str]] = []
    for module in MODULES:
        relative = Path(module.replace('.', '/') + '.lean')
        raw = (repo / relative).read_bytes()
        text = raw.decode('utf-8')
        masked = mask_comments(text)
        require(not re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide|unsafe)\b', masked),
                f'forbidden proof escape in {relative}')
        content: list[str] = []
        scopes: list[tuple[str, str]] = []
        for original, code in zip(text.splitlines(), masked.splitlines()):
            line = code.strip()
            if line.startswith('import '):
                dependencies = line[7:].split()
                require(all(dep in EXTERNAL or dep in seen for dep in dependencies),
                        f'unreviewed/out-of-order import in {relative}: {line}')
                continue
            if line.startswith('#print axioms '):
                continue
            require(not line.startswith(('#eval', '#check', '#print')),
                    f'unexpected command in {relative}')
            if line.startswith('namespace '):
                scopes.append(('namespace', line[len('namespace '):].strip()))
            elif re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+\w+)?', line):
                parts = line.replace('noncomputable ', '').split()
                scopes.append(('section', parts[1] if len(parts) > 1 else ''))
            elif re.fullmatch(r'end(?:\s+[\w.]+)?', line):
                require(bool(scopes), f'unmatched end in {relative}')
                _, name = scopes.pop()
                endname = line[3:].strip()
                require(not endname or endname == name, f'scope mismatch in {relative}')
            content.append(original)
        require(all(kind == 'section' and not name for kind, name in scopes),
                f'unclosed named scope in {relative}')
        content.extend('end' for _ in scopes)
        chunks.append(f'\n-- BEGIN {relative.as_posix()}\n' + '\n'.join(content) + '\n')
        sources.append({'module': module, 'sha256': hashlib.sha256(raw).hexdigest()})
        seen.add(module)
    chunks.append('''
open scoped BigOperators RealInnerProductSpace

/-- Public-facing expanded type: no custom moment-slice definition appears in
this statement. -/
theorem solution {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) :
    Hirsch.DiamLE
      {s : EuclideanSpace ℝ (Fin n) |
        (∀ i, 0 ≤ s i) ∧ (∑ i, s i) = 1 ∧ (∑ i, t i * s i) = mu} 2 := by
  exact HirschExcessTwo.momentSlice_diamLE_two t mu

#print axioms solution
''')
    return ''.join(chunks), sources


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--repo', type=Path, default=Path('.'))
    args = parser.parse_args()
    require((args.repo / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.30.0',
            'Lean pin mismatch')
    packages = json.loads((args.repo / 'lake-manifest.json').read_text())['packages']
    require(any(p.get('name') == 'mathlib' and p.get('rev') == PIN for p in packages),
            'Mathlib pin mismatch')
    proof, sources = flatten(args.repo)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(proof, encoding='utf-8')
    data = {
        'evidence_level': 'generated source only; requires Lean compilation and axiom audit',
        'mathlib_rev': PIN,
        'sources': sources,
        'standalone_sha256': hashlib.sha256(proof.encode()).hexdigest(),
    }
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    print(json.dumps(data, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
