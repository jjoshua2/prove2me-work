#!/usr/bin/env python3
"""Build a source-faithful standalone for the public carrier-savings identity.

All repository-local definition/proof bodies reachable from
`Solutions.PolynomialCircuitDeletionSavingsPublic` are retained in dependency
order. Imports are replaced by focused Mathlib imports; dependency axiom-print
commands are removed, while the target's own axiom report is retained. No
credentials, network access, or theorem stubs are used.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
TARGET='Solutions.PolynomialCircuitDeletionSavingsPublic'
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
HEADER='''import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
'''


def build(output: Path, manifest_path: Path, expected: Path|None=None) -> None:
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.30.0':
        raise RuntimeError('Lean pin mismatch')
    lake=json.loads((ROOT/'lake-manifest.json').read_text())
    if not any(p.get('name')=='mathlib' and p.get('rev')==PIN for p in lake['packages']):
        raise RuntimeError('Mathlib pin mismatch')
    seen=set(); order=[]
    def visit(module: str) -> None:
        if module in seen:return
        seen.add(module)
        if module=='Mathlib':return
        if module.startswith('Theorems.'):
            raise RuntimeError('theorem-stub import: '+module)
        if module.startswith('Mathlib.'):
            return
        path=ROOT/(module.replace('.','/')+'.lean')
        if not path.is_file():raise RuntimeError('unhandled import: '+module)
        text=path.read_text(encoding='utf-8')
        for imp in re.findall(r'^import\s+(\S+)',text,re.M):visit(imp)
        order.append((module,path,text))
    visit(TARGET)
    out=[HEADER];manifest=[]
    for module,path,text in order:
        rows=[];balance=0
        for line in text.splitlines():
            if re.match(r'^import\s',line):continue
            if line.startswith('#print axioms') and module!=TARGET:continue
            if re.match(r'^(?:noncomputable\s+)?section(?:\s|$)|^namespace\s',line):balance+=1
            if re.match(r'^end(?:\s|$)',line):balance-=1
            if balance<0:raise RuntimeError('unbalanced scopes: '+module)
            rows.append(line)
        out += [f'\n-- BEGIN {module}\nsection\n','\n'.join(rows)+'\n','end\n'*balance,'end\n']
        data=path.read_bytes()
        manifest.append(dict(module=module,sha256=hashlib.sha256(data).hexdigest(),
            git_blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()))
    if expected is not None and manifest!=json.loads(expected.read_text()):
        raise RuntimeError('source differs from frozen manifest')
    output.parent.mkdir(parents=True,exist_ok=True)
    manifest_path.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(''.join(out),encoding='utf-8')
    manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(dict(modules=len(order),output=str(output),
        sha256=hashlib.sha256(output.read_bytes()).hexdigest()),indent=2))


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--manifest',type=Path,required=True)
    ap.add_argument('--expected-manifest',type=Path)
    args=ap.parse_args(); build(args.output,args.manifest,args.expected_manifest)
