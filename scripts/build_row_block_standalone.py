#!/usr/bin/env python3
"""Reproduce the source-faithful, focused-import row-block proof and manifest.

This retains every local proof/definition body from four modules in dependency
order. File-local scopes are closed; only imports and dependency axiom-print
commands are replaced. No network, credentials, theorem stubs, or invented
axioms. Use --expected-manifest to fail on any source drift.
"""
from __future__ import annotations
import argparse,hashlib,json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
MODULES=['Definitions.Def_Hirsch_model','Solutions.PolynomialProductWalk',
         'Solutions.PolynomialAffineDiameterTransport','Solutions.PolynomialRowBlockRouting']
HEADER='''import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Bornology.Constructions
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

'''


def build(output:Path,manifest_path:Path,expected:Path|None=None)->None:
    if (ROOT/'lean-toolchain').read_text().strip()!='leanprover/lean4:v4.30.0':
        raise RuntimeError('Lean pin mismatch')
    lake=json.loads((ROOT/'lake-manifest.json').read_text())
    if not any(p.get('name')=='mathlib' and p.get('rev')==PIN for p in lake['packages']):
        raise RuntimeError('Mathlib pin mismatch')
    out=[HEADER];manifest=[];seen=set()
    for module in MODULES:
        path=ROOT/(module.replace('.','/')+'.lean');text=path.read_text(encoding='utf-8')
        for imp in re.findall(r'^import\s+(\S+)',text,re.M):
            if imp!='Mathlib' and not imp.startswith('Mathlib.') and imp not in seen:
                raise RuntimeError('unhandled or out-of-order import: '+imp)
        lines=[];balance=0
        for line in text.splitlines():
            if line.startswith('import '):continue
            if line.startswith('#print axioms') and module!=MODULES[-1]:continue
            if re.match(r'^(?:noncomputable\s+)?section(?:\s|$)|^namespace\s',line):balance+=1
            if re.match(r'^end(?:\s|$)',line):balance-=1
            if balance<0:raise RuntimeError('unbalanced scope: '+module)
            lines.append(line)
        out += [f'\n-- BEGIN {module}\nsection\n','\n'.join(lines)+'\n','end\n'*balance,'end\n']
        data=path.read_bytes()
        manifest.append({'module':module,'sha256':hashlib.sha256(data).hexdigest(),
            'git_blob':hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()})
        seen.add(module)
    if expected is not None and manifest!=json.loads(expected.read_text()):
        raise RuntimeError('source drift from frozen manifest')
    output.parent.mkdir(parents=True,exist_ok=True);manifest_path.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(''.join(out),encoding='utf-8')
    manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'local_modules':len(MODULES),'standalone_sha256':
        hashlib.sha256(output.read_bytes()).hexdigest()},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True)
    p.add_argument('--expected-manifest',type=Path);args=p.parse_args()
    build(args.output,args.manifest,args.expected_manifest)
