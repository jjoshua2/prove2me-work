#!/usr/bin/env python3
"""Final compilation/axiom gate for the four standalone publication wrappers."""
from __future__ import annotations
import argparse, datetime, hashlib, json, re, subprocess
from pathlib import Path
from build_face_cover_publication import SOURCE, SOURCE_RUN, PIN, LEAN, check_proof

ALLOWED={'propext','Classical.choice','Quot.sound'}

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def run(command, log: Path):
    result=subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    log.write_text(result.stdout)
    print(result.stdout, flush=True)
    if result.returncode:raise RuntimeError('Lean command failed; see '+str(log))
    return result.stdout

def main():
    a=argparse.ArgumentParser();a.add_argument('--packet',type=Path,default=Path('face_cover_publication_packet'));args=a.parse_args()
    out=args.packet;manifest=json.loads((out/'manifest.json').read_text())
    if (manifest['source_commit'],manifest['source_run'],manifest['mathlib_rev'],manifest['lean_toolchain'])!=(SOURCE,SOURCE_RUN,PIN,LEAN):
        raise ValueError('packet provenance mismatch')
    if Path('lean-toolchain').read_text().strip()!=LEAN or PIN not in Path('lake-manifest.json').read_text():raise ValueError('working pin mismatch')
    if digest(Path('Definitions/Def_Hirsch_model.lean'))!=manifest['public_model_sha256']:raise ValueError('public model changed')
    run(['lake','build','Definitions.Def_Hirsch_model'],out/'model.log')
    records=[]
    for entry in manifest['entries']:
        key=entry['key'];proof=out/(key+'.lean');statement=out/(key+'.statement.lean')
        if digest(proof)!=entry['solution_sha256'] or digest(statement)!=entry['statement_sha256']:raise ValueError('packet changed')
        check_proof(proof.read_text())
        # Statement's one intentional sorry creates only the registration target.
        run(['lake','env','lean',str(statement)],out/(key+'.statement.log'))
        log=run(['lake','env','lean',str(proof)],out/(key+'.proof.log'))
        m=re.search(r"'solution' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
        if m:axioms={x.strip() for x in m[1].split(',') if x.strip()}
        elif "'solution' does not depend on any axioms" in log:axioms=set()
        else:raise ValueError('missing solution axiom report')
        if axioms-ALLOWED:raise ValueError('unapproved transitive axiom')
        records.append({'name':entry['name'],'key':key,'solution_sha256':digest(proof),'statement_sha256':digest(statement),
                        'axioms':sorted(axioms),'standalone_compilation':'PASSED'})
    receipt={'status':'PASSED','source_commit':SOURCE,'source_run':SOURCE_RUN,'mathlib_rev':PIN,
        'manifest_sha256':digest(out/'manifest.json'),'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'entries':records,'publication':'NOT_STARTED'}
    (out/'verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print('All four standalone statements, proofs, and transitive axiom audits PASSED.',flush=True)

if __name__=='__main__':main()
