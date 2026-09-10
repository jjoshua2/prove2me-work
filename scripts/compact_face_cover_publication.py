#!/usr/bin/env python3
"""Prune unused frozen declarations from the two large publication proofs.

The underlying theorem statements and proof declarations are unchanged. Every
included declaration is extracted verbatim from SOURCE; only transitive source
that is not referenced by these proofs is omitted. This keeps server theorem
compilation comfortably below the previous timed-out packet size.
"""
from __future__ import annotations
import hashlib, json, re, subprocess
from pathlib import Path
from build_face_cover_publication import SOURCE, PREAMBLE, check_proof


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def read_git(repo: Path, path: str) -> str:
    return subprocess.check_output(['git','-C',str(repo),'show',f'{SOURCE}:{path}'], text=True)


def decl(text: str, name: str) -> str:
    m=re.search(r'(?m)^(?:theorem|lemma|def|abbrev)\s+'+re.escape(name)+r'\b',text)
    if not m: raise ValueError('missing frozen declaration '+name)
    tail=text[m.end():]
    # A Lean doc comment belongs to the declaration *after* it. Stop before
    # that comment; otherwise a compact namespace can end immediately after
    # `/-- ... -/`, and Lean quite correctly expects a declaration before `end`.
    nxt=re.search(r'(?m)^(?:/--|(?:(?:theorem|lemma|def|abbrev)\s+)|#print\s+axioms\s+|end(?:\s|$))',tail)
    end=m.end()+(nxt.start() if nxt else len(tail))
    return text[m.start():end].rstrip()+'\n'


def ns(name: str, *chunks: str) -> str:
    return 'namespace '+name+'\n\n'+''.join(chunks)+'\nend '+name+'\n'


def frozen_sources(repo: Path) -> dict[str,str]:
    paths=[
      'Solutions/PolynomialProductWalk.lean',
      'Solutions/PolynomialFaceReentrySplice.lean',
      'Solutions/PolynomialAdjEndpoints.lean',
      'Solutions/PolynomialGeodesicFaceCover.lean',
      'Solutions/PolynomialWeightedFaceCover.lean',
      'Solutions/PolynomialVertexSpan.lean',
      'Solutions/PolynomialBalancedRowFaceCover.lean',
      'Solutions/PolynomialRankSensitiveFaceCover.lean',
    ]
    return {p:read_git(repo,p) for p in paths}


def minimal_weighted(S: dict[str,str]) -> str:
    return ''.join([
      ns('HirschProduct',
         decl(S['Solutions/PolynomialProductWalk.lean'],'append_walk'),
         decl(S['Solutions/PolynomialProductWalk.lean'],'pad_walk')),
      ns('HirschFaceSplice',
         decl(S['Solutions/PolynomialFaceReentrySplice.lean'],'extreme_in_extreme_face'),
         decl(S['Solutions/PolynomialFaceReentrySplice.lean'],'face_adj_to_parent'),
         decl(S['Solutions/PolynomialFaceReentrySplice.lean'],'splice_reentry_through_extreme_face')),
      ns('HirschPolynomialAccess',
         'variable {d : ℕ}\n',
         decl(S['Solutions/PolynomialAdjEndpoints.lean'],'adj_right_extreme')),
      ns('HirschFaceSplice',
         decl(S['Solutions/PolynomialGeodesicFaceCover.lean'],'Walk'),
         decl(S['Solutions/PolynomialGeodesicFaceCover.lean'],'IsShortestLength'),
         decl(S['Solutions/PolynomialGeodesicFaceCover.lean'],'walk_vertices_extreme'),
         decl(S['Solutions/PolynomialGeodesicFaceCover.lean'],'shortest_face_visit_span_le'),
         decl(S['Solutions/PolynomialGeodesicFaceCover.lean'],'shortest_face_visit_card_le'),
         decl(S['Solutions/PolynomialWeightedFaceCover.lean'],'shortest_weighted_face_cover_budget'),
         decl(S['Solutions/PolynomialWeightedFaceCover.lean'],'diamLE_of_weighted_face_cover')),
    ])


def minimal_codimension(S: dict[str,str]) -> str:
    return ''.join([
      ns('HirschPolynomialAccess',
         decl(S['Solutions/PolynomialVertexSpan.lean'],'vertex_tight_rows_span_checked')),
      ns('HirschRankFaceCover',
         decl(S['Solutions/PolynomialRankSensitiveFaceCover.lean'],'tight_rows_outside_subspace_card_ge_codim')),
    ])


def minimal_rank_selected(S: dict[str,str]) -> str:
    return ''.join([
      minimal_weighted(S),
      ns('HirschPolynomialAccess',
         decl(S['Solutions/PolynomialVertexSpan.lean'],'vertex_tight_rows_span_checked')),
      ns('HirschBalancedFaceCover',
         'variable {d n : ℕ}\n',
         decl(S['Solutions/PolynomialBalancedRowFaceCover.lean'],'rowSupportingFace'),
         decl(S['Solutions/PolynomialBalancedRowFaceCover.lean'],'rowSupportingFace_isExtreme')),
      ns('HirschRankFaceCover',
         decl(S['Solutions/PolynomialRankSensitiveFaceCover.lean'],'tight_rows_outside_subspace_card_ge_codim'),
         decl(S['Solutions/PolynomialRankSensitiveFaceCover.lean'],'rowSection'),
         decl(S['Solutions/PolynomialRankSensitiveFaceCover.lean'],'rowSection_isExtreme'),
         decl(S['Solutions/PolynomialRankSensitiveFaceCover.lean'],'diamLE_of_rank_increasing_row_bounds')),
    ])


def solution_wrapper(entry: dict) -> str:
    short=entry['name'].split('.')[-1]
    sig=entry['formal_statement'].split('theorem '+short,1)[1].rsplit(':= by sorry',1)[0].strip()
    proof={
      'codimension':'exact HirschRankFaceCover.tight_rows_outside_subspace_card_ge_codim a b x hx U',
      'rank_selected':'exact HirschRankFaceCover.diamLE_of_rank_increasing_row_bounds a b F hF U hU B hFD hconnect',
    }[entry['key']]
    return 'theorem solution '+sig+' := by\n  '+proof+'\n\n#print axioms solution\n'


def main() -> None:
    repo=Path('.');out=Path('face_cover_publication_packet')
    S=frozen_sources(repo)
    manifest=json.loads((out/'manifest.json').read_text())
    indexed={e['key']:e for e in manifest['entries']}
    compact={
      'codimension':minimal_codimension(S),
      'rank_selected':minimal_rank_selected(S),
    }
    for key,body in compact.items():
        entry=indexed[key]
        proof=PREAMBLE+'\n'+body+'\n'+solution_wrapper(entry)
        check_proof(proof)
        (out/(key+'.lean')).write_text(proof)
        entry['solution_sha256']=sha(proof)
        entry['solution_bytes']=len(proof.encode())
        entry['compacted']=True
        entry['compaction_sources']=[{'path':p,'sha256':sha(text)} for p,text in S.items()]
    # Finish the small independent counting theorem before the larger rank-selected
    # packet, so a later infrastructure timeout cannot hide its result.
    order={'weighted':0,'codimension':1,'barrier':2,'rank_selected':3}
    manifest['entries'].sort(key=lambda e:order[e['key']])
    manifest['compaction']='codimension and rank_selected dependency closures pruned from immutable SOURCE declarations; namespace variables restored; public statements unchanged'
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    (out/'verification.json').unlink(missing_ok=True)
    sizes={e['key']:e['solution_bytes'] for e in manifest['entries']}
    if sizes['codimension'] >= 10000 or sizes['rank_selected'] >= 30000:
        raise ValueError('compaction size regression: '+repr(sizes))
    print(json.dumps({'compacted':True,'solution_bytes':sizes},sort_keys=True))

if __name__=='__main__':main()
