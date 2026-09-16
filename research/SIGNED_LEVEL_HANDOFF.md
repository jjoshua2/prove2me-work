# Signed coordinate levels: continuation handoff

## Current work and scope

Baseline main `e455a8da7080786f7d622a44c80cc970f1e2922e`; branch
`research/signed-coordinate-levels`. Recheck live main, STATUS, the five project
instructions and open ownership before continuing. Coordination comment5691300413
on #273 was posted/read back. #273's disjoint-cut code, #272's global direction
catalogue, #270's blocked companion, other active branches and #210 are unchanged.

This is COMPLETE WRITTEN RESEARCH and exact software, not a Lean packet. There
is no new compiler/axiom gate, Actions run, theorem registration, platform
submission or authenticated root/leaf poll. Local Lean/Lake/gh were absent and
release/GitHub-host DNS failed. No secrets, permissions, workflows or pin changed.

## What is proved and actually implemented

For [0,1]^d with cuts proportional to signed unit pair rows +/-e_i+/-e_j,
choose d independent active original rows. Their signed graph consists of
anchored trees and unbalanced unicycles. With q distinct nonzero absolute
normalized RHS values C, EVERY vertex coordinate belongs to

    Lambda = [0,1] intersect (({-1,0,1}+S_(d-1)(C)) union (1/2)S_(2d)(C)),
    S_R(C) = {n.C : n integer, ||n||_1<=R}.

The alphabet is derived from ALL input data, not from visited bases. Its size
is at most3B_q(d-1)+B_q(2d), where B_q(R)=sum_j 2^j binom(q,j)binom(R,j).
The classical coordinate-extreme argument gives a genuine original route
of length at most d(|Lambda|-1), within the least common original face.
Each phase moves BOTH fronts to the same minimum or maximum coordinate face;
rank changes, not numerical gaps, count its edges. No nonlinear coordinate
rounding or single fixed objective is asserted. Facet reentries can occur.
The q1 bound is4d^2-d, independent of numerical denominators.

The producer uses LPs on normalized tangent sections. A fixed rational
lexicographic objective selects a real extreme ray without full local-star
or global direction enumeration. Its {0,+/-1}/H direction denominator bound
H<=2m makes the symbolic priority exact. Zero-gap original-row duals certify
phase endpoints. The consumer checks original vertex/edge right inverses and
phase duals without LP, inversion, elimination or route discovery. Alphabet
enumeration is still performed. LP-call count is at most L+4d; the inherited
Bland INTERNAL pivot count is not proved polynomial. Caps are failures, not
certificates of no route. Lower-dimensional inputs use ambient dimension;
only genuinely established facet counts are labelled facets.

## Important stronger EXISTING guarantee

Do not turn the implementation's fixed-q requirement into a false open theorem.
The same signed-root row systems have GLOBAL delta-distance at least1/sqrt(2d).
The orthogonal complement of any row span has disjoint signed-indicator
components C; the exact squared projection is sum_C (a.s_C)^2/|C|. A nonzero
integer numerator gives the bound. Dadush--Haehnle arXiv1412.6705v1,
Definition4/Lemma5/Theorem3, already imply the explicit diameter estimate

    8 sqrt(2) d^(5/2) [1+log(d sqrt(2d))]

for full-dimensional pointed signed-normal polyhedra with ARBITRARY real RHS,
even unbounded. This is a written specialization of classical theory, not a
new shadow algorithm or historical priority claim. Its algorithm is NOT
implemented here, and its pivot guarantee does not transfer to our LP engine.
Our explicit few-level path can have a smaller bound in the q1 case.
Michini--Sassano's diameter<=d is already stronger on the stable-set examples.

The complete note SIGNED_COORDINATE_LEVEL_ROUTES.md credits these facts and
also distinguishes current Black arXiv2609.08647v1 from our claim: fixed-height
lattice boxes can have exponential MONOTONE diameter; unbounded 0/1-vertex
polyhedra can have exponential ordinary diameter. Our finite-level argument
requires compactness and permits changing/reversing objectives. No reproduction
of those published constructions is claimed.

## Executed results and nonshortest cases

Fourteen independent full-H references:2253 active bases,103 vertices,168 edges.
201 tested pairs use333 edges vs314 BFS;17 outputs are nonshortest,6 row reentries.
Six larger routes use124 original edges,700 LP calls and15622 internal pivots.

- Tiny theta=2^-160 chain: d16/32 uses16/32 edges, shortest by a proved simple
  target-facet count. d32 has95 genuine facets,31 cuts tight at target,97 levels,
  bound3072, no common endpoint facet. The old scaled-grid number is only a
  loose UPPER bound, not a comparison against best known geometry.
- Nonsimple wheel d16/32: all30/62 cut rows meet; actual paths10/18, with
  separate SHORTEST two-edge comparisons. The d32 input has94 genuine facets
  and32 redundant box upper rows, not126 facets. Preserve this adverse result.
- Two-magnitude mixed-sign cases d16/32:23/47 active cut rows,16/32 returned
  edges; represented rows55/111. Neither facet minimality nor shortestness is
  asserted for those mixed inputs.

A complete-graph family has at least2^(d-1)-d ACTUAL edge directions, while the
coordinate alphabet has four levels. At d32 this is2,147,483,616 lines versus
level bound96. The count is a proved formula, not an enumeration;22 sample
edges were checked. This is classical stable-set geometry used as a control.

Nineteen malformed/unsupported/capped cases fail. The unequal-gain cube gives
2^d distinct last-coordinate values from just RHS0,1; tests through d12. Its
actual diameter is d, so this obstructs an extension of the LEVEL method, not
Polynomial Hirsch. Independent exact Gram projections test the signed-angle
formula11716 times:8079 positive distances and3637 zero distances. Unequal
coefficient near-parallel controls through2^-160 show the angle restriction.

Thirteen saved route records and two comparison paths replay with LP, inverse,
elimination, vertex/route producers and lexicographic selection disabled.
The initial combined large process timed out after five models at the45-second
harness limit; final sources use separate named stages, all of which completed.
It is not a failed proof, negative route certificate or unreported large success.

## Integrity, files and reproduction

Three new source blobs, all remotely read back and matched locally:
- signed_level_routes.py:02ed5aad782913b8b93b1da9d596d69b84e89301.
- test_signed_level_routes.py:999d0c4b4fcfc5fc77b489012ad666375d181fcb.
- check_signed_root_angles.py:ea7089bac94998a1e6dbc2bc15e1e4b7897c75de.

Two byte-identical dependencies are reused, NOT overwritten:
exact_farkas_lp.py (ea511a79164d953792942d8be3dd3537646738d6) and
original_route_exclusion.py (a764196e54970825823cad4575b947b507f95951).

A clean FIVE-source workspace reproduced all EIGHT raw reports and SEVEN
serialized fixture files BYTE-FOR-BYTE. No timing fields were excluded. The
original graphs and Gram reference use installed SymPy; the route producer
and certificate consumer need standard-library rational arithmetic only.
Source manifest, derived compact summary and replay file retain the full
raw report/fixture hashes. Full records accompany the ZIP and regenerate:

    for s in small chain wheel mixed directions negative audit; do
      python3 scripts/test_signed_level_routes.py --stage "$s" \
        --out "/tmp/$s.json" --fixtures /tmp/signed-level-fixtures
    done
    python3 scripts/check_signed_root_angles.py --out /tmp/angles.json

The add-only research patch excludes both dependencies and does not replace
root STATUS. The new handoff and completion comment provide the frontier link.
No source/parser correctness is silently described as Lean-extracted.

## Remaining conjecture-facing obligation

The unrestricted obstacle is not high cut overlap, a huge actual direction
set, or arbitrary RHS within these signed-root normals. Those have the above
class-specific solutions or existing polynomial guarantees. Arbitrary carriers
need not have such a normal structure, a well-conditioned coordinate chart,
or a small finite-level inventory. Unequal coefficient gains break both
arguments while still allowing short routes in the example. A next general
step must control original routes beyond that structural restriction, without
restarting #267's ruled-out universal polynomial complete flagification.
