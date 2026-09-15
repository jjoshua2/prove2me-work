# Complete-two-face acquisition: research handoff

Development base: main6d9dac0a5f0192759a35448de6919b2de5925a73, after #251/#252.
Ownership recorded on #252 in comment5672566155. Preserve the accepted #250
projected-face theorem and its owner, and #244's separate fibre assembly.

## What is new and what is not

Input A,b,start,target in a simple bounded full-dimensional ORIGINAL-H polytope.
An incident two-face has <=m-d+2 edges; at retained-face dimension h, binom(h,2)
faces suffice. Trace each COMPLETE polygon and take the shortest first-acquisition
arc (possibly objective-decreasing); if none exists, take a strictly increasing
arc to the largest phase value on ANY inspected face. This is not graph lookahead
of ever-increasing radius, and no factor chart/neighbor graph is supplied.

The quantitative proof charges each fallback to at least h-1 new improving
2-faces. It has dominated their phase maxima, so none can be charged again in
that phase; an acquired target facet is disjoint from every earlier no-hit face,
so none returns in later phases. With e=m-d and r=d-initial common target facets:

    (h-1)B_h <= binom(e,h-2),
    L <= r floor((e+2)/2)+sum_{j=2}^{r-1}binom(e+1,j).

This is a proved WRITTEN selector bound, not a polynomial bound in unrestricted
d,m or an improvement on best classical general diameter bounds. The code audits
actual retired labels, dominance of all inspected face maxima, and the inequality.
Do not confuse polynomial per-decision work with polynomial total work.

## Positive class and mandatory limitations

The rule is shortest for all pairs in affine products of polygons, without a
supplied product chart. Rectangular two-faces offer no new first acquisition when
none is immediate; complete polygon factors supply shortest component arcs.
The fixed-horizon parabolic obstructions now take h+2 shortest edges regardless
of the long forward chain. At N64,h2, new4 versus old65; at h16, new18 versus65.
Exploration work is still counted:69/83 full face edges, respectively.

The truncated octahedron has a source with NO incident two-face reaching a target
facet. The algorithm must fallback. It cannot be described as always acquiring
one new facet per decision. Generic new routes are not all shortest. Among1016
reference pairs:21 improve,995 tie,0 worsen in this sample only;16 new routes
remain longer than BFS. The original six-model614-pair benchmark is unchanged.

## Files and exact local commands

New scripts: two_face_acquisition.py, test_two_face_acquisition.py.
Full proof: TWO_FACE_ACQUISITION.md. Actual report: TWO_FACE_ACQUISITION_CHECK.json.
Dependency blobs are frozen and checked by the test script:
73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976 (simple_tangent_policy_audit),
4b6be3e8f7fc304c87474205898d85f71e39a15d (target_phase_pivot),
87c82480b19b3c699d2c9bcf1919d3bb8ea16058 (target_roof_phase_barrier).
They are package dependencies, NOT new commits or modified code.

    python3 -m py_compile scripts/two_face_acquisition.py scripts/test_two_face_acquisition.py
    python3 scripts/test_two_face_acquisition.py

For bounded tool runtimes, run each --graph NAME separately, then:

    python3 scripts/test_two_face_acquisition.py --family delays
    for i in 0 1 2 3 4; do python3 scripts/test_two_face_acquisition.py --product-case "$i"; done
    python3 scripts/test_two_face_acquisition.py --family roof
    python3 scripts/test_two_face_acquisition.py --aux
    python3 scripts/test_two_face_acquisition.py --assemble

Every stage must come from the same new source/dependency hashes. The dimension12
new product route is fully executed. The old depth-two comparison there exceeded
our local call budget and is explicitly NOT reported; all other stated old
comparisons are actually replayed. A first development product-stage timeout was
not a geometry failure and did not produce a PASS receipt.

## Verification discipline

Auditor never calls inverse/rank/LP/face discovery. It checks original T*D=-I,
all feasible coordinates, both allowed boundary neighbors at every polygon corner,
unique edge labels, complete eligible-face coverage, maximal original edge ends,
shortest first-hit selection, and fallback dominance. All target rows stay locked.
Explicit no-acquisition is a whole-polygon negative certificate, not a sampled
failure. Parsing uses exact rational strings/integers, not floats.

The global bounded/simple/full-dimensional class is a theorem INPUT. A local
successful basis is not a new proof that every unseen original vertex is simple.
Returned original edges are independently checked regardless. For facet-count
interpretation use irredundant ORIGINAL rows; no extension-row substitution.
In dimension2 a whole original polygon is explored. The accurate claim is no
precomputed ambient graph, not that no whole graph can ever coincide with a face.

There is no new Lean module, compile/axiom audit, Actions gate or Prove2Me verdict.
The tests/JSON checker are not Lean-extracted. Existing formal results are not
resubmitted or weakened. Next progress needs a polynomial compression of the
retired-facet-subset account, a stronger global selection theorem, or another
route construction for arbitrary high-dimensional carriers. More fixed-radius
neighbors alone do not establish such a result.
