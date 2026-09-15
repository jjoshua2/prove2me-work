# Continue from original-facet segments without reopening classical claims

Read the LIVE STATUS, main SHA and PR queue. This contribution implements the
classical Adiprasito--Benedetti construction from original rational H queries,
not a new proof of the flag Hirsch theorem. It makes no new Lean/Prove2Me claim.

Production input is only A,b,start,target, in the simple bounded full-dimensional
original-facet class. No vertex graph, facet graph or incidence catalogue is
supplied. Every constructed link graph is backed by exact original feasible or
strict-dual intersection witnesses. The output has original inverse and maximal-
ratio edge certificates. The consumer replays BFS/recursion but does no LP or
geometric search. Do not call it free of all graph computation.

Raw length obeys L=distinct_seen-d+facet_reentries. The classical flag guarantee
makes the last term zero; generic inputs are not assumed flag. The polynomial
LP-query count in the note is CONDITIONAL on short output/flagness. It is not
a polynomial Bland-pivot or runtime theorem. The first reentered facet gets a
searched missing-triangle witness in an actually visited link; if diagnostic
caps are reached, that is incomplete diagnosis, not a flagness verdict.

The separate facet_reentry_repair.py keeps the segment's endpoints and replaces
an actual absence interval by an independently audited shorter #253 route in
the shared facet. It does not keep the old conservative-segment constraint.
Every accepted splice strictly reduces edge count. It is not asserted to remove
all reentries or obtain a shortest/uniformly polynomial route.

CRITICAL CLASSICAL LIMIT: Labbe--Manneville--Santos arXiv1510.07678 construct
Hirsch polytopes with facet pairs for which EVERY combinatorial segment is
exponentially long. A different label ordering within this family is not a
universal fix. This is a known theorem, not a new experiment or an open target
for a false polynomial bound. Do not spend a formalization cycle proving it.

The precise new route-local input is the original-row failure certificate
S+w+p,S+w+q,S+p+q feasible but S+w+p+q empty, involving reentered facet w.
The written localized AB induction explains why this is the correct defect
to inspect. It does not prove distinct charging of defects or a bound on the
cost of successful/failed repairs. Those are the remaining quantitative tasks.

Reproduce:
    python3 scripts/test_original_facet_segments.py --stage flag
    python3 scripts/test_original_facet_segments.py --stage nonflag
    python3 scripts/test_original_facet_segments.py --stage large

Construct:
    python3 scripts/original_facet_segments.py input.json --output segment.json
    python3 scripts/facet_reentry_repair.py input.json segment.json --output repaired.json

The test references reconstruct small graphs independently and explicitly count
nonshortest, reentered and over-m-d outcomes. Do not advertise the new component
as dominating #253. Large cube and corridor instances have exact special-family
provenance; no enormous full vertex graph is silently enumerated. Test failures
from malformed certificates are distinguished from geometric infeasibility.

Existing exact_farkas_lp.py, simple_tangent_policy_audit.py and two_face_acquisition.py
remain byte-identical. The large test imports the existing #254 corridor constructor
and accounting dependency unchanged. No accepted proof, pin, workflow, permission
or secret is changed. Full generated reports/fixtures live in the conversation
bundle and regenerate; the committed execution summary labels itself derived.

The open conjecture needs a bound for arbitrary high-dimensional carriers. This
is a certified alternative route component and repair experiment, not that bound.

Actual final small-suite comparison: 1,424 pairs, 3,404 raw edges, 3,391 repaired,
3,389 unchanged #253, 3,360 shortest. The 13 observed reentries all have checked
missing triangles and all 13 are repaired, but 31 nonshortest outputs remain.
The 16D cube run has 16 actual edges, 12,862 intersection answers, 279 LP calls,
and 586 internal pivots; no 65,536-vertex graph is enumerated. The four known
stacked-polar corridors give 4/7/9/15 edges versus #253's 4/7/11/17. The whole
three-stage suite reproduces in a fresh dependency directory, with all fields
other than timing and all generated fixture bytes identical. Read the execution
summary and replay hashes instead of interpreting favorable examples universally.
