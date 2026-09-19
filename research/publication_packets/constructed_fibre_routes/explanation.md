# Construct a short fixed-core fibre route of actual edges

## Statement

Let P be the convex hull of a finite core point list. Let Q be a Minkowski
sum of finitely and injectively listed factor hulls S_i with k_i listed points.
Two supplied endpoint objectives strictly expose the SAME core point o, and
respectively expose chosen points p0_i and p1_i in each factor.

The theorem constructs N and a path from o+sum p0_i to o+sum p1_i with

    N <= sum_i(k_i-1).

Every path point belongs to the FULL sum P+Q and has a decomposition o+q with
q in Q, so the core coordinate stays fixed. Every transition is nonstationary
and an actual exposed edge of P+Q. Its supporting functional and equality of
the ENTIRE global supporting slice with the segment are conclusions.
The number of core points is NOT charged in this bound.

No generic objectives, ordered events, interval winners, common wall maxima,
stationary compression, path, support-face certificate, no-revisiting condition
or transition count are assumed. The finite presentations, exposed core point
and exposed endpoint tuples are genuine inputs. Empty factor families,
singleton/lower-dimensional factors, redundant distinct listed points and zero
steps are included. Endpoint membership is explicit even for N=0.

This is classical finite Minkowski/normal-fan geometry formalized at a concrete
missing interface. Related primary context: Deza and Pournin, *Diameter,
decomposability, and Minkowski sums of polytopes*, arXiv:1806.07643v1, common-
objective face decomposition and fibre lemmas. No historical novelty or general
Polynomial Hirsch result is claimed.

## Coordination and exact reused source

Another agent opened #243 for the scalar sequence while this continuation was
preparing the same obligation. The independent scalar candidate was WITHHELD:
no duplicate scalar PR, problem registration or proof submission was made.
The new geometric proof uses that agent's exact repaired, Lean-verified source
from proof head65e683ec0b19dc98932b6e62782976dc3de3385e, run34804405107.

The downloaded archive10332617541 has independently recomputed SHA-256
6a1c43065b1bbbfca525d22f0099f8645f46f7a8b0e3efa96185a9a27c76480b.
Its solution hash is
c26a8737a7d2b3c697b9b5a197f0733b3129f2ad60b16071adb6f15e3a5ec8dc.
Only its public helper declaration is renamed when making it an importable
module. All mathematical proof bodies are unchanged. The other agent subsequently completed its publication and merged #243.
Theorem8b5a47c4-8e01-4823-9014-ed546f69991f, submission
cf94f560-6133-4340-867d-36624f0e82db, is recorded ACCEPTED/live Proved on that
PR. This does not establish verification of the new geometric adapter.
The new packet contains the actual proof, not an assumed child theorem.

#243 already reuses accepted #239's slope-rank count. Accepted #242 supplies
endpoint-preserving generic objectives. The compiled Minkowski support/crossing
modules supply the entire exposed-segment construction. They are included as
actual proofs in the Mathlib-only standalone packet. Their existing repository
source files are not overwritten by local dependency copies.

Three importable module candidates are included in the companion bundle:
PolynomialFiniteAffineSequenceCore (the verified #243 source under a reusable
name), PolynomialFiniteEnvelopeSequence (a small output-interface adapter), and
PolynomialConstructedFibreRoutes (the geometric construction, strict comparison
preservation, and full-core fibre theorem). They are not separately committed
nor module-build-verified in this packet PR. The standalone publication source
contains their full proof bodies and is the exact object submitted to the gate.

## 1. Reuse the constructed scalar itinerary

Each factor's score along a generic objective line is a_p+t*b_p. The finite
set of pairwise roots divides [0,1] into open cells. The verified #243 theorem
constructs their ordered samples and unique maximizing tuples, proves closed-
cell persistence and endpoint agreement, removes stationary states, and retains
an actual common wall between each neighboring retained sample.

Its compressed sequence has at most sum(k_i-1) transitions, by the accepted
slope-rank argument. These data are outputs; the geometric theorem does not
assume a sampled sequence is complete or that deleting stationary states
preserves arbitrary adjacency. The small adapter only chooses its existing
wall witnesses and repackages the verified fields.

## 2. Genericity from actual finite point differences

The geometric proof forms ALL within-factor differences of distinct listed
points. Applying #242 produces objectives that preserve the requested endpoint
winners, separate those differences at the endpoints, and ensure that any
simultaneously vanishing nonzero differences along the interpolating line
are parallel. This is not a numeric genericity assumption.

It also includes arbitrary shared strict comparison vectors in the finite
perturbation conditions. A convex combination of the two resulting strict
inequalities stays strict at every interior wall. For the fixed core these
vectors are core(q)-core(o), for every other listed core point q.
Thus every wall objective continues to expose the SAME core point o.

## 3. Wall winners yield whole factor support segments

The scalar itinerary supplies strict left/right winners and both maximizing
wall endpoints. The compiled crossing theorem uses the parallel-tie property
to show every wall-maximizing listed point lies BETWEEN those endpoints. It
extends the finite checks to the entire convex hull. All factor displacements
have a consistent orientation; at least one is positive, so they cannot cancel
when summed. The full Q support slice is a nondegenerate segment.

This proves actual ordinary edges, not merely feasible endpoints, potential
edge directions, or a circuit move. Independent simultaneous ties such as a
square diagonal are explicitly outside the crossing argument and rejected
by the independent test.

## 4. The edge is in P+Q, not only in Q

At a constructed wall h, strict core comparisons prove

    h(x)<=h(o) for every x in P, with equality only at o.

This is derived over the entire convex hull from the finite point inequalities.
For z=x+y in P+Q, the equality

    h(z)=h(o)+h(path_Q(j))

forces equality separately in the two support bounds. Therefore x=o and y
belongs to the Q segment already proved. The entire FULL supporting slice is

    o+[path_Q(j),path_Q(j+1)]
      =[o+path_Q(j),o+path_Q(j+1)].

The reverse inclusion is also proved. Translation preserves nondegeneracy,
and a supporting slice is extreme, giving actual Hirsch adjacency in P+Q.
This avoids the earlier invalid route-transfer shortcut: it does not project
an arbitrary extension edge or infer adjacency from vertex correspondence.

## Scope relative to a full core walk

The theorem provides the finite fixed-core fibre leg required between selected
bridge endpoints. Accepted #240 supplies genuine exposed core-edge bridges.
The written aggregate target for a core route of L edges is

    L+(L+1)*sum_i(k_i-1).

This packet does not claim that all arbitrary-core endpoints/bridges and fibre
legs have already been assembled into that final theorem. Their common endpoint
choices and actual model bindings must still be provided and composed. Nor does
it show that every high-dimensional H-carrier has a representation with small
core-route cost and small factor point count. The original facet count cannot
be replaced by an unrelated extension's row count.

## Exact regression

    python3 scripts/test_finite_envelope_sequence.py

The independently implemented scalar reference intersects each affine line's
dominance inequalities to find winning intervals, rather than trusting the
root-sort constructor. Final tests:355 score systems,1369 raw intervals,
285 retained transitions,729 removed stationary transitions,42744 comparisons.

68 small geometric systems have177 actual exposed edges, checked against3749
complete finite point-sum comparisons. The full-core extension is independently
checked against26201 complete core-plus-factor point-sum comparisons, with1050
strict core wall comparisons.525 additional shared strict-comparison checks pass.
Simultaneous parallel changes, redundant collinear points, empty factor families
and zero-step cases are included.

Large cases have201 listed core points and16/32/64 triangular factors in
dimensions8/12/16. They construct21/43/97 edges with bounds32/64/128. The core
point count is not added to those bounds. All32200 core wall comparisons are
checked, plus component support identities, without enumerating the complete
point-tuple products. The numbers3^16,3^32,3^64 are RAW tuple counts, not asserted
numbers of distinct vertices. Thirteen malformed/unsupported cases fail.
These finite exact tests are not Lean extraction, JSON verification, shortest-
path proofs or a uniform runtime/bit-complexity theorem.

A local test-development bug consumed a generator in vector summation; it was
fixed before the final suites and clean replay. Only actually completed final
counts are recorded. The formal result rests on the proof gate, not extrapolating
these numerical tests.

## Verification boundary

Local Lean/Lake is absent; DNS and a public toolchain download failed. This
packet is prepared for one final pinned compile/axiom/publication gate. Source
inspection and exact Python tests are NOT compilation. The public statement
inlines all support/adjacency/set definitions and its preamble contains only
Mathlib import/open commands, preventing local-definition type-identity errors.
Five new declarations are printed for transitive axiom auditing.

#241's separate existing publication comment was blocked before posting; no
alternate trigger was attempted and that bounded-image source is NOT included
here. #243's scalar work was coordinated and reused, not resubmitted. #238 and
retired/reserved #210 are not modified or triggered. Preserve the actual run
state, exact source hashes and authenticated verdict; do not claim acceptance
from merely queued or compiled status or duplicate any pending registration.
