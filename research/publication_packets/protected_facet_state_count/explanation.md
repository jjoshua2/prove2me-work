# Positive finite counting bound for protected facet intervals

## Exact formal target

The theorem is `Hirsch.protected_facet_state_count`. Let V be a finite set of
labels, B a finite exception set, and P a sequence of n distinct d-element
subsets of V. Assume that, for each label outside B, its occurrences in P form
an interval: whenever it occurs at indices i and k, it also occurs at every
j between them. The theorem proves

    n <= (|V|-d+1) * 2^|B|.

For ANY finite registry C containing all actually occurring exceptional
signatures P(i) intersect B, it additionally proves BOTH

    n <= (|V|-d+1) * |C|,
    n <= sum_{S in C} (|V minus B| - (d-|S|) + 1).

Subtractions in the formal statement are natural-number truncated subtraction.
The theorem includes n=0, d=0 and an empty exception set. It does not require
that irrelevant labels of B be inside V; removing such labels only improves
the interpretation of the resulting bound.

These are state counts. For a nonempty simple route with L edges, n=L+1, so
the first conclusion gives L <= (m-d+1)*2^k-1 for m=|V| and k=|B|. The registry
conclusions can be substantially sharper if known incompatible exceptional
subsets are excluded. A registry need only cover the signatures of this route;
it need not classify all geometric vertices or all possible signatures.

The public target's preamble is only `import Mathlib` and an `open scoped
BigOperators`. Every custom helper is confined to the solution source, and
its public signature is literally extracted into problem.json. The target
uses only Mathlib types and predicates, with no copied local structure whose
identity could differ on the platform.

## A direct injective encoding

For time i define

    Seen(i) = union over j<=i of (P(j) minus B),
    Retired(i) = |Seen(i) minus (P(i) minus B)|.

Seen contains the protected labels encountered so far. The second quantity
counts those no longer active at time i. Every such label is outside the
current complete state P(i), so

    Retired(i) <= |V minus P(i)| = |V|-d.

A sharper signature-specific bound is

    Retired(i) <= |V minus B| - (d-|P(i) intersect B|).

The proof now uses the explicit map

    i |-> (P(i) intersect B, Retired(i)).

It proves this map is injective, rather than assuming that each signature is
visited only a bounded number of times. Suppose i<=j have the same encoding.
Their current protected-set sizes agree, because both complete states have
size d and their exceptional intersections are equal. The identity

    |Seen(i)| = Retired(i) + |P(i) minus B|

therefore gives |Seen(i)|=|Seen(j)|. Seen is increasing in time, so those finite
sets are equal. A protected label active at j consequently occurred at some
k<=i. Its interval property forces it to be active at i too. Every exceptional
label active at j is active at i by the common signature. Hence P(j) is a
subset of P(i). Equal size makes these states equal, and the stipulated
injectivity of P yields i=j. The reversed index order is symmetric.

Thus the whole visited sequence injects into

    powerset(B) x {0,...,|V|-d},

or into C times that same counter range. Counting either finite product gives
the first two conclusions. For the weighted conclusion, use the finite sigma
set whose fiber over S is the range of size

    |V minus B| - (d-|S|) + 1.

The same injective map lands in these fibers. Summing their finite cardinalities
proves the third conclusion. The proof uses no geometric existence theorem,
no supplied bound per signature, and no count of all vertices of a polytope.

## Relation to the current Polynomial Hirsch work

This is the positive FINITE COUNTING CORE of the conditional route bound in
PR #259, research/DEFECT_CONFINEMENT.md. That research separately argues that
confining missing triangles in appropriate recursive links protects all labels
outside B for a particular combinatorial-segment construction. The current
packet does NOT formalize that geometric implication or the classical
Adiprasito--Benedetti construction. Its interval premise is explicit, rather
than silently assumed true for arbitrary polytopes.

For an actual simple-polytope route, the d labels can be its active original
facets, and deleting complete-vertex loops yields distinct states. This packet
does NOT perform that deletion, prove original-edge adjacency, or handle a
nonsimple vertex by pretending its active set always has size d. Those are
separate interfaces. The count is more general than an edge-walk result:
adjacency is unnecessary once its stated finite-set hypotheses hold.

A fixed k gives a linear-in-facet-excess bound; k=O(log m) would give a polynomial
bound. The theorem does NOT establish either regime for arbitrary carriers.
A polynomial registry C would similarly suffice under protected intervals,
but such a registry is not constructed here for general polytopes. Nor is a
bound on a delivered loop-erased route automatically a bound on the work of
constructing a longer raw route or recognizing its interval property.

This contribution is distinct from ACCEPTED #281's stellar-persistence LOWER
count. That theorem remains unchanged and is not resubmitted. The present
positive theorem counts actually visited states in a route, rather than the
size of a completed refinement. It does not contradict the full-refinement
obstruction or establish the Polynomial Hirsch conjecture.

## Why the hypotheses matter

Without protected intervals, the three distinct size-two states

    {0,1}, {1,2}, {0,2}

on V={0,1,2}, with B empty, violate the asserted two-state upper bound. Their
last two states have the same retired-count encoding. Without distinctness,
repeating a singleton state also violates the one-state bound for m=d=1.
The formal proof therefore includes both assumptions explicitly. Uniform state
size and containment in the finite original ground set are also checked.
The test suite rejects an allowed-signature registry that omits a visited state.

No hypothesis here is a statement that the desired global diameter is small.
Nevertheless, establishing these hypotheses with controlled parameters on
arbitrary carriers is a substantive separate problem, not something the
counting theorem proves by itself.

## Validation and actual compilation boundary

The standalone finite test exhaustively considers 33,790 candidate sequences
and exception sets on ground sets of up to four labels. It verifies all 9,502
valid cases, including 6,480 with exceptional-label reentries and 2,808 where
ordinary one-facet-exchange adjacency does not hold (nor is it needed). There
are 400 additional random valid exchange paths, five empty/boundary cases and
five rejected malformed-hypothesis controls. The public statement is checked
byte-for-byte against the solution's final signature.

These counts are exact Python checks of the mathematical encoding, NOT Lean
verification, and no abstract path is claimed to be a polytope realization.
The report and small worked examples are included with a standard-library-only
reproducer. No prior geometric or solver result is relabeled as a new test.

At preparation, no Lean/Lake executable was found in the local environment,
and the toolchain host could not be resolved. A search for an available external
Lean compiler integration returned no matching capability. The user explicitly
asked for a proof-bundle submission attempt, so the existing PR-comment workflow
is used as one prepared pinned final gate. Do not interpret this explanatory
file or the finite tests as a completed compiler/axiom/platform verdict.
Record the actual gate result independently. No toolchain, workflow, permission,
credential, or trusted-publisher secret separation is changed.

    /prove2me publish research/publication_packets/protected_facet_state_count

The solution includes axiom printouts for the key injection, weighted registry
bound, uniform registry bound, powerset bound, and final theorem. Proof admission
checks are source hygiene only; the actual Lean compile/audit is authoritative.
A running or pending registration must not be duplicated.

## Provenance

The counted conditional route mechanism appears in this repository's PR #259,
research/DEFECT_CONFINEMENT.md. The present proof uses a direct cumulative-label
encoding instead of a supplied per-signature enumeration bound. The finite
argument is proved explicitly; no historical-priority claim is made.
Mathlib provides standard finite-set union, difference, product, sigma-sum,
and cardinality identities under the unchanged committed environment:
Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
