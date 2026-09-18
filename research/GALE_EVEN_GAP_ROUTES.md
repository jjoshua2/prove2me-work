# Selected finite-set route from the literal even-gap predicate

Fix m and two selected subsets S,T of Fin m, each of size d. For each pair of
unselected labels i<j, require an even number of selected labels strictly between
i and j. This is exactly the finite-set condition occurring in #302's public
statement. The source here does not assume or import #302's numerical proof.

## Derive the missing enumeration and phase

Enumerate H=univ minus S increasingly as h_0,...,h_(r-1), with r=m-d. Let C_i be
the number of selected labels below h_i. Every label below h_i is either selected
or one of the i preceding holes. Therefore

    C_i+i=h_i.

For two holes h_i<h_j, their selected-prefix difference is exactly the selected
gap count. Gale evenness says C_j-C_i is even. Thus all C_i have the same parity,
and h_i has parity b+i for a single b in {0,1}. Conversely the indexed alternating
phase forces every C_j-C_i even. Both directions include the vacuous empty-hole
case; neither a positive complement size nor an ordered enumeration is supplied
as a public assumption.

The Lean proof uses a finite interval partition and the cardinality of Finset.Iio
to derive the rank identity, then explicit prefix/gap partitions and natural
modular arithmetic. Mathlib orderEmbOfFin provides the increasing bijection onto
the actual complement, not a separately supplied list of suitable labels.

## Reuse the accepted short schedule

Apply the accepted #306 alternating-complement route to those derived natural
value lists. It left-packs each phase in at most r nontrivial replacements,
crosses between phase anchors by at most one replacement, and reverses the
second packing. Its compression theorem removes stationary transitions. This
is the already accepted 2r+1 construction, not newly reproved short-route logic.

Each intermediate set is decoded into Fin m only after its labels are known
in range. Exact cardinality, complement and intersection identities transfer
its endpoints and exchanges. Applying the reverse phase implication gives the
literal selected-set even-gap predicate on every intermediate selected set.
The resulting statement is

    length <= 2*(m-d)+1,
    p(0)=S, p(length)=T,
    every p(t) has size d and even selected gaps,
    successive p(t) differ and intersect in exactly d-1 labels.

The inequality d<=m follows from the actual selected-set cardinality, rather than
being a hidden premise. Empty/full universes, d=0, d=m and equal endpoints are
included. There is no modulo reduction that could turn out-of-range integers
into apparently valid original labels.

## Scope and remaining formal composition

This is the finite-set bridge needed to pass the literal #302 catalogue to #306
without supplying an alternating enumeration or a bounded path. It is not a new
numerical root-sign theorem, an actual-polytope route by itself, or a solution to
Polynomial Hirsch. The separately owned parity-to-numerical catalogue must first
have its complete Lean proof verified; only then can the exact vertex and original
exposed-edge interfaces be composed with this finite route. No original-edge
geometry is assumed in the present theorem to bypass that remaining work.

Neither shortestness, global path injectivity, nonrevisiting, target-label locking
nor numerical score monotonicity is claimed. Repeated vertices and target-label
losses occur in the concrete packing policy. A short walk is enough for its
stated bound, but stronger policies need additional arguments. Classical
Gale-evenness and packing constructions are credited, with no priority or
best-known-diameter claim.

## Supporting computation is distinct from Lean

The exact tests independently evaluate literal selected gaps on all 2047 subsets
through m=10, not just on purported legal cases. They obtain 596 legal and 1451
illegal sets, check 9217 rank-balance and 18943 gap-partition identities, and
construct 13724 endpoint routes with 77806 nontrivial exchanges. The 91530 visited
selected sets satisfy the literal predicate. There are 6072 opposite-phase pairs,
3651 vertex-repeating routes and 11264 target-label-loss routes.

Three larger cases (m,d)=(65,33),(127,95),(257,193) have lengths 33,63,127 below
bounds 65,65,129. Large full graphs are not enumerated. Sixty-nine saved records
audit with the packing producer disabled. Seven invalid endpoint/path controls
are rejected. The full report and fixture replay byte-for-byte in a separate
two-script workspace. The prior packing script is unchanged. These tests are
not an all-size proof by sampling or formal verification of Python/JSON.

Read GALE_EVEN_GAP_HANDOFF.md and the raw run evidence for the actual Lean and
platform status. An issued PR comment or exact arithmetic report is not an
ACCEPTED verdict. No existing source, pin, workflow, actor allowlist, duplicate
check, credential separation or reserved #210 is modified.
