# Constructing the finite crossing itinerary

## Exact new result

For each finite factor dictionary, consider real scores a_i(q)+t*b_i(q). The intercepts within each factor are distinct, and p0,p1 are prescribed unique winners at t=0,1. The theorem constructs increasing interior samples, their unique winning tuples, and intervening wall parameters. Both neighboring tuples maximize every factor at their wall. Adjacent retained tuples differ, and the number N of transitions satisfies N <= sum_i(k_i-1).

No crossing list, sorted parameter sequence, interval winners, wall-maximizing condition, stationary-compression result, or desired length bound is a premise. These were the finite sequence obligations remaining after accepted #242. The result permits simultaneous ties: it is deliberately a scalar envelope theorem, not a claim that a higher-dimensional tied face is its diagonal edge.

## Proof

1. List the formal crossing values (a_i(q)-a_i(p))/(b_i(p)-b_i(q)) of every within-factor pair. Keep the values strictly between 0 and 1 and insert the two endpoints. Formal values from zero denominators are harmless: every genuine tie between distinct indices has a nonzero denominator because the intercept map is injective. The ordered finite set is constructed with Finset.orderEmbOfFin at the committed Mathlib pin.
2. Between adjacent entries there is no crossing. At the midpoint of each interval, choose the maximum of each finite score list. A tie there would yield an omitted crossing, so that maximum is unique.
3. An affine scalar negative at a midpoint and with no zero in the open interval is negative throughout the open interval and nonpositive on its closure. A contrary sign would give an explicit intermediate affine root. Therefore each midpoint winner remains the unique winner throughout the chamber and remains a weak winner at BOTH boundary points.
4. At a shared boundary the winners on both sides are weak maxima. Comparing them in both directions proves equality of their scores. At 0 and 1, prescribed strict endpoint uniqueness identifies the first and last tuples. This does not assume endpoint membership from a zero-step edge certificate.
5. A generic finite-sequence induction deletes stationary repeats. It retains increasing sample times, the endpoint states, every sample property, and the transition relation. A retained sample is allowed to move earlier when its state repeats; the geometric state is unchanged. A separate affine-root calculation proves that every retained common wall still lies strictly between the two retained samples.
6. Apply the already-accepted #239 slope-rank argument: a changed unique affine maximizer at increasing samples has strictly larger slope. Summed finite slope ranks therefore increase at every retained transition and are bounded above by sum_i(k_i-1). That proof body is reused with namespace/declaration renaming, not presented as a new count lemma requiring independent verification history.

Singleton dictionaries are allowed. Empty factor index sets give the empty tuple and N=0. The supplied endpoint tuples ensure individual dictionaries are nonempty. If both endpoint tuples coincide, affine comparisons imply there is no real winner change; stationarity compression covers this case without asking for an edge. No condition on the separation of crossing times is needed.

## Connection to actual ordinary edges

For geometric dictionaries v_i, set a_i(q)=f(v_i(q)) and b_i(q)=g(v_i(q)). Accepted #242 constructs suitable endpoint-preserving objectives whose nonzero within-factor differences have nonzero initial evaluations and no independent simultaneous ties. Its injectivity consequence supplies the intercept assumption here. In the affine interpolation convention (1-t)f+t*h, use g=h-f.

This theorem supplies the strictly maximizing left/right samples and BOTH wall-maximal tuples required by the compiled HirschEnvelopeCrossing.affine_crossing_exposed_edge theorem. That module derives the entire supporting slice, summed-endpoint nondegeneracy and Hirsch.Adj when the ties are parallel. The scalar theorem does not itself supply this parallel-ties hypothesis: without it a triangle can have a simultaneous three-way tie and its selected transition is not automatically the intended ordinary edge.

The remaining geometric adapter must instantiate #242 on actual indexed point differences, convert the finite dictionary functions to membership in their Finsets without introducing duplicate labels, apply the crossing theorem to every retained transition, handle translation/core-fibre membership, and concatenate with #240's actual bridges. Controlled low-cost decompositions for arbitrary high-dimensional carriers remain a separate mathematical problem. This packet is not an unconditional Polynomial Hirsch proof or an assertion that the complete geometric lift is already formalized.

## Verification boundary and provenance

The standalone source imports Mathlib only and uses the repository pin Lean4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. The count proof is reused from research/publication_packets/simultaneous_envelope_edges/solution.lean, Git blob c6ea054c19c061539eba3f19427fd9ec6ef17336. The new root ordering, boundary, compression and wall chronology proofs are in this packet.

Local Lean/Lake was not available in this runtime, and direct toolchain-network access failed. Exact rational tests and source inspection are not Lean compilation. Eight explicit axiom printouts cover the new proof chain. A prepared exact-head hosted gate must determine compilation and the permitted transitive axioms before publication. Do not infer acceptance from this explanation or from Python results.

The independent rational test suite checks 211 cases, 319 retained transitions, 1866 raw cells, 1336 discarded stationary cells, 16093 sample/wall comparisons, 77922 independent closed-cell boundary comparisons, and 11 rejected malformed certificates. It includes no factors, singletons, entirely stationary paths, unused crossings, parallel/simultaneous changes, endpoint ties among losing scores, and crossing gaps down to 2^-240. The Python producer and verifier are not Lean-extracted; their execution is separate evidence and does not kernel-certify arbitrary JSON.

Classical affine-envelope reasoning underlies the construction. The contribution is completion of this explicit formal interface in the project, not a historical novelty claim.
