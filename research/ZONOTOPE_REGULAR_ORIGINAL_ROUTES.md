# Turning the accepted zonotope sweep into a bounded original-edge walk

The candidate extends the accepted sweep theorem to a complete ordered vertex
walk, but its first Lean compilation failed at four elaboration sites. The full
result is not yet Lean verified or accepted. This note describes the written
mathematical argument; the handoff records the exact compiler state.

Let Z=sum_i[0,w_i] for any m real vectors and take linear objectives f,g nonzero
on all nonzero generators. The accepted theorem constructs a target perturbation
k preserving g's whole support face and an exact event set T in(0,1), |T|<=m.
Its objective sweep is h_t=(1-t)f+t*k. Each event exposes a whole nondegenerate
original edge; other times expose singleton vertices. Zero and dependent
representations are allowed, not silently replaced by independent coordinates.

Sort T together with0 and1. Consecutive entries delimit chambers containing no
event. Select a midpoint in each chamber and let its vertex be the sum of those
w_i whose objective evaluations are positive. Coefficient saturation and
regularity prove the entire maximizing face is that singleton, so the point is
an actual extreme point rather than an arbitrary Boolean-cube image.

For a generator not tied at a boundary, its continuous affine evaluation cannot
change sign between a chamber sample and that boundary without another zero.
The exact event characterization excludes that zero. Hence the chamber vertex
also maximizes at the boundary. This proves membership in the WHOLE event face,
not just agreement of endpoint objective values. The same argument identifies
the initial and final chamber vertices with the requested f/g faces.

A nonzero generator tied at an event has opposite nonzero signs at the two
adjacent chamber samples. Its weighted affine identity is

    (b-c) h_a(w_j) + (c-a) h_b(w_j) = (b-a) h_c(w_j) = 0,

where a<c<b. If the two saturated points were equal, saturation under h_a would
force the representation chosen by h_b to use the same coefficient on w_j.
The opposite signs contradict that equality. This distinctness lemma obtained
a standard-only transitive axiom report in the failed driver; the complete
packet and other printed dependent results did not pass.

Both adjoining chamber vertices lie on the original event segment. An extreme
point of the ambient set on a feasible segment is an endpoint. Thus these two
distinct extreme points are precisely its two endpoints, and the whole original
exposed edge joins them. There is one transition for each distinct event, yielding
the intended bound L=|T|<=m. No schedule, chamber enumeration or adjacency is a
premise. The implementation derives the finite mesh, including its endpoints
and the no-hidden-event intervals, using the pinned finite-set order embedding.

The theorem keeps regular objectives as explicit input. It does not yet construct
regular objectives for arbitrary requested zonotope vertices. It counts segment
generators, not original polytope facets, and supplies no polynomial completion
budget in original H data. The result formalizes classical zonotope geometry,
not a new optimal diameter theorem or unrestricted Polynomial Hirsch. No
shortestness, numerical score monotonicity or verified executable parser is
claimed. The exact-rational complete-walk tests and the uncompiled repair patch
are useful evidence and implementation aids, not substitutes for full Lean
compilation and the authenticated platform verdict.
