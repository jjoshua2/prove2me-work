# Accepted original-image edge certificate: next use, not another reproof

PR246 supplies the accepted packet projected_face_edge_certificate. Read its
accepted-evidence.md and publication-receipt.json; the old prepared manifest
and first-gate diagnostic are historical, not unfinished proof status.

The theorem checks the original H-system and a linear map G. The full exposed
preimage face may have high dimension or be unbounded. Its image is an ordinary
edge once three finite identities hold: a positive selected-row exposure;
a rank-one image identity modulo the selected rows; and sharp endpoint bounds
using nonnegative original inequalities plus unrestricted selected equalities.
The entire image slice and its actual Mathlib IsExtreme property are proved.
Source adjacency and source vertexhood are deliberately absent.

A simple exact instance is [0,1]^2 x [0,infinity), projected onto [0,1]^2.
Lifts (0,0,5) and (1,0,7) are not source vertices or adjacent. Selecting the
row -x2<=0, using image normal (0,-1), coordinate phi=x1 and residual vector
(0,-1) gives Gz=phi(z)*(1,0)+(-x2)*(0,-1). The endpoint bounds are the two
original x1 inequalities. The whole half-infinite preimage strip therefore
maps onto exactly the bottom edge. This instance is a rational worked
certificate, not a separately kernel-evaluated public theorem.

Reproduce the complete exact suite:

    python3 scripts/test_projected_face_certificate.py

It writes research/PROJECTED_FACE_EDGE_TESTS.json and regenerates the five
full fixtures in fixtures/projected_face_examples.json. The latter fixtures
and original artifact ZIPs are in the conversation bundle. The producer uses
exact elimination but the independent auditor uses only arithmetic identities.
It still works when the search routines are replaced by raising stubs. This
software is not Lean-extracted and its JSON parser is not formally verified.

For the root problem, the remaining obligation is to CONSTRUCT a sequence of
these actual image edges with polynomial total cost in the ORIGINAL IMAGE
facet count. Neither a compact representative nor a short source graph path
establishes this. The old Klee--Minty projection regression remains a valid
negative control: source edges may project to interior chords. The present
certificate correctly allows a whole high-dimensional preimage face when its
image really is one-dimensional; it does not claim all source edges pass.

#244 owns the fixed-core Minkowski fibre route and its concatenation interfaces.
Use its live proof status and exact geometric hypotheses rather than creating
a competing copy. #241 remains the independently blocked bounded-representative
packet. Do not transfer #246's audit or acceptance to either one. No source,
workflow, pin, permission or secret-separation change to those lines was made.
