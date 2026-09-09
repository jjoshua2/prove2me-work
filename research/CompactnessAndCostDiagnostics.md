# Compactness and cost diagnostics for the clipping theorem

Supplement to `FullSimultaneousClipping.md`, 2026-09-09.
This document and the accompanying exact diagnostic do not change any Lean
source. The script was run locally over exact rationals. It is not a Lean hull
formalization or a Prove2Me publication.

## Compactness cannot just be omitted

The proposed full-diameter bound without compact outer Q is false already in
one dimension:

    Q = [0,infinity), P = Q intersect {x <= 1} = [0,1].

Choose centre o=0, which strictly satisfies the added cut. Q has one extreme
vertex, 0, so `DiamLE Q 0` holds. The final cut face is {1}, whose diameter is
zero. But P has the edge from 0 to 1 and diameter one. Consequently

    diam(P) = 1 > 0 + 0 = diam(Q) + diam(final cut face).

There is no maximizing outer vertex at or beyond the new endpoint 1. This is
exactly where the compactness-based attachment proof fails. The example is
an elementary mathematical counterexample to dropping a hypothesis, not a
counterexample to Polynomial Hirsch. The existing repository's unbounded
single-cut results include an extra charge; do not replace them by the compact
formula without that correction or another genuine condition.

The separate surviving-endpoint walk theorem does NOT assume compact Q. The
example does not violate it, because the final endpoint 1 was not a Q vertex.

## Exact one-row relaxation costs on the old Dantzig witnesses

Run:

    python3 scripts/test_compact_relaxation_costs.py

The script uses the exact centred polar coordinates from PR #50's regression,
then deletes each row in turn. All normals of the original centred polar sum
to zero. For a bounded relaxation it produces strictly positive rational row
weights whose weighted normal sum is zero, and verifies full normal rank.
Those two facts force the recession cone to be {0}: pairing any recession
vector with the positive weighted sum forces every row pairing to vanish,
then full rank forces the vector to be zero. For an unbounded relaxation the
script instead produces a concrete nonzero vector satisfying every homogeneous
inequality. A failed search is never silently labelled bounded or unbounded.

Once compactness is certified, exhaustive rational vertex enumeration and exact
common-tight-row ranks reconstruct the graph. BFS computes the outer diameter
and the diameter of the FINAL removed-row face in the original parent.

### Four-dimensional witness

The original parent has 14 vertices and diameter 4. Deleting row 3 is unbounded;
all seven other one-row relaxations are certified bounded with outer diameter 3.

| Deleted row | Final cut-face cost | Clipping bound |
|---|---:|---:|
| 0, 1, 4 | 3 | 6 |
| 2, 5 | 2 | 5 |
| 6, 7 | 1 | 4 |

Thus the compact clipping theorem recovers the SHARP parent diameter through
either simplex-facet deletion 6 or 7. In particular the row-6 case does not
need the false arbitrary-facet 2-face bridge that this same witness refuted.
This is a finite application, not a proof that a suitable deletion always exists.

### Five-dimensional witness

The original parent has 40 vertices and diameter 5. Every one-row deletion is
certified bounded with outer diameter 4; every final cut facet has diameter 4.
The bound is therefore 8 for every such deletion, not the true value 5.

This confirms a substantive remaining limitation: choosing among single-row
relaxations and charging each whole final face by its diameter does not recover
the sharp route on this example. It does not refute polynomial charging or the
use of several removed rows, selected face subregions, or order-sensitive
amortization. It does show that closing the portal/existence gap alone should
not be confused with obtaining sharp or polynomial cost control.

The diagnostic emits complete rational positive-weight or recession-ray
certificates. These finite computations are separate from the general
kernel-checked clipping implication and make no literature-novelty claim.
