First prove directly by a finite perturbation that any direction
annihilating all tight rows must vanish. For inactive rows choose positive
step sizes controlled by their slacks and take a finite common lower bound.
Both signed perturbations are feasible, and extremality forces the direction
to be zero. Consequently the orthogonal complement of the tight-normal span
is zero, so the tight normals span all of R^d. Extract an independent spanning
subfamily, identify its cardinality with d through its basis, and reindex by
Fin d. The original row index map is injective. Expanding any vector in the
selected basis proves injectivity of its row-evaluation map.

The complete finite-perturbation and basis-selection proofs are included.
The proof imports only Mathlib and the Hirsch model, with no public theorem
dependencies. The classical basis theorem is reused, not claimed as new
mathematics. The later clipping and mixed-routing applications have separate
local verification and are not conclusions of this public theorem.
