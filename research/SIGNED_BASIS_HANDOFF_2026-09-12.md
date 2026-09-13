# Verification handoff: signed basis conditioning and original-H shadow routes

## What is new and what is not claimed

The signed class contains same-sign two-coordinate rows and negative signed
cycles. The old positive-diagonal network recognizer cannot in general remove
those signs. Every nonsingular normalized basis has inverse entries in
{0,+1,-1,+1/2,-1/2}, even when its determinant is exponentially large.
The full proof uses the signed-component kernel and row deletion.

The classical Dadush--Haehnle wide-normal-cone theorem then gives the explicit
mathematical bound36h^3 on an h-dimensional actual carrier, and the verified
sum(h_i)<=3e gives the same-selected-carrier boundD+108H^2 e. These are NOT
newly formalized full signed-polytope diameter statements. The external analytic
result is not imported as a new axiom. The generic aggregation needs actual
local routes and their count bounds.

The code constructs exact routes with a parametric objective and symbolic RHS
basis tie breaking. Every reported point and edge belongs to the ORIGINAL
input. Stationary limiting basis pivots are retained in the certificate and
not charged as edges. The deterministic objective samples are NOT the random
sampler used in the published expected-length proof. Do not claim a polynomial
runtime for this sampler or the capped endpoint-basis enumeration.

## Reproduce before a hosted gate

```
python3 -m py_compile scripts/signed_basis_shadow.py scripts/test_signed_basis_shadow.py
python3 scripts/test_signed_basis_shadow.py
lake build Solutions.PolynomialSignedBasisGeometry \
  Solutions.PolynomialSignedCarrierAggregation
```

The two Lean files are UNCOMPILED candidates. Their nine axiom printouts cover
signed path transport/pinning, inverse-column normalization, dual-frame cone
and separation witnesses, and actual selected-route aggregation. Inspect the
transitive standard-logical-axiom closure at the repository pin. Possible API
repairs concern `real_inner_le_norm`, boolean parity simplification and finite
sum normalization, not mathematical premise changes.

The all-basis signed-component extraction and graph-to-Euclidean norm bound are
proved in the note and exact code, not all separate Lean declarations. The
complete symbolic simplex algorithm and affine quotient are likewise not an
end-to-end formal existence theorem. A public theorem must preserve those
boundaries and its true external dependencies.

## Important certificate invariants

- Use every original inequality, including duplicates and constant rows.
- Recognize absolute gain balance, but retain the coefficient SIGNS. A negative
  cycle pins a component; it is not an inconsistency of the polyhedron.
- A failed absolute-gain normalization is unsupported input, not large diameter.
- The actual endpoint midpoint is strict in the quotient after ALL common
  equalities are removed. Same-component rows may become ±2 unary rows.
- A matrix inverse is accepted only after all original normalized B*C=I equations
  and the entry alphabet have been checked.
- Symbolic RHS perturbation is just finite lexicographic coefficient arithmetic.
  No floating epsilon or unverified numerical rank is used.
- Check multiplier feasibility over each objective interval, the precise
  entering ratio, every basis update, the original endpoint blockers, and rank
  d-1 of original common tight rows for every nonstationary move.
- The word "shortest" is not a claim about these sampled routes. Their exact
  lengths, the classical existence bound, and algorithmic runtime are distinct.

## Test interpretation

The small signed basis suite independently compares with Gaussian elimination.
The small H suite exhausts active bases, reconstructs the graph by original
shared rank, and checks every output against that graph. Large examples never
enumerate a complete vertex set. The odd-star family proves an exponential
edge-direction lower bound analytically and checks actual sampled edges.

The 2^-80 gain imbalance control demonstrates failure of uniform inverse-entry
bounds outside the recognized class. Its underlying polytope is a triangle,
not a high-diameter counterexample. The2026 general-TVPI paper cited in the note
bounds circuit diameter; it cannot be used as an edge bound.

All new paths are add-only and distinct from the current network and Minkowski
files. No workflow, dependency pin, original proof, or platform status is changed.
