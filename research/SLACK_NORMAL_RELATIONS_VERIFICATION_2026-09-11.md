# Exact slack certificates: source verification recovered 2026-09-11

This integration transplants the exact two source blobs from PR92 onto current main without the historical verification-workflow ancestry.

- Frozen source commit: `4a9204edd7f03c7f9676f9dc9762be121e43bf1a`.
- `Solutions/PolynomialSlackMomentCertificate.lean`: Git blob `90005f87a9939477770c515ec19345ec93765f2b`.
- `Solutions/PolynomialSlackNormalRelations.lean`: Git blob `d46a7c7ba16d3eda1aae038e3046522af3b83ec0`.
- Successful run: `34615241828`; job: `103315400010`.
- Artifact: `10269999256`, `slack-moment-certificate-final-audit`.
- Artifact SHA-256: `752defc2e3fa23ff3ad58809a101074ccdcfa96501467fdda3caa91438247a0d`.
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Both modules compiled. All 14 required declarations passed direct axiom auditing with only `propext`, `Classical.choice`, and `Quot.sound`.

## Mathematical scope

The strongest declaration is `HirschSlackMoment.hpoly_and_row_faces_diamLE_two_of_normal_relations`. If an n-row H-polyhedron in ambient dimension d has a reference extreme vertex, n=d+2, strictly positive row weights c, nonconstant t, and the finite identities

```
sum c_i a_i = 0
sum t_i c_i a_i = 0
sum c_i b_i = 1,
```

then both the H-polyhedron and every original row-support face have intrinsic padded graph diameter at most two.

The proof establishes the entire affine slack image by rank-nullity, not mere containment. It then transports actual extreme points and extreme-segment adjacency through the injective affine slack map. No diameter conclusion or open research theorem is a hypothesis.

This does NOT establish existence of these relation witnesses from boundedness alone. In particular it does not yet establish the unconditional M_min <= h+2 consequence or the general Polynomial Hirsch conjecture.

## Evidence boundaries

The cited source gate is actual hosted compilation and transitive axiom evidence, not a claimed local build. The current conversation's local environment again timed out while mounting the exported Lean runtime. The final publication packet must therefore reuse these exact verified source blobs and pass independent standalone compilation and axiom audit before any credentials are exposed. A separate authenticated Prove2Me receipt is required for public Proved status.
