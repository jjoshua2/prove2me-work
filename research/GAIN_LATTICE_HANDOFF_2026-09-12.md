# Verification handoff: quantitative gain cycles beyond signed magnitude balance

## Coordination and exact dependencies

Continuation of PR #210 from a8b93f3b0e9198517d77b65996d8694a3799ebfe.
All new paths are additions; earlier signed/network/Minkowski implementations,
publication packets, workflows and pins stay unchanged. The Python route
state machine reuses scripts/signed_basis_shadow.py unchanged. Its SHA256 is
recorded separately in the new execution receipt. The generic gain inverter,
conditioner, and route verifier are new, not a monkey-patch of old globals.

## Highest-value mathematical content

1. Normalize cycle magnitudes to powers of supplied q>1 after arbitrary tree
   scaling. Integer potential balancing minimizes the maximum exponent radius.
   A returned negative cycle proves R-1 impossible even for real potentials.
2. All simple path gains are bounded by Gamma=q^T, with T the sum of the d-1
   largest absolute residual row exponents. All nontrivial signed cycle gaps
   are >=eta, where eta=1-q^(-g) and g is the gcd of fundamental cycle exponents.
   At g=0 use eta=1. Every nonsingular normalized basis inverse entry is <=Gamma/eta.
3. For q=1+1/(dR), or the directly verified condition U<=6dR, the classical
   normal-cone theorem gives360 R^2 d^4 ordinary-edge diameter. The inherited
   h-dimensional common-face bound is360 R^2 d^2 h^2, NOT automatically360 R^2 h^4.
4. Four rows e1,e2,e1+e2,e1+(1+epsilon)e2 force global delta<=sqrt(epsilon)
   after ANY invertible linear preconditioning. This is not a diameter lower
   bound and does not rule out local feasible-basis conditioning.

## Run locally before any hosted final gate

```sh
python3 -m py_compile scripts/gain_lattice_certificate.py \
  scripts/gain_shadow_extension.py scripts/test_gain_lattice_routing.py
python3 scripts/test_gain_lattice_routing.py
lake build Solutions.PolynomialQuantizedGainGeometry \
  Solutions.PolynomialGainConditioningBarrier
```

The two Lean files are UNCOMPILED candidates. Audit the eleven printed declarations
under the pinned standard logical axioms. Potential API-sensitive points are
sum_range_succ normalization, inv/mul rewriting, and the nlinarith normalization
of the quartic natural-number cost. No hole is intentionally left in a proof.
Do not weaken actual-route or local-cost hypotheses to force a compilation.

The full graph-to-basis extraction, analytic wide-normal-cone theorem, and
Euclidean cross-ratio normalization are paper proofs/exact checks, not all
complete Lean declarations. The external Dadush--Haehnle theorem is not added
as an axiom. The actual selected-carrier adapter takes real local routes and
cost evidence, not arbitrary numerical model tags.

## Reproduction and interpretation

The test regenerates three large input/route fixtures and the source-hashed
receipt. It independently compares sparse gain kernels/inverses with Gaussian
elimination, small H-graphs with returned edges, and minimum gauge radii with
finite brute force. Radius and cycle-gap certificate verification does not
invoke the discovery routine. Route verification does not invoke path search.

The supplied base is part of the recognized class, not automatically discovered
for every input. An unrecognized base can be omitted to try the general exact
route constructor, but that does NOT attach a uniform polynomial diameter bound.
The finite objective sampler is not the published expected-length distribution;
all successful edges are checked on the ORIGINAL input, including stationary
symbolic pivots and common-face lifting. Computation caps are failed searches,
not geometric nonexistence.

The two-dimensional near-resonance example has a very short graph route. The
bad inverse and all-preconditioner bound diagnose a limitation of a conditioning
proof, not a hard graph. Likewise, large determinants in the48D integer cycle
coexist with small normalized inverses. Preserve these distinctions in any
publication or user summary.

## Next research

Control multiple independent gain scales or positive cycle resonances that do
not lie on a sufficiently separated one-dimensional exponent lattice. Checking
only the chosen fundamental cycle gains is insufficient: combinations may
nearly cancel. A universal affine preconditioner cannot guarantee a global
all-basis delta either. A different local/phase argument could still work.
No new root child or general Polynomial Hirsch conclusion is created here.
