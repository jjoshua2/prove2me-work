# Verification handoff: wide cones despite arbitrarily resonant gains

This add-only continuation is based on PR #210 head
4d82742bf8acd4905bb2933bec09839a8d3ed7e9. Earlier solvers and proofs are unchanged.
The numerical wrapper reuses gain_shadow_extension.py, gain_lattice_certificate.py
and signed_basis_shadow.py byte-for-byte. The two new Lean modules import the
prior signed geometry/aggregation modules on the same PR; those prerequisites
must compile first. Do not claim that every import is already accepted on main.

## Mathematical target worth checking

A spanning-forest certificate permits arbitrary overlapping balanced cycles.
Every nonunit fundamental cycle must be coherently directed and edge-disjoint
from every other fundamental cycle. Thus unbalanced blocks are single directed
cycles, while balanced blocks can be dense. Gamma=product max(G_C,1/G_C).

Every independent basis cone has width at least1/(2 Gamma^2 d^(3/2)), with no
minimum cycle-gap factor. In a cycle block, sum of normalized cycle rows is
(1-G)e_r. The center sign(1-G)e_r plus the off-cycle tree rows has cycle dual
margins1/|1-G|. The same denominator in the inverse-column norm CANCELS.
Basis-dependent diagonal gauges must be transported back, losing at mostGamma.

Faces preserve the block condition and cannot increaseGamma. Applying the
CLASSICAL Dadush--Haehnle wide-normal-fan theorem yields256h^3 whenGamma<=2.
The same selected-carrier dimension mass givesD+768H^2e. The external analytic
result is not formalized or imported as an axiom in these candidates.

## Local commands

```sh
python3 -m py_compile scripts/coherent_gain_cones.py scripts/test_coherent_gain_cones.py
python3 scripts/test_coherent_gain_cones.py
lake build Solutions.PolynomialCoherentCycleCones \
  Solutions.PolynomialCoherentCarrierCosts
```

The 180 new Lean lines contain ten axiom printouts. They are UNCOMPILED candidates.
Possible API-sensitive repairs: Finset.smul_sum, LinearEquiv coercions and maps,
and the generic cubic assembly's multiplication normalization. Preserve positive
cone coefficients and whole-ball inclusion; replacing them by a bound on a
basis inverse would reintroduce the very resonance factor removed here.

The finite dual-frame core does not automatically formalize the graph-to-basis
classification or heredity proof. The complete constructive route algorithm
and the normal-fan theorem likewise remain distinct dependencies. Keep those
boundaries in any public statement and do not add a circular root premise.

## Exact tests

The test regenerates four large input/route fixtures and the execution receipt.
It checks all basis subsets in its libraries through dimensionfive, including a
dense balanced core; dimensionsix is sampled. Every accepted cone is separately
checked by Gaussian inverse margins. Original-H vertices/edges are independently
enumerated for the small models. Large cases do not enumerate their graphs.

The 2^-240 resonance specimen has an enormous inverse entry but a fixed positive
cone margin. This is a feasible basis in an explicit quadrilateral, not just
an infeasible algebraic basis. Both sides of gain1 are tested. The noncommensurate
cycle example uses opposite two-adic valuation signs to rule out ANY common
integer-power base; it is not just a failure of a guessed q.

The wrapper checks its own face's Gamma rather than transferring the ambient
intrinsic dimension uncritically. Every visited cone witness is tied to the
actual quotient basis and every ordinary edge to the original inequalities.
Positive-proportional normal duplicates are collapsed only in the structural
normal graph; original RHS rows and route checks are retained.

## Algorithmic limits

The inherited finite seeded objective sampler is NOT the analytic paper's
expected-length sampler. Endpoint basis selection and pivot caps can fail; no
uniform runtime claim is made. Actual output routes and the mathematical
existence bound are separate evidence. A missing structural certificate means
unsupported structure, not high graph diameter.

After local green and transitive standard-axiom audit, use one existing hosted
final gate. No new workflow, credential use or platform mutation was performed
in the originating session.
