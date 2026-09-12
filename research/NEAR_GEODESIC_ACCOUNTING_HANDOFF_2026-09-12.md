# Verification handoff: controlled detours and additive carrier spill

## Keep the separate work separate

Baseline main: `321f473d871aad2d692595acd97a667d6a648d06`.
This packet does not edit #205, #206, STATUS.md, pins, workflows or platform
records. It has four NEW Lean modules; no new Lean acceptance is claimed.
The two near-geodesic modules consume #206's interfaces after that PR is
integrated. The amortized/additive modules already depend only on main.

## Highest-value result

`HirschAdditiveAllowance.AdditiveRepair.sound` closes the ACTUAL route recurrence
under proper-face dimension drop, child excess <= parent e, sibling sum <= e+b,
and explicit small-leaf routes of rate C at excess <=b:

    cost <= C*e+(1+b*C)*h*(e-b).

This is not restricted to zero additive spill. The proof conserves shifted
mass (e-b)+ on large children. In particular b<=3 permits C=1 from the existing
small-excess theorem. The existence of such splits for arbitrary polytopes is
NOT a proved premise and must not be smuggled into an unconditional theorem.

The companion `PortalRepair.sound` gives actual cost <= h*e+sum(local charges).
The near-geodesic proof bounds ALL contact POSITIONS by k+3, including repeated
labels, and then gives sum(delta)+r*s <= r*e+(k+3)*s for actual pairs.

## Run locally

```sh
python3 -m py_compile scripts/portal_detour_optimizer.py \
  scripts/additive_allowance_solver.py scripts/test_portal_detours.py
python3 scripts/test_portal_detours.py
python3 scripts/portal_detour_optimizer.py fixtures/cyclic_polar_12_input.json \
  --slack 1 --mode conservative
python3 scripts/additive_allowance_solver.py fixtures/cyclic_polar_12_input.json \
  --allowance 2 --slack 1
lake build Solutions.PolynomialAmortizedPortalRoutes \
  Solutions.PolynomialAdditiveAllowanceRouting
# After the corresponding #206 interfaces have been integrated:
lake build Solutions.PolynomialNearGeodesicWindows \
  Solutions.PolynomialNearGeodesicCarrierMass
```

There are 14 axiom printouts across 447 Lean lines. Inspect the transitive
standard-logical-axiom closure and repair elaboration locally before using
any existing final hosted gate. The candidate API-sensitive points are
finite dependent-sum induction in `route_chain`, Finset cardinality <=1,
position-set minimum/cardinality lemmas, and natural-number distributivity
in the additive recurrence. No proof hole is intentionally left in source.

## Scope that must survive elaboration repairs

- Near-geodesic contacts are occurrence POSITIONS, not a toFinset of labels.
- The supplied graph walk may revisit a cut; all portal pairs still incur cost.
- Do not force a non-shortest walk into the old shortest-certificate structure.
- Numerical mass tags in the generic route-tree theorem are not themselves
  polytope facts. A geometric wrapper must certify them from intrinsic faces.
- Small leaves include actual routes and their bounded rate, not an open
  high-excess routing oracle. Proper-face dimension and excess conditions are
  explicit at every internal node.
- Cached subproblems are charged on every occurrence.
- The numerical implementation requires a complete simple irredundant rational
  input. A nonsimple input or capped enumeration is rejected, not normalized
  without proof. The analytical incidence result has broader hypotheses.

## Exact obstruction and positive fixture

The 4D 12-facet centered moment-curve polar has 54 fully enumerated vertices.
For specified endpoints, all strict-geodesic first-edge/target-facet/portal
choices in the implemented repair family have minimum child excess16 and
minimum child potential32, against parent e8 and Phi32. Thus no zero-charge
root, and no b2/b3 additive root, exists in that restricted family at k0.
With k1 both a zero-charge tree and a b2 additive tree give six actual edges.
The latter has three internal nodes and leaf excess total3; its general bound
is80. Independent graph distance is6. Strict-region UNCONSTRAINED lookahead
can also find six edges, but with positive charge: do not claim that every
six-edge route needs a detour. The counterexample is to local accounting under
shortest-region restriction, not to short graph routes.

The test regenerates the exact input, two optimum tables, and full recursive
certificates. The independent optimum audit enumerates label walks separately
from the optimizer and uses a separate portal-chain DP.

## Deliverables and next mathematics

The full proof note distinguishes mathematical statements, generic Lean
candidates, exact rational instance verification and unproved universal
existence. The compact receipt records all seven code hashes. Detailed receipts
and generated fixtures are in the conversation ZIP and regenerate from the
committed scripts. Do not promote finite successes to a universal b or k.

After these modules verify, the research target is existence of bounded-spill
portal choices on broad intrinsic carriers, rather than another proof that a
factor-three one-level estimate can be iterated. No new open Prove2Me child or
platform mutation was created by this packet.
