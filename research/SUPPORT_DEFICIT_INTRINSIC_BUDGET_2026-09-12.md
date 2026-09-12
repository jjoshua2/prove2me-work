# Beyond #201: intrinsic carrier budgets and the deficit barrier

## Verified integration of the independent #202 continuation

Both Lean sources from PR #202, commit
`4797a18206c63e761628e556d5ca4bd1eef3c169`, compile UNCHANGED at the committed pin
and are preserved in the #201 integration source commit
`117709458ec4b071dc846cd8443feea19ca2669b`. Their 12 axiom reports contain only
standard logical axioms. The combined build and audit cover 30 required
new declarations and 406 reports across dependencies; see
[the verification receipt](verification/2026-09-12-exact-support/local-verification.json).
The finite checker has also been rerun and matches the preserved source hashes.

The route modules remain independent of #201's imports, using merged #193/#200.
The exact-degree refinements below use #201, whose pointwise proof is now compiled
and whose run-count identity is newly formalized. The piecewise constants below
remain mathematical/finite-tested corollaries unless explicitly named as Lean
declarations. Public theorem status is recorded separately in STATUS.md.

## 1. A vertex-pair carrier's dimension is bounded by its OWN excess

For actual parent vertices p,q, let F be their smallest common face. Let h be
its intrinsic dimension and M its minimum equivalent intrinsic row count.
Put delta=M-h, the repository's `commonFacePresentationExcess`.

**Proposition.** `2h <= M`, hence `h <= delta` and `M <= 2delta`.

Proof: choose the existing irredundant strict intrinsic model, containing the
coordinate endpoints 0 and q'. They are vertices. Every nonzero restricted
row is slack at at least one endpoint: a row tight at both is a common-source
row, whose restriction to the common direction vanishes. Each vertex has at
least h nonzero active rows, by the existing tight-row spanning lemma. The
two active-row sets are disjoint, so there are at least 2h rows. The existing
minimum-count/irredundancy theorem identifies this model's row count with M.
The two excess inequalities follow by natural-number arithmetic. QED.

This is the standard separated-vertex counting argument, reused rather than
presented as a new general polytope theorem. Its useful new application is to
the same minimal carriers whose actual portal pairs the deferred repair charges.

The code directly composes:
- `commonFace_edgeRefinement_ready_model`;
- `commonFace_coord_endpoint_separation`;
- `separated_extremes_n_ge_two_d`;
- `commonFace_minCount_eq_irredundant_subpresentation`.

The vertex assumptions MUST remain. Distinct interior points of a 3-simplex
have full common carrier with h=3, M=4, delta=1, contradicting h<=delta.
Coincident vertices are harmless: their carrier is a point and h=M=delta=0.

A consequence for the former residual statement is that `h>=6` implies
`delta>=6`, not merely delta>=4. Excess-four and excess-five actual vertex
carriers cannot be the high-dimensional residual calls.

## 2. Turn an excess cap into an actual edge cost

Apply the public Larman bound to the MINIMUM intrinsic presentation, not to
the n original rows. Affine transport gives

```
diam(F) <= M * 2^(max(h-3,0)).
```

Thus if delta<=K, the proposition gives h<=K and M<=2K, yielding

```
diam(F) <= 2K * 2^(max(K-3,0)).
```

This bounds ordinary-edge distance, not circuit distance or just excess.
Extreme-face lifting supplies a parent-edge route for the actual portal pair.
Where K<=3, retain the existing exact small-excess bound K instead. The first
module therefore includes the optional piecewise budget

```
B(K) = K                              for K<=3,
       2K * 2^(K-3)                   for K>=4.
```

The values 16 and 40 below are conservative bounds obtained from already
formalized inputs, not optimal classical diameter constants. Bremner and
Schewe's *Edge-Graph Diameter Bounds for Convex Polytopes with Few Facets*
(Experimental Mathematics 20(3), 2011; arXiv:0809.0915) establishes the
small-excess-six regime by finite combinatorial/SAT arguments. That external
result was checked as background but is NOT an unproved input to these modules.
Formalizing it is unnecessary to establish the present parameterized bound.

## 3. Every fixed support deficit now closes, without adjacency restrictions

For the chosen certificate set e=n-d, r=number of used cuts, and g=e-r.
#201 gives, on each actual selected cut i,

```
delta_i <= g + 1 + deg_S(i) <= g+3.
```

Merged #193 also suffices for the coarser cap: it gives
`delta_i+(r-3)<=e`; together with r+g=e, this implies delta_i<=g+3,
including r<3 under natural subtraction. Accordingly the new module can
advance independently while #201 is being verified.

By Sections 1-2 every call has h_i<=g+3, M_i<=2(g+3), and an ordinary-edge
route of length at most `2(g+3)*2^g`. The deferred callback assembles all
selected routes on the SAME path, proving

```
Route budget <= D + 2r(g+3)*2^g.                (A)
```

The code includes a target-rooted existential certificate and route, with D=1.
No local route premise remains except the already-public Larman theorem. There
is no assumed recurrence, guessed factorization, or unused-pair route bound.

| Deficit g | Safe coefficient of r in the route budget |
|---|---:|
| 0 | retain the existing 3, rather than the coarser Larman coefficient 6 |
| 1 | 16 |
| 2 | 40 |
| 3 | 96 |
| 4 | 224 |

Thus the g=1 and g=2 cases no longer require the selected cuts to form a
matching or an independent set. For EVERY fixed g, the cost is linear in r.
This is a fixed-parameter diameter estimate, not a claim of an efficient
algorithm for computing the nonconstructively selected certificate.

The exact #201 degrees make the constants smaller. Let c be the number of
selected path components and s the number of isolated selected cuts. Counts of
degree-zero, degree-one and degree-two cuts are s, 2(c-s), r-2c+s respectively.
Using B on the cap g+1+degree gives these total CUT-cost bounds:

```
g=0:  3r - 2c,
g=1: 16r - 26c + 12s,
g=2: 40r - 48c + 11s.
```

The formulas give zero when r=c=s=0. They are mathematical corollaries with
finite regression checks; the second module claims only the safe uniform
budget (A), not Lean formalization of the selected-forest degree identity.

## 4. A polynomial regime, with a precise limitation

Let N=n+d>=1. Since r,g<=N, if `2^g<=N^k` for a fixed k, then

```
D + 2r(g+3)*2^g <= D + 8*N^(k+2).
```

This exact natural-number implication is included in Lean. In particular,
certificates with logarithmic deficit have polynomial route budgets. It does
NOT establish that every polytope admits such a certificate.

In fact a universal logarithmic-deficit existence theorem for these shortest
certificates is FALSE. The following explicit obstruction should prevent that
from becoming another unproductive open leaf.

## 5. Cubes force large deficit on every shortest repair path

Take P=[0,1]^d, n=2d, and target v=0. Its target-slack cuts are exactly
`x_i<=1`. Every such cut face contains the parent vertex z=(1,...,1).
Consequently their labels form a clique in the parent-vertex region graph,
regardless of the other old-edge or endpoint labels in the mixed cover.

A chordless path can contain at most TWO vertices of a clique: if it contained
three at ordered positions j1<j2<j3, the first and third would be adjacent
while nonconsecutive, a chord. Therefore every certificate using a shortest
mixed path in this construction satisfies

```
r<=2, hence g=d-r>=d-2.
```

For any fixed k, eventually 2^g>(3d)^k, so the sufficient polynomial criterion
from Section 4 cannot hold on these certificates in all dimensions. This
obstruction is independent of how the shortest path or portals are chosen.

Yet the cube diameter is exactly d: each edge changes one coordinate, and
flipping differing coordinates one at a time attains that bound. Thus a large
support deficit is NOT evidence of a large actual diameter. The cube also
shows h<=delta and M<=2delta can be sharp: opposite vertices of a k-cube
carrier have h=delta=k and M=2k, while distance is only k.

This cube obstruction is proved mathematically here; it is not claimed as a
new Lean theorem. The Python checker tests its exact common-hub equations and
the finite clique/chord argument, not arbitrary-polytope geometry.

## 6. Resulting research priorities

Do not keep working on isolated excess-four/excess-five high-dimensional calls:
Section 1 eliminates that combination, and Section 3 routes every bounded-gap
regime. Do not propose a universal logarithmic support deficit: cubes refute it.

The meaningful remaining case has large deficit. It needs a bound exploiting
structure beyond that scalar: for example the existing certified independent
row-block machinery handles cube-like product structure, while coupled
high-excess carriers still need a joint argument. Any proposed potential must
stay polynomial on cubes even though these shortest certificates have r<=2,
g growing with d, and potentially high-dimensional carriers. This is a
concrete stress test, not a new conjectural reduction that merely restates Hirsch.

No Polynomial Hirsch proof or general bound for coupled large-deficit carriers
is claimed. The contribution is the completed parameterized EDGE-cost argument
plus an explicit geometric obstruction to the tempting next shortcut.

## Checks actually run in this session

```
python3 scripts/check_support_deficit_budget.py
python3 -m py_compile scripts/check_support_deficit_budget.py
```

The committed JSON records exact source SHA-256 hashes and these passing counts:
15,453 size/budget cases; 106,483 selected-path/gap cases; 18,388 polynomial
implications; 8,191 cube vertex pairs modulo symmetry; 10,416 simplex pairs;
7,814 clique selections excluded by chordlessness; cube hub checks in dimensions
1 through 64. An interior-simplex negative control checks the necessity of
vertex hypotheses. These are arithmetic and explicit-example regressions,
NOT Lean compilation, transitive axiom verification, or Prove2Me acceptance.
