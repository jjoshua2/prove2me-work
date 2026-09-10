# The exact geometric cost of repairing circuit rank defect

Project: `jjoshua2/prove2me-work`. Continuation dated September 10, 2026.

This is the durable repository handoff for the ordinary-mathematics result originally developed and exactly tested in the standalone continuation packet. The packet's original full note has SHA-256 `f1602d7e4c9965c5c478102c72ce0782b42cbe9d04c0782064e598b0d0696f7c`; see `odc_verification_receipt.json` for the executed evidence. The statements below are **not Lean-verified and not Prove2Me-Proved**.

## 1. Defect resource

Let `P` be a bounded full-dimensional `d`-polytope, `d >= 1`, with `n` genuine facets, written irredundantly as `a_i x <= b_i`. Let `u != v` be vertices and `g=v-u`. Define

```text
r(P,g)     = rank {a_i : a_i g = 0}
delta(P,g) = d - 1 - r(P,g)
e(P)       = n - d
B(P,g)     = e(P) + delta(P,g) = n - 1 - r(P,g).
```

For bounded full-dimensional presentations the row map is injective, and row-circuit support minimality is equivalent to neutral rank `d-1`. Hence `delta=0` exactly when `g` is a row circuit. Genuine-facet presentations matter: redundant rows can change the neutral rank.

## 2. General face restriction

### Theorem 1 — defect/excess transfer

Let `F` be a `d`-dimensional face of a bounded `D`-polytope `R`. Suppose nonzero `g` is parallel to `F`. Use genuine-facet descriptions of both `R` and `F`. Then

```text
0 <= delta(R,g) <= delta(F,g),
delta(F,g) - delta(R,g) <= e(R) - e(F),
B(F,g) <= B(R,g).
```

In particular, if `g` is an ambient circuit,

```text
e(R) >= e(F) + delta(F,g).
```

### Proof

Let `R` have `N` genuine facets and `F` have `n`. The ambient rows identically tight on `F` span the annihilator of `lin F`, of dimension `D-d`, and annihilate `g`. Choose `D-d` independent such rows as affine-hull equations.

The ambient neutral-row span has dimension `D-1-delta(R,g)`. Its restriction to `lin F` has kernel exactly the affine-hull annihilator, hence restricted rank

```text
(D-1-delta(R,g)) - (D-d) = d-1-delta(R,g).
```

Choose one ambient row representing each genuine facet of `F`. Their neutral restrictions have rank `d-1-delta(F,g)`, so `delta(F,g) >= delta(R,g)`. After choosing the affine-hull rows and the `n` facet representatives, exactly

```text
N - (D-d) - n = e(R)-e(F)
```

ambient rows remain discardable. Deleting that many vectors loses at most that much neutral rank. This gives the second inequality and therefore monotonicity of `B=e+delta`.

The exact drop in `B` is the number of discarded residual inequalities minus the independent neutral rank carried by them. Thus loss of circuit rank can consume all apparent facet-excess savings.

### Generalized localization

For distinct feasible `x,y` in a `D`-polytope `R`, let `h` be their minimal common-face dimension and `f_x,f_y` the dimensions of their individual minimal faces. With `g=y-x`, a disjoint active-row count gives

```text
2h <= e(R) + delta(R,g) + 1 + f_x + f_y.
```

For vertex endpoints,

```text
2h <= B(R,g) + 1.
```

This contains the circuit case `delta=0`, hence `2h <= N-D+1` for vertex-to-vertex circuit displacements.

## 3. Facet-optimal isometric circuit completion

### Theorem 2

For every `P,u,v` above there is a bounded full-dimensional polytope `R` with

```text
dimension(R) = d+1,
facets(R)    = n + delta(P,g) + 1,
e(R)         = e(P) + delta(P,g) = B(P,g),
```

such that:

- the floor `P_0={(x,0):x in P}` is an unchanged genuine facet of `R`;
- the embedded displacement `(g,0)` is a row circuit for the irredundant facet description of `R`;
- `(u,0)` to `(v,0)` is maximal in both orientations;
- there is an explicit edge/stay map from the vertex graph of `R` onto the vertex graph of `P`, fixing the floor;
- consequently every original vertex-pair graph distance is exactly preserved;
- all counted facets are genuine; rational input admits rational choices.

Moreover these counts are optimal among bounded extensions containing `P` as a proper affine face and making embedded `g` a circuit:

```text
minimum ambient facet excess = n-d+delta(P,g),
minimum ambient facet count  = n+delta(P,g)+1.
```

The lower bound is Theorem 1 plus the requirement that a proper containing face have ambient dimension at least `d+1`.

### Construction

Start with a one-sided wedge over a genuine facet:

```text
W = {(x,t): a_i x <= b_i for i != f,
             t >= 0,
             a_f x + t <= b_f}.
```

Its floor is `P`, its graph projects by edge/stay to `P`, and the lifted displacement keeps the same defect: the new floor normal adds one neutral dimension, while a neutral wedged row can be recovered by subtracting that floor normal.

If `delta=0`, the wedge already gives the optimal completion. Otherwise choose a cost in `(g,0)^⊥` uniquely exposing a roof vertex `q+`. Such costs form an open set. In the quotient of `(g,0)^⊥` by the current neutral-row span, choose exactly `delta` independent exposing costs. Make shallow cuts just below their common maximum at `q+`. All old wedge vertices except `q+` survive strictly, including the entire floor. The new normals annihilate `(g,0)` and complete the neutral rank to ambient dimension minus one.

The cuts meet in the interior of the old inequalities and their normals are independent, so each supports a genuine facet. Map all new vertices back to `q+`; retained old vertices map to themselves. Edges incident to retained vertices agree locally with old wedge edges, and edges between new vertices map to a stay. Composing with wedge projection preserves every original floor distance exactly. Maximality follows because the original line through two distinct vertices intersects `P` exactly in their segment.

An actual external edge parallel to `g` is deliberately not part of Theorem 2; Section 5 explains why it can cost more.

## 4. Minimum exactly balanced ambient dimension

### Theorem 3

Among exactly balanced polytopes `Q` satisfying `facets(Q)=2*dimension(Q)`, containing `P` as a proper affine face and making the selected pair one ambient circuit step, the claimed minimum possible dimension is

```text
D_min = max(d+1, B(P,g)).
```

The minimum balanced facet count is `2*D_min`, attained while preserving the isometric floor and graph retraction.

The lower bounds are immediate: proper containment needs dimension at least `d+1`, while exact balance makes ambient facet excess equal ambient dimension, which by Theorem 1 is at least `B(P,g)`.

For attainment, start from Theorem 2. If `B >= d+1`, perform `B-(d+1)` one-sided wedges; each increases dimension and facet count by one while preserving excess, circuit status, and floor metric. If `B<d+1`, keep dimension `d+1` and add `d+1-B` shallow one-vertex truncations away from the protected floor; old neutral rows remain, so the circuit survives. This reaches exact balance.

Example: for the 8-cube and a diagonal changing two coordinates, `d=8,n=16,delta=1`, so `B=9`; the first completion is already balanced in dimension 9 with 18 facets, preserving all 256 original vertices and their pairwise distances.

## 5. Requiring an external realizing edge can cost one more

### Theorem 4 — maximum-defect case

Suppose `r(P,g)=0`, i.e. `delta=d-1`. If an extension contains `P` as a face, makes `g` a circuit, and has an actual `g`-parallel edge **outside** `P`, then

```text
e(R) >= n = B(P,g)+1.
```

This is sharp via the earlier prism-cap construction; the minimum total facet count for a proper-face extension with external realization is `n+d+1`, and the minimum balanced dimension is `n`.

Proof of the extra unit: every representative of an original facet is nonneutral. At the cheaper equality `N=n+D-1`, an ambient circuit leaves exactly `D-1` independent neutral rows total. Every ambient facet containing the protected `P` is among them. Any edge parallel to `g` needs an active neutral span of rank `D-1`, hence must lie in every one of those neutral containing facets and therefore in `P`, contradicting external realization.

Thus the cheaper optimal circuit completion need not contain a parallel edge. At maximum defect and `d>=2`, it cannot contain one anywhere.

## 6. Consequence for the Polynomial Hirsch strategy

`B=e+delta` is both a face-restriction resource and, according to Theorem 2, the exact excess cost of completing an arbitrary protected displacement to an ambient circuit. The completion/restriction round trip can preserve **all** original graph distances while saturating

```text
ambient circuit excess B -> original face excess e plus defect delta,
e + delta = B.
```

Therefore the resource inequality alone cannot force strict progress. A useful induction still needs additional information: actual selected portals, route order, special restricted rows, or an independently certified low-cost geometric representation. The completion theorem and balanced minimum are hardness/structure diagnostics, not smaller Open children for `polynomial_edge_refinement_of_circuit_walks`.

## 7. Exact evidence boundary

The original exact constructor produced 17 optimal first-stage completions on 13 input models. The independent audit covered 37 stages, 1,838 vertex occurrences, 6,657 recomputed graph-edge occurrences, 375 genuine-facet witnesses, 38,778 protected original-pair distance comparisons, 74 forward/reverse maximality checks, and 1,119 defect/excess restrictions; 776 restrictions strictly lowered `B`. It also checked 19 maximum-defect no-realizing-edge cases and rejected five deliberately corrupted certificate types.

Representative balanced outputs include:

| Original | d,n | delta | balanced D,N | output vertices | protected distance |
|---|---:|---:|---:|---:|---:|
| square diagonal | 2,4 | 1 | 3,6 | 8 | 2 |
| cube opposite pair | 3,6 | 2 | 5,10 | 28 | 3 |
| 4D Dantzig | 4,8 | 3 | 7,14 | 68 | 4 |
| 5D Dantzig | 5,10 | 4 | 9,18 | 252 | 5 |
| 8-cube two-coordinate diagonal | 8,16 | 1 | 9,18 | 392 | 2 |

See `research/odc_verification_receipt.json` for exact scope and hashes. These finite checks do not prove the universal statements.

## 8. Literature / novelty boundary

The standard wedge and graph projection are reused project machinery. Borgwardt–Brugger, *Circuits in Extended Formulations* (arXiv:2208.05467), is primary background on circuit noninheritance; it is not cited as proving these optimal completion statements. No exact prior statement matching the claimed sharp completion minima was located in the initial literature search, but **no novelty claim is made** without a deeper dedicated review.
