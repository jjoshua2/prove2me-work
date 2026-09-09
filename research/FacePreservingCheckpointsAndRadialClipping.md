# Fixed-parent checkpoint rounding and simultaneous radial clipping

Continuation of PR #48 / PR #50, 2026-09-09.

## Current verified / public status

Polynomial Hirsch remains open. The PR #50 source mathematics was fully
verified at commit `7cea19e9abdd16607bbfdaf5919f4a1433b6d416`, Actions run
`34403714961`: all **16 new declarations** compiled in Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`; the audit checked **39 reports**
and found only `propext`, `Classical.choice`, and `Quot.sound`; exact regression
output reproduced byte-for-byte.

A separate publication gate, Actions `34406122009`, rebuilt and audited two
public wrappers, recursively flattened their private `Solutions.*`
dependencies, independently compiled/axiom-audited both standalone proofs, and
then authenticated to Prove2Me.

Two results from this work are now public **Proved** theorems:

1. `Hirsch.face_preserving_vertex_selection`
   - theorem `c8ebefd3-d31a-4d33-b1f8-6298669cc3ba`
   - submission `5c026214-1592-4db8-bc03-be242ced7b18`
   - **ACCEPTED / Proved**
2. `Hirsch.face_interval_cover_route_bound_of_feasible_start_containment`
   - theorem `6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102`
   - submission `6c140ee2-141f-4b4f-baa3-031a31df4f7f`
   - **ACCEPTED / Proved**

The same authenticated run posted Polynomial Hirsch mission discussion comment
`dd739cf3-7749-4947-a20a-ba16a17859ef`, linking these results and recording the
radial construction, its formalization boundary, and the remaining global
research gaps. Receipt artifact: `10125766656`.

No new Open theorem child was created.

The **complete simultaneous-clipping `L + sum B_i` theorem below is still not
one end-to-end Lean declaration**. The finite breakpoint/face-cover extraction
and clipped-old-edge diameter-one assembly remain formalization work. It is
therefore represented on Prove2Me as mission research context, not falsely
registered as a Proved theorem.

## 1. Intermediate checkpoints need not be vertices

Let `P` be compact, and let `F_i` be any family of closed extreme subsets of
`P`; the family need not be finite. For every `x ∈ P`, there is a parent vertex
`r(x)` such that

```text
x ∈ F_i  ->  r(x) ∈ F_i, for every i simultaneously.
```

Moreover the selector can satisfy `r(v)=v` for every existing parent vertex.
It need not be continuous, nearest-point, or adjacency-preserving.

Proof: intersect `P` with every supplied face containing `x`. The intersection
contains `x`, is closed/compact, and is extreme in `P`. Krein–Milman supplies
an extreme point of the intersection, hence a parent vertex. Choose one for
nonvertices and fix existing vertices.

Consequences proved in Lean:

- a feasible shared point of two closed parent faces supplies a genuine shared
  parent vertex;
- a fixed feasible face-covered checkpoint sequence with vertex endpoints can
  be rounded simultaneously without changing its available face budget;
- PR #48's start-containment theorem needs only the two global endpoints to be
  vertices; marked intermediate checkpoints may be nonvertices;
- the analogous feasible active-containment theorem is source-verified as well.

The selector and feasible start-containment route theorem are now the two
public results above.

This is geometric: it uses compactness and actual faces of one fixed parent.
Merely preserving labels of faces of an earlier polytope does not suffice.

## 2. A genuine facet sweep defeats naive historical-label transport

Take

```text
P_t = [0,1]^3 ∩ {3x + 2y + z <= t}
```

and move the last facet from `t=11/2` to `t=9/2`. Both endpoint polytopes are
simple, full-dimensional, and irredundantly represented by the same seven
inequalities; both have ten vertices.

The stationary faces `F_x={x=1}` and `F_y={y=1}` intersect initially but are
**disjoint** in the final parent, even though both remain genuine final facets.
The old shortest path

```text
u=(1,0,0) -> z=(1,1,0) -> v=(0,1,0)
```

has surviving endpoints but loses `z`. Thus the network consisting only of
the two historical support labels loses its connection. The ambient final
polytope is still connected and its `u-v` distance remains two, so this is a
representation falsifier, not a Hirsch counterexample.

The **final moving facet** supplies the missing connector. A feasible final
face-covered sequence is supported by `F_x`, the final moving facet, and
`F_y`; its two interior checkpoints can be nonvertices, which the public
selector now rounds correctly. The radial certificate below constructs an
actual three-edge final route within certified budget four.

A smaller five-facet intersection-loss example is also checked exactly.

Lesson: project an old path into one **fixed final parent** and use final faces,
rather than assuming historical face intersections survive deformation.

## 3. Positive construction: simultaneous monotone clipping

Let `Q` be a convex polyhedron and

```text
P = Q ∩ ⋂_i {a_i(x) <= b_i},  i=1,...,m,
```

be compact. Assume a common centre `o ∈ Q` strictly satisfies every added cut:
`a_i(o)<b_i`.

Let `u,v` be vertices surviving as vertices of both `Q` and `P`, and suppose a
length-`L` edge/stay walk in `Q` joins them. For the **final** cut faces

```text
F_i = P ∩ {a_i(x)=b_i},
```

let `B_i` bound intrinsic graph diameter.

The ordinary mathematical construction gives a final `P` edge/stay route of
length at most

```text
L + sum_i B_i.
```

It uses at most `m` final cut faces and at most `L` clipped old edges, charging
each distinct support once rather than every historical deformation event.
Every `B_i` remains an explicit cost.

### Fixed radial map

Set `s_i=b_i-a_i(o)>0` and define

```text
lambda_i(x) = (a_i(x)-a_i(o))/s_i
mu(x)       = max(1, lambda_1(x), ..., lambda_m(x))
rho(x)      = o + (x-o)/mu(x).
```

Because `mu>=1`, `rho(x)` is a convex combination of `o` and `x`, remains in
`Q`, and satisfies every final cut. Thus `rho` maps the relevant part of `Q`
into `P` and fixes every point already in `P`.

If `mu(x)>1`, some cut `i` attains the maximum and
`a_i(rho(x))=b_i`; `rho(x)` lies in the **final** face `F_i`.

Nine algebraic/radial declarations are kernel-verified, covering evaluation,
convex membership, cut feasibility, active-face equality, unit-scale behavior,
finite radial-scale existence, final-clip membership, active final-face
membership, and affine dominance on a cell.

### Cell decomposition of one old edge

Parameterize an old edge by `x(t)=(1-t)p+tq`. Each normalized violation
`lambda_i(x(t))` is affine. Include the constant function `1`; insert `0`, `1`,
and all pairwise crossings in `(0,1)`. On each resulting closed cell, one affine
function is maximal throughout.

- If the constant `1` dominates, `rho` is the identity and the cell is a
  clipped portion of the old edge inside `P`.
- If cut `i` dominates, the whole radial image lies in final face `F_i`.

Adjacent cells share the exact same feasible radial image at their common
breakpoint. Consecutive old edges likewise share the same radial image at the
old vertex. The whole constructed trace therefore lives in **one fixed final
parent** and is genuinely face-covered.

Simultaneous face-preserving rounding converts all those feasible shared points
to final-parent vertex portals while retaining the needed support incidences.
Existing distinct-region routing then charges each final cut face once and each
clipped old edge at most once, giving the stated `L + sum_i B_i` budget.

## 4. Formalization boundary — do not overclaim

The complete simultaneous-clipping statement is **not yet one end-to-end Lean
theorem** and was intentionally not registered as Prove2Me Proved.

Remaining formal assembly:

1. finite extraction/sorting of the pairwise breakpoint set and construction of
   the resulting cell/face cover;
2. the clipped-old-edge diameter-one / adjacency assembly in the form expected
   by the mixed-region theorem;
3. combine those with the already verified radial algebra and public
   feasible-checkpoint routing theorem.

The ordinary proof plus executable exact constructor strongly constrain this
work, but they are not a substitute for the final Lean declaration. The
mission discussion comment above explicitly records this boundary.

## 5. Circuit obstruction to a tempting shortcut

The irredundant hexagon

```text
|x|+|y| <= 2,  |y| <= 1
```

has one maximal horizontal row-circuit step from `(-2,0)` to `(2,0)`. The
endpoints have graph distance three, share no tight row, and their segment lies
in no proper face. Rounding the endpoints does nothing because they are already
vertices.

Therefore a general circuit segment cannot simply be substituted for an old
edge in the radial theorem. Taking the whole polytope as its repair support
would insert the unknown target diameter into the assumed budget and would not
solve circuit-to-edge refinement.

## 6. Exact regression suite

`python3 scripts/test_face_preserving_checkpoints.py` uses standard-library
exact rational arithmetic, exhaustive candidate vertex bases, tight-row rank,
and graph searches.

Deterministic coverage includes:

- **1,506** simultaneous-rounding checkpoints across 2D/3D/4D cubes and exact
  4D/5D Dantzig regressions;
- **48** seeded radial multi-cut instances in dimensions 2–4;
- **694** exactly certified affine cells;
- **196** nonvertex checkpoint occurrences;
- at most ten distinct supports in one case;
- every explicitly constructed repaired route within its final-face budget;
- the genuine seven-facet moving sweep and five-facet intersection-loss
  witness;
- the six-row maximal-circuit / no-proper-carrier obstruction.

These finite hull computations are exact certificates, not Lean hull
formalizations and not substitutes for the general proof.

## 7. Remaining global research gaps

`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) remains Open.

PR #50 removes one real obstacle: in a fixed parent, shared **nonvertex**
feasible points already suffice for vertex portals.

It also gives a concrete fixed-final-parent representation for simultaneous
monotone clipping, with polynomial **support count**.

What remains hard:

1. **Lean assembly:** finish the two formal pieces above, then publish the full
   radial clipping theorem only if the end-to-end declaration passes.
2. **Applicability:** prove the desired global projective/Pachner/circuit
   construction supplies the required outer-edge / monotone-clipping model. A
   general circuit step is not an old edge.
3. **Polynomial support cost:** prove polynomial control of `sum_i B_i`; a
   polynomial number of final faces does not imply polynomial total diameter.

The next decomposition should keep representation/applicability and face-cost
control separate and should be regression-tested against the exact Dantzig,
crossing/cube, moving-facet, hexagon, and Q28 examples before creating any new
Open Prove2Me children.
