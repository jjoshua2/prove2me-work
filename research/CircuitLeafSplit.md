# Circuit routing and edge refinement for the exact Hirsch leaf

Target: `Hirsch.polynomial_access_to_given_supporting_face`, UUID
`33fc334e-e05b-4090-ac49-f83fd94d9305`.
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## What this split does and does not prove

The parent proof is a conditional reduction, not a solution of polynomial
Hirsch. One child is a source-backed formalization target. The other is an
explicitly conjectural circuit-to-edge conversion, retaining the essential
polynomial-Hirsch difficulty. Neither child is proved just by checking the
parent. This is not a claim to split the conjecture into two routine lemmas.

The useful distinction is geometric: short relaxed routes now have a
published mathematical construction, whereas turning those routes into
vertex-edge walks still requires new work. The split separates those jobs
and identifies the obstruction to using the relaxed construction directly.

## Child A: cubic circuit routes in an irredundant presentation

`Hirsch.cubic_circuit_walk_bound` asserts that for separated extreme endpoints
u,v of a bounded n-row H-polytope, one can retain m <= n original rows,
without changing the feasible set, so the presentation is irredundant and
strictly feasible and there is a padded maximal circuit route of length
C_c (m+d)^3 from u to v.

The source is Bento Natura, *Circuit Diameter of Polyhedra is Strongly
Polynomial*, arXiv:2602.06958v2 (10 February 2026), Theorem 3.1 and Corollary
3.2: https://arxiv.org/html/2602.06958v2 . The standard-form bound is
O(r^2 log r), where r is the equation rank. A cubic envelope is sufficient
here. The source's circuit augmentations may have nonvertex intermediates;
the source does not prove Child B.

`HirschCircuit.exists_irredundant_strict_model` provides a separate concrete
proof of preprocessing, independent of the numerical circuit bound:
choose a minimum-cardinality subfamily defining the original set. Removing
any retained row changes the set, yielding an explicit violation witness.
Every retained row is nonzero because u is feasible. The midpoint of u,v is
strict on every retained row by endpoint separation. Reindex by Fin m.
This argument needs neither boundedness nor extremality of the endpoints.

The remaining source formalization proceeds through slack coordinates.
For retained row matrix A, boundedness and nonemptiness force A to be
injective: a nonzero kernel direction would give an unbounded feasible line.
The affine map x -> b-Ax identifies P with nonnegative points in b-range(A).
Choose equations M s=q with ker(M)=range(A); equation rank is at most m.
Support-minimal row directions correspond to elementary kernel vectors in
slack space; feasibility, extremality and maximal augmentations transfer.
Apply the source theorem and pad, treating the zero-dimensional case
separately. These source arguments are formalization tasks, not imported
axioms or an already accepted platform result.

## Child B: polynomial edge replacement -- open research

`Hirsch.polynomial_edge_refinement_of_circuit_walks` asks whether there are
uniform constants C_e,k_e such that any length-L maximal circuit route
between vertices of an irredundant, strictly feasible bounded m-row
H-polytope can be replaced by a graph walk with at most

    C_e (m+d)^k_e L

steps. Intermediate points of the replacement may differ. They need not
visit the nonvertex circuit intermediates. No monotonicity, unit-cost
per-step replacement, or permanent retention of visited facets is required.

The restriction to irredundant presentations is deliberate. Redundant
inequalities can change the circuit directions without changing the graph.
Child A removes this freedom rather than silently manufacturing useful
circuits with additional rows.

## Exact implication to the original leaf

Assume A and B. Use A to obtain m retained rows and a circuit route of length
L=C_c(m+d)^3. Use B in this presentation. The resulting genuine edge budget is

    C_e(m+d)^k_e C_c(m+d)^3
      = C_e C_c (m+d)^(k_e+3)
      <= C_e C_c (n+d)^(k_e+3).

The two presentations define exactly the same subset, hence exactly the
same vertices and edges. Pad at v to the last budget. Choose z=v in the
original leaf. The originally supplied supporting row remains tight at v,
even if it was removed from the irredundant subfamily. In particular this
is access to the SAME given supporting face, not a chosen alternative face.

`Solutions/Sol_Hirsch_leaf_circuit_split.lean` has the exact original leaf
signature and imports only the two children, never its own target.
`scripts/check_circuit_leaf_split.py` also produces an implication with the
two children as explicit hypothesis arguments. Its axiom audit must contain
only propext, Classical.choice, Quot.sound. The imported-stub version may
add sorryAx solely because the two children are Open. Neither audit proves
the hypotheses themselves.

## The active-row obstruction

At a vertex x, take a feasible nonzero direction g and put

    J = {i : <a_i,x>=b_i and <a_i,g>=0}.

For a maximal positive segment, these are the rows tight throughout the
segment. In a full-dimensional H-polytope its carrier is one-dimensional
precisely when rank(A_J)=d-1. A circuit only guarantees rank d-1 from ALL rows
orthogonal to g, including inactive ones. It need not give d-1 independent
ACTIVE rows. Thus a maximal circuit augmentation need not be a graph edge.

The one-balance box pivot succeeds because its moving pair includes the only
possible interior coordinate. Every other coordinate is at a bound, so the
carrier has dimension one. This condition is not established for arbitrary
H-polytope circuit directions.

A possible route into Child B is an amortized replacement through the
higher-dimensional carriers. The existing low-rank, product-factor and
clipping lemmas handle certain carrier geometries, but no uniform bound for
all remaining carriers is proved here.

## Exact counterexample to dimension-only conversion cost

For k>=1 let r=k+1/2. Form an upper chain

    (x, r^2-x^2), x=-r,-r+1,...,r,

and its reflection in the horizontal axis, excluding duplicate endpoints.
Their convex hull is a strictly convex (4k+2)-gon with irredundant edge
inequalities and a strict feasible origin.

The extreme endpoints u=(-r,0),v=(r,0) are joined by ONE maximal horizontal
row-circuit augmentation. The top and bottom rows are horizontal facets;
any nonzero direction with smaller row support would also have to be
horizontal, so it has exactly the same support. A row through v with
positive horizontal normal component certifies maximality.

The graph is a cycle and u,v are antipodal, so their edge distance is
2k+1=n/2. No constant depending only on dimension can bound conversion cost.
This does not refute the polynomial row-dependent overhead in Child B.
The accompanying exact-rational checker reconstructs all vertices and
edges and verifies row-deletion witnesses for k=1,2,4,8,16. The distances are
3,5,9,17,33, respectively, with circuit length one in each example. These
finite diagnostics are not additional Lean-verified theorems.

## Publication boundary

The API helper probes by default. It never prints credentials or commits
keys; it reads PROVE2ME_API_KEY or the gitignored local credentials file.
Authenticated redirects are disabled. A user-provided key in chat is not
thereby installed as a GitHub Actions secret.

Only after reviewing the equivalent-result search and successfully checking
the exact proof files should an authorized agent run:

    python3 scripts/circuit_leaf_api.py --publish-reviewed

This publishes the definition, then the two explicitly Open child problems,
then submits the parent sketch and records actual publication/submission IDs.
A SKETCH_ACCEPTED verdict is NOT Proved while either child remains Open.
