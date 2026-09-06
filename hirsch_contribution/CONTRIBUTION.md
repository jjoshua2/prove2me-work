# Polynomial Hirsch: a description-level balancing reduction

**Selected target:** `Hirsch.polynomial_hirsch_conjecture`  
**Prepared:** September 4, 2026  
**Status:** Mathematical proof-sketch and supporting drafts only. NOT submitted to Prove2Me. NOT checked by Lean. This is NOT a proof of the polynomial Hirsch conjecture.

## 1. What this contributes

The proposed contribution is a reduction of the mission's general goal to its balanced subfamily: H-polytopes in ambient dimension D described by exactly 2D inequalities. The reduction preserves the polynomial exponent. It supplies a complete mathematical argument for the geometric reduction, while leaving the polynomial bound for the balanced subfamily explicitly open.

The construction adapts the classical Klee–Walkup wedge idea, rather than claiming a new diameter bound. Its useful feature for this mission is that it works at the level of the **given inequality description**. It requires neither an irredundant facet list, full dimensionality, simplicity, nor a pre-existing graph-connectivity theorem.

The public mission states that its n counts defining inequalities, including redundant ones, that d is ambient dimension, and that `DiamLE` allows stationary steps. Those conventions are essential to the formulation below. The exact server definition module and environment could not be retrieved through the authenticated API, so no exact-type Lean submission is claimed.

## 2. Statements

Write E_d = R^d and

    P = { x in E_d : a_i · x <= b_i for i = 1,...,n }.

Assume P is nonempty and bounded. Vertices are extreme points. Distinct vertices are adjacent when their joining segment is an extreme subset of P. Use the mission's padded-walk interpretation of `DiamLE(P,L)`.

### Theorem A — balancing with a diameter-transfer map

There is an H-polytope Q in E_D, described by exactly 2D inequalities, where

    D = d + max(0, n - 2d) = max(d, n - d) <= n + d,

such that Q is nonempty and bounded and, for every natural number L,

    DiamLE(Q,L) -> DiamLE(P,L).

Here all maximum/subtraction expressions in this displayed mathematical formula are interpreted in their usual integer sense with the explicit maximum at zero; the corresponding Lean formula is `d + (n - 2*d)` with natural-number subtraction. The alternative `max(d,n-d)` also holds with natural subtraction.

### Corollary B — balanced polynomial bound suffices

Suppose there are natural numbers C and k such that every nonempty bounded H-polytope Q in E_D with a description of exactly 2D inequalities satisfies

    DiamLE(Q, C * D^k).

Then the mission's goal follows, with the same C and k:

    DiamLE(P, C * (n+d)^k).

Conversely, the mission's general goal with constants c,k implies this balanced hypothesis with constants `C = c * 3^k` and the same k. Thus the two existence statements are equivalent. **The balanced polynomial bound is the remaining conjectural child, not a proved lemma.**

## 3. The generalized wedge

Suppose n > 0 and select any row, relabeled row 1. It need not define a facet. Define

    h(x) = b_1 - a_1 · x,

and construct the subset of E_d x R

    W = { (x,t) : a_i · x <= b_i for i != 1,
                   a_1 · x + t <= b_1,
                   -t <= 0 }.

This is an `(n+1)`-inequality description in ambient dimension `d+1`. Equivalently,

    W = { (x,t) : x in P and 0 <= t <= h(x) }.

Indeed, the last two inequalities imply the removed inequality `a_1 · x <= b_1`; conversely, their conjunction is exactly `0 <= t <= h(x)`.

The projection is `pi(x,t)=x`. There are two affine sections:

    ell(x) = (x,0),       u(x) = (x,h(x)).

Both belong to W for every x in P.

**Nonemptiness and boundedness.** A point x in P gives ell(x) in W. Boundedness of P bounds h on P because h is affine in finitely many coordinates. Since `0 <= t <= h(x)`, W is bounded. This argument also works when h vanishes identically on P.

### Lemma 1 — vertices project to vertices, and bottom lifts are vertices

First, a vertex w=(x,t) of W must satisfy `t=0` or `t=h(x)`. Otherwise, for sufficiently small positive epsilon, both `(x,t-epsilon)` and `(x,t+epsilon)` belong to W and have midpoint w, contradicting extremality.

If `t=0` but x is not a vertex of P, express x as a nontrivial strict convex combination of two distinct points of P. Their bottom lifts express w as the same nontrivial convex combination in W, a contradiction. If `t=h(x)`, use the upper affine section instead. Thus pi sends every vertex of W to a vertex of P.

Conversely, let x be a vertex of P. In any strict convex-combination decomposition of ell(x) by points of W, their nonnegative last coordinates must both be zero. Projecting gives a decomposition of x in P, so extremality forces both points to equal ell(x). Consequently ell(x) is a vertex of W. In particular, pi is surjective on vertices, with ell as a section.

### Lemma 2 — an edge projects to an edge or a point

Let E=[p,q] be an edge of W. If pi(p)=pi(q), its projection is a point and the claim is immediate. Assume pi(p) != pi(q).

Consider the midpoint m of p and q. If m were strictly between the lower and upper affine boundaries, then `m+(0,epsilon)` and `m-(0,epsilon)` would both belong to W for sufficiently small positive epsilon. Since E is an extreme subset of W and contains their midpoint, it must contain both of these points.

That is impossible: projection is injective on the affine line through p and q because their projections are distinct. This line cannot contain two distinct points with the same projection. Hence m lies on the lower boundary `t=0` or the upper boundary `h(x)-t=0`.

The functions t and h(x)-t are nonnegative affine functions on W. If either is zero at m, it is zero at both endpoints and throughout E. Thus E is contained entirely in one of the two sections ell(P) or u(P).

Projection now identifies E affinely with `[pi(p),pi(q)]`. To verify extremality directly, take a strict convex combination of points r,s in P whose result belongs to this projected segment. Lift r and s by the section containing E. Affineness puts their lifted convex combination in E. Extremality of E forces both lifted points into E, so r and s lie in the projected segment. Therefore the projected segment is an extreme subset of P. Its endpoints are distinct vertices by Lemma 1, so it is an edge in the exact sense used by the mission.

This proof makes no assumption that h vanishes on a facet. It covers a redundant row with positive slack everywhere, a row tight only at a vertex, a row tight on all of P, and lower-dimensional P.

### Lemma 3 — diameter bounds descend through the wedge

Assume `DiamLE(W,L)`. For vertices x,y of P, Lemma 1 gives vertices ell(x),ell(y) of W. Take an L-step padded walk between them. Project every vertex of that walk using pi.

By Lemma 1, all projected points are vertices of P. By Lemma 2, an edge step projects to an edge step or a stationary step; a stationary step also remains stationary. The projected walk therefore witnesses an L-step padded walk from x to y. Since x and y were arbitrary,

    DiamLE(W,L) -> DiamLE(P,L).

Notice that the proof does not assume connectivity in advance. It transfers the walk whose existence is asserted by the hypothesis.

## 4. Proof of Theorem A

### Case n <= 2d

Append `2d-n` tautological rows `0 · x <= 1`. This leaves the set P unchanged, gives a description with exactly 2d inequalities, and takes D=d. The diameter transfer is the identity.

### Case n > 2d

Apply the generalized wedge `m=n-2d` times. At each step, there is at least one row to select. Each step raises both the ambient dimension and the number of describing inequalities by one, preserves nonemptiness and boundedness, and has the diameter-transfer property of Lemma 3.

After m steps,

    D = d+m = n-d,
    N = n+m = 2(n-d) = 2D.

Composing the diameter transfers proves Theorem A. The resulting ambient dimension satisfies D <= n+d.

There is also a closed-form description. Keep selecting the augmented copy of the first row. After m wedges the description is

    a_i · x <= b_i                     (i != 1),
    a_1 · x + t_1 + ... + t_m <= b_1,
    -t_j <= 0                         (j = 1,...,m).

It has n+m rows in d+m coordinates. Projection onto the original x-coordinates is the composite diameter-transfer map.

### Zero-dimensional and other boundary cases

For d=n=0, padding does nothing and Q=P. The unique point in E_0 needs only stationary walks. If d=0<n, the wedge construction still applies, even if some or all rows have zero slack. No actual increase in affine dimension is required: the parameter is ambient dimension. No step of the argument assumes distinct lower and upper sections.

To work in the mission's exact `EuclideanSpace R (Fin (d+1))` rather than `E_d x R`, transport the construction through the standard linear equivalence obtained by splitting the last coordinate. Affine bijections preserve extreme points, extreme segments, and padded walks; this transport must be formalized rather than assumed to be definitional equality.

## 5. Proof of Corollary B and converse

Choose Q,D from Theorem A. The conjectural balanced bound supplies

    DiamLE(Q, C*D^k).

Transfer it to P. Since D <= n+d, natural-number exponentiation and multiplication are monotone, and padding a walk preserves validity. Hence

    DiamLE(P, C*D^k) -> DiamLE(P, C*(n+d)^k).

This proves the implication to the mission's goal.

For the converse, apply the mission's bound to a description with n=2D and d=D. The resulting bound is

    c*(2D+D)^k = c*(3D)^k = (c*3^k)*D^k.

These identities also hold for k=0 and D=0 with the usual natural-number exponentiation convention.

## 6. Proposed Prove2Me decomposition

The target remains `Hirsch.polynomial_hirsch_conjecture`.

Suggested direct children:

1. **`balanced_hpoly_transfer`** — Theorem A, with its actual H-polytope coefficient witnesses and `forall L, DiamLE Q L -> DiamLE P L`. The geometric proof above is complete on paper; it still needs a Lean formalization.
2. **`balanced_polynomial_bound`** — existence of C,k giving `DiamLE Q (C*D^k)` for all nonempty bounded H-polytopes described by 2D inequalities. This child remains conjectural.
3. Reuse or prove the mission's **monotonicity of `DiamLE`** if it is not already available.

Useful reusable infrastructure below the first child includes affine-equivalence transport, padding of inequality descriptions, the generalized wedge's vertex/edge projection properties, and transfer of padded walks through a vertex-surjective map that sends edges to edges or stationary steps.

The intended root proof is a reduction, not a direct proof of the conjecture. It should import the two children, specialize the balanced bound, transfer the walk, and increase the numerical bound. It must not import its own target. The generic Lean draft in this package illustrates the logical composition but is **not** an exact-type mission submission.

## 7. Validation and limitations

The accompanying `check_wedges.py` performed exact rational vertex/edge enumeration for **52 one-step wedges** and **13 fully balanced systems**. All checks passed. Checks included projection of every enumerated vertex, existence of every bottom vertex lift, edge-or-point projection for every enumerated edge, and nondecrease of graph diameter.

Examples include triangles, squares, a hexagon, a tetrahedron, an octahedron, a segment in ambient dimension two, a singleton in ambient dimension two, zero-dimensional systems, redundant positive and zero-slack rows, and a redundant row tight only at one vertex. These finite checks are safeguards against construction errors; they do not prove the general theorem and are not Lean verification.

**Not completed in this environment:** authenticated mission/milestone inspection, exact server definition retrieval, Lean installation/compilation, child-theorem publication, root-sketch submission, or receipt of any submission ID/verdict. The command environment could not resolve prove2.me, and the read-only web fetch rejected start.md's Markdown content type. Official setup and solver documentation were instead read from the linked public GitHub workspace. No credentials are included in this package.

## 8. Attribution and sources

- Prove2Me, *The Polynomial Hirsch Conjecture*, mission description and public frontier, accessed September 4, 2026. In particular: inequality-count convention, ambient-dimension convention, adjacency via extreme segments, padded-walk diameter predicate, and the displayed goal.
- F. Santos, *Recent progress on the combinatorial diameter of polytopes and simplicial complexes*, arXiv:1307.5900, Section 4.2, Lemma 5: classical wedge/d-step lemma attributed to Klee–Walkup. The construction above is an elementary description-level adaptation; no novelty claim is made.
- Prove2Me official workspace, `SKILL.md` and `references/mission_solver.md`: exact-type `solution` requirement, distinction between direct proofs and reductions, child theorem workflow, and local compilation requirement.

Source locations for a continuing agent:

```text
https://prove2.me/start.md
https://prove2.me/missions/The%20Polynomial%20Hirsch%20Conjecture
https://arxiv.org/html/1307.5900v1
https://github.com/prove2me/prove2me_workspace
```
