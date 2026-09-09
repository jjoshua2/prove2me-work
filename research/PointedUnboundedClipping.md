# Pointed unbounded clipping: one exterior-cap correction

Date: 2026-09-09. Repository: `jjoshua2/prove2me-work`.
Branch: `chatgpt/recession-cap-clipping`, based on PR #51 commit
`845ea75786db5520115d0000a1d7690c164b2d94`.

## Evidence and scope

This note gives a complete ordinary mathematical proof of the pointed-polyhedral
statement below. No novelty relative to the literature is claimed. Its purpose
is to resolve the explicit ray obstruction left by the preceding bounded-clipping
continuation and identify what the remaining cost problem actually requires.

`Solutions/PolynomialExteriorCapClipping.lean` contains seven new declarations,
culminating in an end-to-end **exterior-cap-witness** diameter theorem. Its
hypotheses explicitly supply a compact truncation, a convex exterior cap, the
old-vertex routing bound, the new-cap-vertex classification, and a strict centre.
The universal polyhedral construction/classification of that cap is proved in
ordinary mathematics here, not yet formalized as a general H-polyhedron Lean
lemma. The removal of strict feasibility below is also an ordinary argument.
The source chain passed Actions run `34411257813` at commit
`d7f6385796a16e9c869212674baf359bb3187300`: seven required declarations,
77 axiom reports, only `propext`, `Classical.choice`, and `Quot.sound`.
The offline packet separately records the later standalone check and exact
regression outcome; source verification does not substitute for that check.

The exact rational test scripts were executed on all final vertex pairs of 31
instances. These are finite geometric certificates, not Lean hull theorems or
a replacement for the general proof. No Prove2Me API call, theorem registration,
submission, or publication is performed by this branch. The user handles publication.

## 1. Main mathematical theorem

Let Q be a nonempty **pointed convex polyhedron** in finite-dimensional real
Euclidean space. Pointed means that Q contains no affine line. Q may be unbounded.
Assume its finite extreme-vertex/edge graph has padded diameter at most D.
For finitely many linear inequalities put

    P = Q ∩ ⋂_i {x : f_i(x) ≤ b_i},
    F_i = P ∩ {x : f_i(x) = b_i}.

Assume P is compact and every final cut face F_i has intrinsic graph diameter
at most B_i. All B_i are explicit nonnegative integer hypotheses. Then

    DiamLE P (D + 1 + Σ_i B_i).

This includes newly created endpoints and cases where no original vertex
survives. For bounded Q the preceding theorem gives the better D + Σ_i B_i.
Neither the number of rays nor the diameter of a truncating cap occurs in the
new bound. The correction is ONE, not two and not one per ray.

Strict feasibility of the added cuts and full dimensionality are unnecessary
for this ordinary statement; section 7 handles the exceptional cases. Pointedness
is retained. No extension to arbitrary line-containing polyhedra is asserted.

## 2. Construct a finite cap beyond every relevant point

Write Q = {x : A_j x ≤ c_j, j=1,...,n}. Its recession cone is

    K = {r : A_j r ≤ 0 for every j}.

Pointedness implies that the common kernel of all rows is zero: otherwise x+t r
would be a line in Q. Define the completely explicit linear functional

    ell(x) = -Σ_j A_j x.

For every nonzero r in K, at least one A_j r is negative and none is positive,
so ell(r)>0. This works with redundant rows and with affine equations encoded
as two opposite inequalities. It does not assume a simplicial recession cone.

There are finitely many vertices of Q: each vertex has a full-rank collection
of tight rows and therefore is the unique solution for at least one of the
finitely many full-rank row bases. A nonempty pointed polyhedron has a vertex.
Choose M strictly greater than ell at every such vertex and everywhere on P.
The latter is possible by compactness of P. Put

    R = Q ∩ {x : ell(x) ≤ M},
    G = Q ∩ {x : ell(x) = M}.

R is compact. For completeness, if it were unbounded, fix x0 in R and take
x_k in R with ||x_k-x0|| tending to infinity. A subsequence of normalized
(x_k-x0) tends to a unit vector r. Dividing every defining inequality by the
norm and taking limits gives A_j r≤0 and ell(r)≤0, contradicting ell(r)>0.
R is closed because it is an intersection of finitely many closed halfspaces.

The cap G is convex, G⊆R, and G∩P is empty. The final polytope is unchanged:

    P = R ∩ ⋂_i {x : f_i(x) ≤ b_i}.

G is not a face of P and must NOT be assigned a diameter budget as though it
were. It is a temporary exterior part of the compact outer parent R.

## 3. Exact structural classification of cap vertices

Let V be the finite vertices of Q. Every member of V remains a vertex of R,
and every bounded edge between two old vertices remains an edge: its whole
segment lies strictly below M.

Every vertex z of R is either in V, or lies in G and is adjacent in R to a
member of V. Here is the geometric proof, including the ray step.

If ell(z)<M, the cap inequality is locally inactive. Any nontrivial segment
of Q witnessing failure of extremeness can be shortened about z to stay below
M, so z must already be a vertex of Q.

Suppose instead z is new and ell(z)=M. At a vertex of R, the active rows of
Q together with the cap row span the ambient dual space. The old active rows
cannot already have full rank, since that would make z an old vertex above
our chosen bound. Their rank is therefore exactly d-1. Their common tight
face in Q has dimension one. This rank assertion remains valid for a
lower-dimensional Q because its affine-hull equations are among the active
constraints.

A one-dimensional face of a pointed polyhedron is a segment or a ray, not a
line. It cannot be a bounded segment: both of its endpoint vertices would
have ell<M, as would every point between them, whereas ell(z)=M. Thus it is
an unbounded edge/ray, with a finite endpoint a∈V. Since ell grows strictly
along its recession direction, the cap cuts the ray exactly once, at z.
Its intersection with R is the genuine edge [a,z]. This proves the required
adjacency rather than assuming a missing graph connection.

These finite-vertex/ray facts are standard polyhedral geometry. The ordinary
argument above spells out their use; the current Lean theorem takes their
resulting classification as an explicit input, not as an unproved imported axiom.

## 4. One shared exterior correction, by four endpoint cases

On the vertices of R, temporarily allow either a genuine R edge or a straight
shortcut between any two cap vertices. This is an auxiliary relation, NOT a
claim that cap chords are edges.

Every pair of R vertices has an auxiliary route of length at most D+1:

| Endpoints | Construction | Budget |
|---|---|---:|
| old, old | use the Q finite-vertex route; its edges survive in R | D |
| old, cap | route to the cap endpoint's adjacent old ray base, then its edge | D+1 |
| cap, old | reverse the preceding construction | D+1 |
| cap, cap | one straight chord inside the convex cap | 1 |

In particular, cap-to-cap does NOT need to descend along one ray, traverse
the old graph, and ascend another ray. That is why a +2 estimate is avoidable.
The Lean declaration `exterior_cap_augmented_route_bound` proves this exact
classification-to-route implication, including D=0 and equal endpoints.

The test suite verifies the cap classification and actual adjacent old bases
with exact ranks for each input. It also exercises cap chords which are not
edges; these are marked as exterior shortcuts and never counted as final edges.

## 5. Retract every exterior shortcut into the already-paid final faces

First take a centre o∈P strict for the added cuts and define

    s_i = b_i - f_i(o) > 0,
    mu(x) = max(1, max_i (f_i(x)-f_i(o))/s_i),
    rho(x) = o + (x-o)/mu(x).

The already-developed radial lemmas imply that rho is continuous, maps R into
P, and fixes P. Every point either is fixed or retracts onto a final cut face.

For x∈G, the fixed alternative is impossible: x is outside P, but rho(x)∈P.
Therefore rho(G) is covered entirely by the union of the F_i. It is connected,
as the continuous image of a convex set. In particular, an arbitrary cap chord
retracts to a genuine connected trace through those same fixed final faces.

This is the geometric point which avoids paying the cap's own diameter.
The cap is outside the final polytope, so every one of its images is already
covered by a final support. A large or complicated cap creates no additional
intrinsic-face-diameter term.

## 6. New final vertices and the final route

Let u be a vertex of P. If u is already a vertex of R, no attachment is needed.
Otherwise some added cut is tight at u. Choose that cut i and an R vertex a
maximizing f_i, which exists by compactness. Then f_i(a)≥f_i(u)=b_i. Every point
of [u,a] is on or beyond this cut, so rho([u,a]) lies entirely in the union of
the final cut faces. This attachment may change its active cut label; it is
not required to remain in F_i.

Do the same for v and obtain an R vertex c. Join a to c using section 4's
auxiliary route. The two endpoint spokes and the auxiliary route form a
connected trace in R. Its radial image is connected, contains u,v, and is
covered by:

* final cut faces F_i;
* intersections with P of the genuine R edges used in the route;
* any necessary endpoint/initial singletons at cost zero.

A clipped genuine edge is a closed extreme face of P and is convex and
collinear, so its intrinsic graph diameter is at most one. Stays require no
new support. Exterior cap chords need no clipped-edge support at all, because
their images are already covered by F_i.

The finite closed-face cover theorem converts this connected trace into a
path in the actual face-intersection graph. Intersections supply shared parent
vertices by compactness. A simple path of support labels charges each face
only once, across BOTH endpoint spokes and the entire middle route.

There are at most D+1 genuine edge segments, giving

    dist_P(u,v) ≤ D + 1 + Σ_i B_i.

The ordinary construction is slightly sharper in the cap/cap case: there are
no paid real edges, so that pair is handled with Σ_i B_i alone. The all-pairs
script checks this refinement. The current main Lean theorem states only the
uniform D+1+Σ_i B_i bound.

## 7. Remove the strict-centre assumption in ordinary mathematics

If P is empty, DiamLE is vacuous. If a final cut face F_i equals all of P,
its assumed budget B_i already gives the desired larger bound.

In the remaining case, for each cut i choose p_i∈P strict for that cut. A
convex average with every coefficient positive is strict for every cut:
all slacks are nonnegative, and each row gets a positive contribution from
its selected witness. The empty cut family is immediate. This supplies the
strict centre used above. It is not a hidden full-dimensionality assumption.

The present Lean cap theorem keeps a strict centre as an explicit binder.
Do not advertise that source as the strictness-free H-polyhedron theorem.

## 8. Exact executed tests

`scripts/test_recession_cap_clipping.py` uses the standard library, exact
fractions, exhaustive row-basis vertex enumeration, and exact recession-ray
classification. It verifies that the chosen ell is positive on every
extreme recession ray, the final polytope has no recession directions, the
far cap is redundant for P, all original edges survive, and every new cap
vertex has an actual old-vertex neighbor.

It then explicitly constructs a final graph route for EVERY unordered final
vertex pair, including identical endpoints, rather than checking just the
numerical diameter inequality. Along each segment it partitions the affine
normalized violations at every rational crossing. Maximality at both cell
endpoints certifies the entire cell. The checkpoint selector preserves all
active rows. Every emitted final step is checked against the exact graph.

Identical segment certificates are memoized, never sampled. Statistics clearly
distinguish the 2,197 distinct certified cells from repeated cell occurrences:

| Quantity | Executed result |
|---|---:|
| Pointed unbounded instances | 31 |
| Final vertex pairs | 2,027 |
| Pairs involving new original-parent endpoints | 1,962 |
| Instances with no surviving original vertices | 14 |
| Distinct exact segment certificates | 635 |
| Distinct affine cells certified | 2,197 |
| Affine-cell occurrences across all pair routes | 22,495 |
| Exterior-cap cell occurrences | 8,345 |
| Nonvertex checkpoint occurrences | 19,854 |
| Old/old lift pairs | 142 |
| Mixed old/cap lift pairs | 328 |
| Cap/cap lift pairs | 1,557 |
| Cap chords used | 791 |
| Cap chords which are not graph edges | 3 |
| Instances refuting the formula without +1 | 2 |

Inputs include orthants, pointed strips, a two-vertex epigraph, nonsimplicial
square cones, frusta excluding their original apex, repeated/redundant cuts,
seeded rational instances, and the actual tangent-cone relaxations of the
existing exact 4D and 5D Dantzig examples. Their final polytopes have 14 and
40 vertices, and all 105 and 820 unordered pairs respectively are included.
Randomness chooses some instances; it is not a proof of the general theorem.

## 9. Why the extra one is real, and what still overcharges

The half-line Q=[0,+infinity) has one finite vertex, hence D=0. Adding x≤1
gives P=[0,1], whose diameter is one, while the final cut face is a singleton
with B=0. Thus the universal pointed extension cannot simply omit +1.
The test suite also detects the same failure for an inset interval with no
surviving original vertex.

A different diagnostic shows why using whole intrinsic face diameters can
still be needlessly expensive even when the geometry is fully correct.
Let K_m be the polygon with vertices (i,i²), i=0,...,m-1. Homogenize it into
a pointed 3D cone Q_m with apex 0 and cut at height z=1. The result P_m is a
pyramid. Every base vertex is adjacent to the apex, so Diam(P_m)=2 for m≥4.
But its unique final cut face is K_m, of intrinsic diameter floor(m/2).
The generic cap bound gives 1+floor(m/2), an arbitrarily large overestimate.

`scripts/test_cap_cost_bypass.py` verifies the complete rational graphs for
m=4,6,8,12,16,20. For m=20, the final cut face and exterior cap both have
diameter 10, while the final parent has diameter 2. It explicitly verifies
the common-apex two-edge route between every pair of base vertices.

Two different lessons must not be conflated:

1. The EXTERIOR cap's diameter is not a needed budget at all, by section 5.
2. A FINAL face's intrinsic diameter may overestimate the cost needed between
   its vertices in the P graph; paths through P may leave that face and be much
   shorter. This does not license assigning a guessed small budget. A genuine
   parent-graph bypass must be exhibited, as the pyramid's apex does here.

The existing generic region-routing theorem already permits local routes that
leave their endpoint region. Therefore this does not call for another generic
routing lemma. A useful next cost experiment is to identify verifiable short
parent-graph connectors for the actual portals, or select a cheaper connected
support subfamily, rather than blindly summing full intrinsic face diameters.
Choosing P itself as a region with its unknown diameter would still be circular.

## 10. Formalization boundary and global frontier

The geometric use of convex exterior shortcuts and the endpoint-attachment
assembly are implemented in Lean. The final cap-witness declaration is

    HirschExterior.simultaneous_clip_diameter_from_exterior_cap

Its structural assumptions are local and concretely checkable: compact R,
convex exterior G, a specified old-vertex set V, routes in D between members of
V, and an actual R-edge from every non-old R vertex to some member of V.
They do not assume a graph diameter bound for P or for G.

What remains before a fully formal unrestricted pointed-polyhedral theorem is
mainly the explicit far-cap construction and vertex/ray classification from
sections 2–3, plus the strict-centre dichotomy. These are different from the
still-open global Polynomial Hirsch research task.

For Polynomial Hirsch, this continuation removes the previously identified
obstruction to using POINTED UNBOUNDED outer relaxations in simultaneous
clipping at the ordinary-mathematical level. It does not bound Σ_i B_i by a
fixed polynomial or prove circuit-to-edge refinement. In a tangent cone D=0,
but the retained final-face budgets still contain the lower-dimensional
routing difficulty. Do not silently assume those faces are balanced.

The formal mission frontier remains
`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`). No cyclic decomposition or new Open
children are created here. PR #51's separate bounded proof branch is unchanged.

## Sources and reproduction

The standard finite vertex/ray framework is reviewed by Komei Fukuda's
Polyhedral Computation FAQ, especially the Minkowski–Weyl section and its
polyhedral representation discussion:
https://cddlib.github.io/polyhedral_faq/
The concrete cap proof is given above instead of importing the desired
clipping conclusion from that reference.

Local proof dependencies are the PR #50 and PR #51 source chain, pinned to
Lean 4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. The cone
regressions use the exact Dantzig coordinates already included in
`scripts/test_face_preserving_checkpoints.py`; no hull dataset is fetched.

    python3 scripts/test_recession_cap_clipping.py
    python3 scripts/test_cap_cost_bypass.py
    ~/.elan/bin/lake build Solutions.PolynomialExteriorCapClipping

The branch workflow performs the strict named-declaration axiom audit and
compares both full fresh regression outputs with the committed SHA-256
certificates in `research/exterior_cap_expected.json`. The detailed JSON
outputs are retained in the offline packet, not just the totals. It
never reads a Prove2Me secret and never calls the platform.
