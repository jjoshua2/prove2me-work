# Constructing finite-face routes from actual coordinate levels

## Exact public theorem

Let vertices be indexed by Fin n. They carry a symmetric relation R and an
injective real coordinate map c : Fin n -> Fin d -> Real. A specified family
Face of finite vertex subsets satisfies these four LOCAL structural properties:

1. Taking the nonempty minimum set of any coordinate preserves Face.
2. Taking the nonempty maximum set of any coordinate preserves Face.
3. In every member, a vertex that is not coordinate-minimal has an R-neighbor
   in that member with a strictly smaller coordinate.
4. The analogous single-step property holds in the increasing direction.

For any F in that family and u,v in F, the theorem constructs an indexed finite
R-walk entirely inside F, from u to v, of length at most

    sum_j (card(image of coordinate j on Fin n) - 1).

The actual real coordinate images occur in the conclusion. They are not a
supplied cardinality or alleged complete small catalogue. The theorem does
not assume connectivity, an existing route, a short phase, or a bound on paths.
The conclusion explicitly gives L and p : Nat -> Fin n with p(0)=u, p(L)=v,
all visited vertices in F, and R(p(i),p(i+1)) for each i<L.

The structural one-step and closure hypotheses are explicit. In the intended
polyhedral application, Face is a family of actual vertex sets of compact
polytope faces and R is ORIGINAL ordinary-edge adjacency. The public target
is a finite combinatorial interface; it does NOT contain or prove that entire
geometric instantiation. It also does not prove research #277's cut-image
alphabet construction, a universal polynomial global alphabet, or Polynomial
Hirsch. Those claims must not be inferred from an eventual acceptance.

## Proof construction

First use integer-valued coordinates bounded by K_j. The internal Route record
stores an actual finite walk, including endpoint equalities, every intermediate
membership, and every adjacency. Its nil, prepend, reverse, inclusion and
concatenation constructions are proved directly. There is no primitive path
existence or concatenation axiom.

A well-founded induction on an integer coordinate builds a decreasing walk
until its attained minimum. Each step decreases by at least one. If m is the
minimum, its length plus m is at most the starting value. Applying the same
argument to K-f gives ascent to an attained maximum, with length plus the
starting coordinate at most that maximum. Reversal uses the specified symmetry
of R, not an assumed orientation change.

The main induction removes coordinates from a finite set J of coordinates
still allowed to vary. All other coordinates are constant on the current
finite face. Choose a coordinate j in J. If the two endpoints' values a,b
satisfy a+b <= K_j, descend BOTH to the same minimum-j subset. Otherwise ascend
both to the same maximum-j subset. Finite-set extrema exist; neither endpoint
of the intermediate walks nor their lengths are supplied.

The sum of the two walk lengths is at most K_j. In the descending case,
L1+m <= a and L2+m <= b. In the ascending case, L1+a <= M and L2+b <= M,
with M<=K_j and a+b>K_j. The appropriate elementary integer inequalities give
the joint budget. Both resulting endpoints lie in the SAME smaller admissible
face, though not necessarily at the same vertex. Coordinate j is now fixed.
Apply the induction hypothesis there and concatenate the two outer walks with
the middle walk. Inclusion transports all middle vertices back to the original
F. Once J is empty, coordinate injectivity makes the endpoints equal.

Finally rank each REAL value in its ACTUAL finite coordinate image by the
number of smaller levels. The proof establishes strict-order preservation,
equality reflection on those levels, and rank <= card(levels)-1. These facts
transport all four local hypotheses to the rank coordinates without moving
vertices or changing adjacency. The integer theorem then gives the stated
real-level sum bound. This is combinatorial ranking, not nonlinear geometric
rounding into a new polytope.

The proof covers u=v and d=0. When d=0 and endpoints exist, injectivity already
implies they coincide. Empty coordinate images cannot occur with a supplied
endpoint. Empty Face members impose no one-step/extremum witness obligation.
The walk need not be shortest, nonrevisiting, or monotone for one common linear
objective. Those properties are not in the statement.

## Connection and attribution

This is the finite construction underlying the classical coordinate-extreme
argument of Kleinschmidt and Onn, used in the project's research #274 and #277.
The new work is its standalone formal proof with actual rank images, bounded
walk construction and membership transport, not a historical diameter discovery.

Peter Kleinschmidt and Shmuel Onn, On the diameter of convex polytopes,
Discrete Mathematics 102 (1992), 75-77, DOI 10.1016/0012-365X(92)90349-K.
Alexander E. Black, Small Shadows of Lattice Polytopes, arXiv:2204.09129.
The ordinary-vs-monotone distinction is essential; the present theorem makes
no single-objective monotone claim. Research #277's common-face detour example
and the accepted all-affine-level obstruction #280 remain unchanged.

The next geometric adapter must supply the actual finite vertex enumeration,
edge relation, separating coordinate functions, extreme-face closure and
single-edge improvement facts. These are meaningful hypotheses, not silently
proved by this packet. Even after that adapter, using this result for a
polynomial Hirsch theorem would require a suitable polynomial or adaptive
level budget; no such universal assumption has been discharged here.

## Verification boundary

The source is standalone and imports Mathlib only. Its public preamble contains
only that import, the BigOperators scope and autoImplicit setting. The internal
Route type is NOT present in the target type, avoiding the local-type preamble
mismatch that affected earlier packets. The solution type and problem.json
formal statement are checked textually, changing only the public theorem name.
The committed Lean/Mathlib pin is unchanged.

No Lean or Lake executable was present in this runtime and the direct
raw.githubusercontent.com preflight failed at DNS resolution. Plugin discovery
returned no relevant Lean compiler. Thus no local compile is claimed. At the
user's request, this prepared complete source is intended for the existing
exact-head compile/axiom/publication gate invoked by a NEW top-level PR comment.
A compiler failure must stop publication, and only the trusted publisher's
actual authenticated receipt can establish Prove2Me acceptance.

The independent semantic test checks the local hypotheses and constructs finite
walks on 32 finite graph models, including grids, affine cubes, convex cycles,
simplices, crosspolytopes and the zero-dimensional singleton. It checks 257
admissible face sets, 1,623 local improvement requirements, and 2,451 routes,
including nontrivial initial faces. Those walks total 6,733 edges versus 4,697
shortest-path edges; 812 are nonshortest and are not hidden. Four explicit
countermodels show failures when local improvement, injectivity, symmetry or
extreme-face closure is omitted. These are finite software checks, not Lean
verification or independently verified geometric realizations of every model.
