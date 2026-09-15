# A fixed twelve-facet family also defeats uniform slack-share contraction

This is a second, independent obstruction discovered during review of the
projective-share rule. It concerns the NEW score, not only the old radial gap.
It has three dimensions, twelve genuine facets, twenty simple vertices and
one fixed face lattice for every 0<delta<=1/64. Its first complete-face fallback
reduces rho from 1/3 to (1-13*delta)/3. Thus its relative progress is exactly
13*delta, arbitrarily small. This is NOT a long-path or diameter lower bound:
the tested new routes use six edges, while the true distance is five.

The proof below is written mathematics plus exact finite polynomial
certificates. It is not a Lean or Prove2Me verdict. It does not alter the new
policy or its original 1,016-pair benchmark.

## 1. Original inequalities, with no hidden extension

Use the following nine rational planar sites a_l=(p_l,q_l):

    (1,0), (-3/5,4/5), (-3/5,-4/5),
    (4,1), (1,5), (-4,3), (-5,-1), (-1,-4), (3,-5).

For 0<delta<=1/64 set

    k_l=1-(2*delta/3)(p_l+q_l)-delta^2*(p_l^2+q_l^2).

The ORIGINAL three-dimensional polytope is

    z_1,z_2,z_3 >= 0,
    (k_l+2*delta*p_l) z_1 + (k_l+2*delta*q_l) z_2
                 + k_l z_3 <= 1,     l=0,...,8.            (1)

The target is v=0. The source is

    x=(1,1,1)/(3*(1-delta^2)).                              (2)

The three inner sites have squared norm one and their convex hull contains
zero strictly. At (2) exactly those three roof rows are tight; all remaining
rows have positive slack. Their normals are independent for delta>0, so x is
a simple vertex. Target v has exactly the three coordinate facets tight.

All roof coefficients are positive: |p_l|,|q_l|<=5,
|p_l+q_l|<=6 and p_l^2+q_l^2<=34 give the conservative lower bound
1-14*delta-34*delta^2>0. Hence (1) is bounded, and sufficiently small strictly
positive z is interior. This is an actual full-dimensional original H-model,
not a projected polytope or an assumed graph.

## 2. Fixed angular geometry of the three source facets

For z!=0 put S=z_1+z_2+z_3, u=z/S and t=1/S. The inequalities are exactly

    u>=0, sum u=1,
    t >= 1 + max_l [2*delta*a_l . ((u_1,u_2)-(1/3,1/3))
                    -delta^2*||a_l||^2].                  (3)

With w=((u_1,u_2)-(1/3,1/3))/delta, the dominating-plane comparisons reduce to

    2*a_l.w-||a_l||^2 >= 2*a_j.w-||a_j||^2.                (4)

These are the ordinary nearest-site/Voronoi comparisons, but only the exact
linear identities (4) are used. The three inner-site cells are bounded by
the outer sites. Their vertices, collectively without duplicates, are

    (-491/158, 103/158), (-125/44,0), (-96/35,-151/70),
    (-229/178,617/178), (0,0), (5/4,5/2),
    (4/3,-8/3), (13/9,-49/18), (11/6,5/2), (113/34,-67/34).

They give the entire three source facets, polygons with4,5,6 corners. Every
associated original u-coordinate is positive for delta<=1/64. Consequently
none of those facets or their boundary edges acquires a target coordinate
facet. This is a genuine no-acquisition fallback, not an immediate shortcut
excluded artificially by the selector.

The minimum among the three quantities w_1,w_2,-w_1-w_2 over those vertices
is -13/3, attained at (11/6,5/2). Since the source has equal target slacks,
the normalized target-slack share vector used by the actual policy is exactly
u. Therefore

    rho(x)=1/3,
    min rho over the inspected source facets=(1-13*delta)/3,
    relative decrease=(rho(x)-rho(next))/rho(x)=13*delta.    (5)

The minimum point is reached in two polygon edges. The fixed source-facet
graph and exact direction comparisons make this the policy's first selected
macro. No other inspected point can improve the coefficient in (5).

## 3. Every row is a genuine facet, and the whole type is fixed

For each site a_l choose (u_1,u_2)=(1/3,1/3)+delta*a_l and the corresponding
u_3=1-u_1-u_2. All coordinates are strictly positive in the stated interval.
At that location, its own expression in (4) exceeds every other expression by
||a_l-a_j||^2>0. Set t=1+delta^2||a_l||^2 and z=u/t. Exactly that roof row is
tight. This gives a relative-interior witness for each of the nine roof facets.
The three target coordinate facets have similarly strict roof slack near zero.
Thus f=12 genuinely, rather than a larger redundant input count.

The separate symbolic checker starts from the20 observed active triples at
one rational parameter, but does not infer an all-parameter theorem from that
sample. For every triple it certifies its determinant is nonzero, solves the
three original equalities symbolically, and certifies ALL other original
inequalities strictly for EVERY
0<delta<=1/64. There are20 determinant certificates,60 exact equality checks and180 strict
slack checks.

Each strict rational slack has numerator and denominator represented as a
positive power of delta times a polynomial. Substituting s=64*delta, the
checker reconstructs that polynomial in the Bernstein basis on[0,1]. All
coefficients are nonnegative, at least one is positive, and the coefficient
at s=1 is positive. This proves strict positivity throughout(0,1], not merely
at the five tested parameter values. Both signs of each rational expression
are normalized consistently before this check. The packet stores the exact
coordinate expressions and polynomial coefficient certificates.

These20 vertices have distinct active triples and exactly three tight rows,
so they are distinct simple feasible vertices for every allowed parameter.
For any bounded three-dimensional polytope, Euler's equation and degree>=3
give v<=2f-4. With f=12, twenty already attains that upper bound. No additional
vertices or hidden nonsimple vertices can remain. All facet/vertex incidences,
and hence the whole face lattice and edge graph, are therefore fixed for the
entire interval. This is a proved coverage argument, not a supplied complete
vertex list that the checker simply trusts.

For every vertex incident to a source facet, the symbolic checker additionally
proves that its scaled angular coordinates w are constant in delta and equal
to the listed finite set, with minimum coordinate -13/3. Combined with the
complete incidences, this validates the entire source-star calculation in (5).

## 4. What was actually run

    python3 scripts/test_angular_roof_barrier.py

Five exact instances delta=2^-k, k=6,10,40,120,240, each reconstruct the original
H-graph independently and verify the complete new route against it. Every
instance has20 vertices,30 edges,12 facets,first macro2 edges,full route6 edges,
and independent source-target distance5. The exact first relative gain is
13/2^k. Vertex active sets and scaled angular source-star vertices agree across
all five numerical instances. The parameter certificate separately proves
that these incidences and first-gain formula hold on the entire interval.

The total six-edge policy trajectory is numerically checked at those five
values; its same exact sequence for all real delta is NOT asserted just from
sampling. The five-edge graph distance follows for all parameters from the
separate proved constant face lattice. Neither is an exponential trajectory.

A clean dependency replay reproduces the parameter certificates and all
numerical fields after removing elapsed time, and both stored full fixtures
are byte-identical. The script uses SymPy to construct and simplify symbolic
rational coordinates, then checks polynomial identities/sign certificates.
It is exact research software, not a verified symbolic algebra implementation
or a Lean-extracted certificate checker.

## 5. Consequence for the larger proof strategy

The old radial gap can be made arbitrarily uninformative by a positive
projective re-encoding. The new share score avoids that artifact: its route
is projectively equivariant. But this genuine deformation shows that even an
invariant local angular gain need not have a coefficient-independent positive
fraction, while both dimension and the ENTIRE combinatorial type stay fixed.
No claim is made that the deformations themselves are projectively equivalent;
indeed the invariant measured gain changes.

Thus the new score is not a missing uniform geometric contraction theorem.
Its permanent facet-subset accounting remains valid and its coefficient is
improved by shortest macros, but the potentially exponential number of
macros remains. A successful polynomial argument needs a global invariant or
structural control not reducible to a uniform fractional decrease of either
of these numerical potentials. This result narrows a proposed argument; it
does not rule out polynomial original-edge routes or solve Polynomial Hirsch.
