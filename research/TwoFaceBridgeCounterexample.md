# Counterexample to the arbitrary-facet 2-face bridge claim

## Summary

The September 2009 Polynomial Hirsch discussion proposed the following central
claim for a Dantzig figure `(P,x,y)`:

> If `F` is a facet containing `x`, then some vertex of `F` is 2-adjacent to
> `y` (equivalently, a 2-face contains `y` and a vertex of `F`).

This claim is false even for a **good simplex facet** and even when the
Dantzig pair has distance exactly `d`. There is an explicit rational
4-dimensional example, and taking products with cubes gives counterexamples
in every dimension `D >= 4`.

Historical discussion:
https://gilkalai.wordpress.com/2009/08/09/the-polynomial-hirsch-conjecture-discussion-thread/
(see comments 60--65 for the 2-face claim and the gap in its attempted proof).

## A realizable simplicial dual

Start with a 4-simplex on vertices `0,1,2,3,4` and stack successively beyond
facets

```text
{0,1,3,4}
{0,3,4,5}
{0,1,2,3}
```

The resulting simplicial 4-polytope `Q` has 8 vertices and the following 14
facets:

```text
0124  0127  0135  0137  0145  0234  0237
0346  0356  0456  1234  1237  1345  3456
```

An exact rational realization is

```text
q0 = (0,     0,       0,      0)
q1 = (1,     0,       0,      0)
q2 = (0,     1,       0,      0)
q3 = (0,     0,       1,      0)
q4 = (0,     0,       0,      1)
q5 = (1/4,  -1/5,     1/4,    1/4)
q6 = (1/20, -21/320,  5/16,   5/16)
q7 = (1/4,   1/4,     1/4,   -1/16)
```

The facet list above was rechecked with exact rational affine determinants;
all 14 listed facets are supporting tetrahedra.

Take the two disjoint facets

```text
X = {3,4,5,6}
Y = {0,1,2,7}.
```

After polarity they become the estranged vertices `x,y` of a simple
4-dimensional Dantzig figure `P` with 8 facets.

Choose the primal source facet `F6`, dual to vertex `6` of `Q`. The four
primal vertices in `F6` correspond to the dual facets

```text
{0,3,4,6}
{0,3,5,6}
{0,4,5,6}
{3,4,5,6} = X.
```

Their intersections with the target tight set `Y={0,1,2,7}` have sizes
`1,1,1,0`. In a simple 4-polytope, two vertices lying in a common 2-face
must share at least `d-2=2` facets. Hence **no vertex of `F6` is 2-adjacent
to `y`**.

Moreover vertex `6` of the simplicial dual has neighbors only
`{0,3,4,5}`. Thus `F6` has only 4 ridges: it is a tetrahedron, much better
than the old sufficient threshold `2d-2=6`.

The Dantzig pair is extremal. There is a primal path

```text
3456 -> 0346 -> 0234 -> 0124 -> 0127
```

of length 4. Since the endpoints are simple and have disjoint tight sets of
size 4, every edge can replace at most one tight facet, so every path has
length at least 4. Therefore `dist_P(x,y)=4=d`.

## Direct rational H-presentation of the primal

Translate `Q` by the average of its vertices

```text
c = (31/160, 63/512, 29/128, 3/16)
```

so that the origin is interior, then polarize. Multiplying every polar
inequality by 2560 gives the equivalent H-presentation

```text
A0 = (-496, -315, -580, -480)
A1 = (2064, -315, -580, -480)
A2 = (-496, 2245, -580, -480)
A3 = (-496, -315, 1980, -480)
A4 = (-496, -315, -580, 2080)
A5 = (144, -827, 60, 160)
A6 = (-368, -483, 220, 320)
A7 = (144, 325, 60, -640)
```

with common right-hand side `bi = 2560`.

The estranged primal vertices are

```text
x = (-11520/5567, -56320/16701, 5248/16701, 5248/16701)
y = (0, 0, -128/125, -512/125).
```

The tight rows at `x` are exactly `{3,4,5,6}` and those at `y` exactly
`{0,1,2,7}`.

## Counterexamples in every dimension >= 4

Let `k >= 0` and form `P_k = P x [0,1]^k`. Then

```text
dim(P_k) = 4+k = D,
facets(P_k) = 8+2k = 2D.
```

Choose `x_k = (x,0,...,0)` and `y_k = (y,1,...,1)`. Their incident facets
are disjoint and the product graph metric gives

```text
dist(x_k,y_k) = dist_P(x,y) + k = 4+k = D.
```

The bad source facet is `F6 x [0,1]^k`, with `4+2k = 2D-4` ridges, still
below `2D-2`. Every 2-face of a Cartesian product is a product of faces whose
dimensions sum to 2, so the bridge failure persists for all `D >= 4`.

## Consequence

The example rules out these universal claims:

1. every source facet has a 2-face bridge;
2. every low-ridge source facet has a 2-face bridge;
3. extremal distance `d` forces such a bridge;
4. a specified facet can always be rescued by replacing 2-face with a fixed
   small bridge dimension.

The stronger selectable-good-facet variant is ruled out separately by the
exact dimension-5 certificate in `SelectableTwoFaceBridgeCounterexampleD5.md`.
