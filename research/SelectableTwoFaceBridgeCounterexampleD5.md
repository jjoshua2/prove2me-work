# Exact dimension-5 counterexample to the selectable good-facet 2-face bridge

## Claim ruled out

A weaker version of the 2009 2-face bridge idea survives the dimension-4
counterexample in `TwoFaceBridgeCounterexample.md`:

> For a simple `(d,2d)` Dantzig figure with estranged vertices `x,y`, choose
> among the facets through `x` one having at most `2d-2` ridges.  Perhaps at
> least one such "good" facet contains a vertex sharing a 2-face with `y`
> (and symmetrically one may choose the orientation `x,y`).

This weaker **selection** claim is also false.  The counterexample below is a
rational simplicial 5-polytope with 10 vertices.  After polarity it gives a
simple `(5,10)` Dantzig figure whose two estranged vertices are at graph
distance exactly `5`.  In each orientation there is exactly one good source
facet, and that facet has no 2-face bridge to the opposite endpoint.

## Rational simplicial dual

Let `Q` be the convex hull of the following ten points in `R^5` (all
coordinates have denominator `10000`):

```text
q0 = (-7906, -3779,  3765,  2536, -1617) / 10000
q1 = (-2479, -1913,  3968,  8624,   277) / 10000
q2 = (-8136,   213,  4395,  1773, -3361) / 10000
q3 = ( 1815, -3255,  7206,  5567,  1784) / 10000
q4 = ( 2471, -9137, -2139, -1790,  1623) / 10000
q5 = ( -183, -2801,    99,  9569,   738) / 10000
q6 = (-1635,  4562, -7049,  2145, -4714) / 10000
q7 = (-6786,  4628, -3912,  3784, -1704) / 10000
q8 = ( 1614,  2189, -3607, -8899,  -636) / 10000
q9 = (-4161,   -60,  1196, -7692,  4700) / 10000
```

Exact integer determinant tests were run on all `C(10,5)=252` five-vertex
subsets.  Exactly the following 40 subsets are supporting facets, so `Q` is
simplicial and the combinatorial data below is certified over the rationals:

```text
01235 01239 01257 01279 01345 01349 01459 01579
02345 02349 02456 02468 02489 02567 02678 02789
04567 04579 04678 04789 12356 12367 12379 12567
13459 13567 13579 23456 23468 23489 23678 23789
34568 34589 35678 35789 45679 45689 46789 56789
```

Take the disjoint facets

```text
X = {0,1,2,3,5}
Y = {4,6,7,8,9}.
```

After polarity, `X` and `Y` are the estranged primal vertices `x,y` of a
simple 5-polytope `P` with 10 facets.

## The pair has distance exactly d=5

Facet adjacency in the simplicial dual is ridge adjacency.  The following
sequence gives a primal path of length five:

```text
01235 -> 01345 -> 01459 -> 04579 -> 45679 -> 46789.
```

The endpoint tight sets `X,Y` are disjoint and each has size five.  In a
simple 5-polytope one graph edge can replace only one tight facet, so every
path between the endpoints has length at least five.  Hence

```text
dist_P(x,y) = 5 = d.
```

Thus the bridge failure is not caused by choosing a short/non-extremal pair.

## Exactly one good source facet in each orientation

For a simplicial dual, the number of ridges of primal facet `Fi` equals the
degree of dual vertex `i`.  The degrees are

```text
vertex: 0 1 2 3 4 5 6 7 8 9
degree: 9 8 9 9 9 9 9 9 8 9.
```

For `d=5`, the projective-removal threshold is `2d-2=8`.  Therefore:

- from source endpoint `X`, the **only** good source facet is `F1`;
- after reversing the Dantzig pair, from source endpoint `Y`, the **only**
  good source facet is `F8`.

(The two exceptional dual vertices even have the same neighbor set
`{0,2,3,4,5,6,7,9}`.)

## Neither good facet has a 2-face bridge

In the polar correspondence, a primal vertex in facet `Fi` is a dual facet
containing `i`.  In a simple 5-polytope, a primal vertex and `y` can lie in a
common 2-face only if their tight sets share at least `d-2=3` facets.
Equivalently, a 2-face bridge from `Fi` to target `Y` would require some dual
facet containing `i` to contain at least three vertices of `Y`.

For the only good source vertex `i=1`, the maximum value of

```text
|Z intersect Y|
```

over all dual facets `Z` containing `1` is **2**, never 3.  Hence `F1` has no
2-face bridge to `y`.

After reversing orientation, for the only good source vertex `i=8`, the
maximum value of

```text
|Z intersect X|
```

over all dual facets `Z` containing `8` is again **2**.  Hence `F8` has no
2-face bridge to `x`.

Consequently there is no choice of orientation and no choice among the
low-ridge source facets that makes the proposed 2-face bridge available.

## Optional direct primal H-presentation

The average of the ten integer numerator vectors is `S/10`, where

```text
S = (-25386, -9353, 3922, 15617, -2910).
```

Translate the rational points by their barycenter and polarize.  Multiplying
all polar inequalities by `100000` gives a direct primal H-presentation

```text
Bi dot x <= 100000
```

with integer normals

```text
B0 = (-53674, -28437,  33728,    9743, -13260)
B1 = (   596,  -9777,  35758,   70623,   5680)
B2 = (-55974,  11483,  40028,    2113, -30700)
B3 = ( 43536, -23197,  68138,   40053,  20750)
B4 = ( 50096, -82017, -25312,  -33517,  19140)
B5 = ( 23556, -18657,  -2932,   80073,  10290)
B6 = (  9036,  54973, -74412,    5833, -44230)
B7 = (-42474,  55633, -43042,   22223, -14130)
B8 = ( 41526,  31243, -39992, -104607,  -3450)
B9 = (-16224,   8753,   8038,  -92537,  49910).
```

The estranged primal vertices are the unique solutions obtained by making
rows `X` and `Y` tight respectively.  This gives a direct finite rational
certificate suitable for Lean if later needed.

## Consequence for the research plan

This example rules out the remaining single-2-face selection strategy:

1. the 2-face bridge need not exist for an arbitrary source facet;
2. it need not exist for an arbitrary **good** low-ridge source facet;
3. even allowing us to choose **some** good source facet does not save the
   claim;
4. allowing reversal of the Dantzig pair does not save it;
5. restricting to an extremal pair with distance exactly `d` does not save it.

The appropriate next target is therefore not another single low-dimensional
bridge statement.  The promising historical route is projective
removal/reintroduction with **controlled cumulative path damage**: most local
moves preserve or shorten a path, while the exceptional move may increase it.
For polynomial Hirsch, that exceptional cost need only be polynomially
summable; it need not be zero or one on every step.
