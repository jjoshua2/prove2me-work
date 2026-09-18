# Written extension: two-edge lookahead does not restore score contraction

**Status:** ordinary mathematical argument plus exact symbolic/rational checks.
This extension is NOT in the accepted #304 Lean statement and has NOT received
another Lean audit or Prove2Me verdict. It does not alter that frozen packet.

## Precise extension of the same example

Use the six original nodes (-1,0,e,2e,3e,1), with 0<e<1/4, and the same source
u, target v, and score f=A_0+A_5 as #304. For every delta>0, e can be chosen so
that EVERY vertex reachable from u in at most TWO original edges has score
increase less than delta*(f(v)-f(u)), while v is three edges away.
The source itself has zero increase; all four other radius-two vertices have
strictly positive increase. Thus merely replacing one-edge contraction by a
fixed two-edge contraction does not repair this numerical-score argument.

## Complete six-cycle, not a sampled neighbor assumption

Write the ordered nodes as a_0<...<a_5. For a two-label set {i,j}, the root
polynomial (t-a_i)(t-a_j) has constant nonzero sign at all remaining nodes
exactly when i,j are consecutive, or {i,j}={0,5}. If the pair is neither, there
is an unselected node strictly between the roots and another outside, giving
opposite signs. The accepted exact root-polynomial vertex criterion (#299)
therefore leaves exactly the six tight sets

    {0,1}, {1,2}, {2,3}, {3,4}, {4,5}, {0,5}.

All six give actual vertices; adjacent entries, including the wrap, share a
row and give original edges by #295. There are no extra edges: an incident
edge must retain a source-tight row. Otherwise, immediately after leaving the
source, both source-tight rows and every initially slack row would be strict,
putting an interior point on a proper exposed segment. That is impossible for
a nonzero exposing functional; a zero functional exposes the whole 2D set,
not a segment. Each original row is tight at exactly two listed vertices, so
its full supporting slice permits only the already listed edge. This proves
the graph is the six-cycle, without assuming a graph table.

Using b={0,1}, l={1,2}, u={2,3}, r={3,4}, c={4,5}, v={0,5}, the cycle is
b-l-u-r-c-v-b. The vertices at distance at most two from u are exactly u,l,r,b,c;
v is at distance three. These graph claims in this extension are written
arguments using the established interfaces, not newly compiled Lean claims.

## Exact formulas and uniform estimate

The additional endpoint beyond r is

    c=(3(1+3e)/(1+6e-2e^2), -3/(1+6e-2e^2)).

Its six original slacks, with common positive denominator H=1+6e-2e^2, are

    (6(1+3e), 9e, 6e(1-e), 3e(1-2e), 0, 0)/H.

This confirms feasibility and exact tight set {4,5}. With
b=(-3/(1+3e+7e^2),-3/(1+3e+7e^2)) and g=f(v)-f(u), direct algebra gives

    g = 6(1+2e^2)/(1+4e^2),
    (f(b)-f(u))/g = e(14e^3+6e^2+5e+3)/((1+2e^2)(1+3e+7e^2)),
    (f(c)-f(u))/g = e(3-4e-4e^3)/((1+2e^2)(1+6e-2e^2)).

The b numerator after division by e is less than
14/64+6/16+5/4+3=155/32<5, and its denominator is at least one. Thus its
relative gain is below 5e. For c the numerator after division by e is positive
and less than three, while its denominator exceeds one; its gain is below 3e.
The already established l,r gains are positive and below 2e^2<5e.
Choosing e=min(1/8,delta/10) gives 0<e<1/4 and every radius-two gain below
5e*g<=delta*g/2<delta*g. This proves the asserted arbitrary-delta extension.

## Boundary and checks

This is NOT an obstruction to short paths: the target is exactly three edges
away. It does not rule out longer lookahead, other objectives, adaptive
combinatorial potentials, or Polynomial Hirsch. No general fixed-lookahead
claim for arbitrary horizons or larger node families is proved here.

`scripts/test_moment_two_step_gain.py` checks nine symbolic rational identities
and 41 complete exact-rational six-cycle references, including e=2^-128.
All 164 non-source radius-two endpoint estimates pass. This supports the written
argument, but finite tests do not establish its all-real quantifier; the algebra
and inequalities above do. No extra publication is made for this extension.
