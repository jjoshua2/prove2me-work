# Actual-neighbor transport: quantitative gain and the small-mass obstruction

## 1. The formal quantitative interface

Use the original dimension-d mean-centered moment rows
A_i(x)=sum_(j=1..d)(a_i^j-average_l a_l^j)x_j, with d<m and injective real
parameters. At distinct actual extreme points u,v, let I be u's tight rows.
The accepted release theorem constructs a normalized direction w_p for every
p in I and a positive first-blocking time t_p. Put z_p=u+t_p*w_p. Each z_p is
an actual neighbor and [u,z_p] is an exposed ORIGINAL segment.

The normalization gives A_p(w_p)=-1 and A_i(w_p)=0 for all other i in I.
For c_p=1-A_p(v)>=0, source active-map injectivity proves

    v-u = sum_p c_p*w_p.

Consequently b_p=c_p/t_p>=0 gives the exact actual-edge identity

    v-u = sum_p b_p*(z_p-u),     Lambda=sum_p b_p.

This is a nonnegative linear combination of edge DISPLACEMENTS, not a convex
combination of neighboring vertices. Let f be the sum of v's tight original
rows, g=f(v)-f(u)>0 and h_p=f(z_p)-f(u). The accepted target-score lemma makes
v the unique maximizer. Thus h_p<=g and g=sum_p b_p*h_p, so Lambda>=1. A finite
weighted maximum on the positive-weight indices selects p with

    b_p>0,     h_p>0,     g<=Lambda*h_p.

Equivalently the step gains at least g/Lambda. A shared target row has zero
c_p and cannot be selected, proving preservation of every shared target row.
The all-neighbor witnesses, weights, identity, mass bound and improving index
are conclusions, not assumed oracles. The precise public type includes the
normalized exposed-edge endpoints; it obtains first-blocking times internally
from the accepted constructor without repeating all of its ratio equations.

The new source reuses accepted #298 release geometry and #301's finite-sum and
target-score helpers. No accepted public target is submitted again. The
compilation/publication status is recorded separately in the packet evidence.
Classical feasible-cone and weighted-average reasoning is credited; no claim
of historical novelty or of a new best diameter theorem is made.

## 2. A fixed two-dimensional family has arbitrarily large mass

This section is a WRITTEN geometric/algebraic corollary with symbolic identities
and exact rational checks. It is NOT an additional conclusion of the submitted
Lean theorem and has no separate Prove2Me verdict.

Take five parameters (0,e,1,2,3), with 0<e<1, and the same original centered
moment inequalities in dimension two. Let D=e^2-5e+14. Define

    u  = ( 5e/[2(7-3e)],        -5/[2(7-3e)] ),
    v  = ( 25/D,               -5/D ),
    z0 = ( 5(e+1)/[2(4-e)],     -5/[2(4-e)] ),
    z1 = ( -15/[(4-e)(e+1)],     5/[(4-e)(e+1)] ).

Their exact tight sets are respectively {0,1}, {3,4}, {1,2}, {0,4}, where labels
index the five parameters rather than the parameter values themselves.
Every omitted slack in the following table is zero:

| Point | Nonzero original slacks 1-A_i(point) |
|---|---|
|u|i2:5(1-e)/[2(7-3e)]; i3:5(2-e)/(7-3e); i4:15(3-e)/[2(7-3e)]|
|v|i0:30/D; i1:5(3-e)(2-e)/D; i2:10/D|
|z0|i0:5e/[2(4-e)]; i3:5(2-e)/[2(4-e)]; i4:5(3-e)/(4-e)|
|z1|i1:5e(3-e)/[(4-e)(e+1)]; i2,i3:10/[(4-e)(e+1)]|

All listed expressions are strictly positive for 0<e<1. In particular D>9.
The accepted exact moment-vertex criterion therefore makes all four points
actual extreme points. u and z0 share one original row, and u and z1 share
one original row. Accepted #295 makes those full common slices exposed original
edges. Distinct active sets ensure nondegeneracy.

Normalize the edge directions by releasing row0 or row1 at unit rate. The
corresponding edge times and weights are

    t0=5e/[2(4-e)],       t1=5e(3-e)/[(4-e)(e+1)],
    b0=12(4-e)/(eD),      b1=(4-e)(2-e)(e+1)/(eD).

The exact source-to-target displacement is b0*(z0-u)+b1*(z1-u). Both weights
are positive. Their sum satisfies

    Lambda(e)=(4-e)(14+e-e^2)/(eD),
    Lambda(e)-1/e=(3-e)(14+3e-e^2)/(eD)>0.

Thus Lambda(e)>1/e with fixed d=2 and m=5; it is unbounded as e tends to zero.
Indeed e*Lambda(e) tends to4. A dimension/row-count-only bound on THIS mass is
therefore false, rather than merely unproved from finite tests.

The first-blocking endpoint interpretation needs no hidden choice: these two
normalized directions preserve the respective other source row; their exposed
segments are the full feasible slices and their positive endpoint times are
exactly the first blockers. Every normalized direction is fixed by the invertible
source active map. The mass is therefore not enlarged by arbitrary rescaling
of a direction.

## 3. A weak guarantee is not a long route

With target score f=A_3+A_4, the full gap is

    g(e)=5(13-5e)/[2(7-3e)].

The neighbor gain fractions are

    h0/g=-4(e^2-3e+1)/[(e-4)(5e-13)],
    h1/g=(e-3)(5e^2-13e-8)/[(e-4)(e+1)(5e-13)].

As e tends to zero these tend to -1/13 and6/13, respectively. Thus one weighted
term is negative and the other supplies a substantial true improvement even
while 1/Lambda tends to zero. The large positive weights cancel strongly in
the signed gain identity. It would be wrong to infer a small actual maximum
gain, a slow pivot policy, a graph-distance lower bound or a Hirsch counterexample
from the unbounded mass.

This suggests retaining the signed gain distribution rather than discarding
it in g/Lambda, or using a different route-local invariant. Neither suggestion
is assumed to be an established polynomial bound. Even a small relative-gain
bound requires care about termination thresholds if objective gaps can be
arbitrarily small. Existing all-endpoint finite ascent remains separate.

## 4. Executed supporting tests and reproduction

Six complete original-H small models examine153 square systems, yielding51
vertices. All578 ordered distinct pairs check2060 original-edge records and
coordinate transport identities,170 equality cases and158 unit-mass cases.
Two selected higher-dimensional examples (d8,d16) check all outgoing neighbors;
both have unit mass and are not claimed as hard long routes. Twelve saved
records check47 original edges with direction/candidate/inverse/solver production
disabled. Six forgeries are rejected. A clean three-script workspace repeats
the full2676-byte report and282982-byte fixture byte-for-byte.

The separate symbolic script checks the four explicit original slack tables,
both normalizations, both weights, the displacement identity, the exact mass
identity and gain limits. The sign inequalities are justified in the text,
not accepted merely because SymPy guessed them. It does not compile Lean.

    python3 scripts/test_moment_neighbor_transport.py --out /tmp/transport
    python3 scripts/check_neighbor_mass_family.py --out /tmp/transport/symbolic.json

The runtime has no local Lean/Lake. Formal compilation, axiom audit, publication
and live readback must be read from the exact frozen packet's actual evidence,
not inferred from these software tests or the written unbounded-family argument.
