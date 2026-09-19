# Six original rows: tiny true first-step gains, short actual routes

This note gives the written argument for the packet
`moment_six_row_small_gain`. Consult its current verification record separately:
source text and exact rational tests do not establish Lean acceptance.

## Explicit original geometry

Let 0<e<1/4 and take the six parameters a=(-1,0,e,2e,3e,1). Their mean is e and
the mean square is (1+7e^2)/3. The ORIGINAL rows are

    A_i(x) = (a_i-e)*x_0 + (a_i^2-(1+7e^2)/3)*x_1 <= 1.

Put D=1+4e^2, E=1+10e^2, F=2-7e^2, G=1+3e+7e^2. All four denominators are
positive in the stated parameter interval. Define

    u=(9e/D,-3/D), l=(3e/D,-3/D), r=(15e/E,-3/E),
    v=(0,3/F), b=(-3/G,-3/G).

The nonzero original slacks are listed below; every omitted slack is zero.

| Point | Nonzero slacks 1-A_i(point) |
|---|---|
|u|i0:3(e+1)(2e+1)/D; i1,i4:6e^2/D; i5:3(1-e)(1-2e)/D|
|l|i0:3(e+1)/D; i3:6e^2/D; i4:18e^2/D; i5:3(1-e)/D|
|r|i0:3(2e+1)(3e+1)/E; i1:18e^2/E; i2:6e^2/E; i5:3(1-2e)(1-3e)/E|
|v|i1:3/F; i2:3(1-e)(1+e)/F; i3:3(1-2e)(1+2e)/F; i4:3(1-3e)(1+3e)/F|
|b|i2:3e(e+1)/G; i3:6e(2e+1)/G; i4:9e(3e+1)/G; i5:6/G|

Every listed expression is strictly positive. The exact tight sets are
{2,3}, {1,2}, {3,4}, {0,5}, {0,1}. The accepted moment tight-row criterion
makes all five actual extreme points. The accepted common-row theorem gives
the entire exposed original slices [u,l], [u,r], [l,b], [b,v]. In particular
u,l,b,v is a three-edge route. No projected auxiliary edge is used.

## There are no additional exposed-segment neighbors

For any feasible z, direct evaluation gives

    z-u = ((1-A_3(z))/(6e^2/D))*(l-u)
        + ((1-A_2(z))/(6e^2/E))*(r-u).

Both coefficients are nonnegative. A feasible point keeping row2 lies in the
whole slice [u,l]; one keeping row3 lies in [u,r]. If that point is extreme,
it must be one endpoint of the respective segment.

Suppose instead an extreme z distinct from u loses BOTH source rows and [u,z]
is exposed in the original P. Both displayed coefficients are then positive.
An exposing functional has equal values at u,z and is nonincreasing toward
l,r. The displacement equality forces it equal toward l as well. Thus l lies
in [u,z]. Extremality of l in P forces l=u or l=z. The former contradicts the
known distinct tight sets; the latter contradicts the assumed loss of row2.
Therefore the only original exposed-segment neighbors are exactly l and r.
This is a complete geometric proof, not the two-neighbor claim inferred from
finite computational samples.

## Actual best gain, as opposed to a weak guarantee

Take the fixed target score f=A_0+A_5; these are precisely the target's tight
rows. Let g=f(v)-f(u). The exact expressions are

    g=6(1+2e^2)/D > 0,
    (f(l)-f(u))/g = 2e^2/(1+2e^2),
    (f(r)-f(u))/g = 2e^2(1-2e^2)/((1+2e^2)(1+10e^2)).

Both fractions are strictly positive, and the left one is larger. Both are
strictly below 2e^2. For any delta>0 choose e=min(1/8,delta/4). It is positive,
less than1/4, and satisfies 2e^2<delta. Hence EVERY actual incident exposed-edge
neighbor gains less than delta times the target gap. A proposed positive lower
fraction depending only on d and m cannot hold for this score, even at d2,m6.

This is stronger than the particular written five-row mass example in #303:
there the bound1/Lambda vanished but the best actual gain stayed near6/13.
Here the best actual gain itself tends tozero. Earlier project #256 already
has written fixed-combinatorics radial/angular obstructions on other models;
no historical-first general obstruction or new classical polygon theorem is
claimed. This work supplies a compact formal original-moment instance with
complete incident-neighbor classification and an explicit short comparator.

## What does not follow

The example does not force a long route: three actual original edges suffice.
The public Lean target does not assert shortestness, although all exact tested
graphs have distance3. Nor does it claim that all subsequent moves are tiny,
that every objective is ill-conditioned, or that a multi-edge/adaptive policy
fails. It is not a counterexample to Polynomial Hirsch. A useful route proof
must control combinatorial changes or use an appropriate multi-step argument,
not assume a coefficient-independent fixed fraction of this numerical gap.

## Exact supporting tests and formal boundary

The standard-library Fraction script reconstructs all15 two-row systems for
each of59 parameter values:885 systems,354 vertices and354 edges across the
complete small graphs. It checks1770 original point-row values,59 exact source
neighbor sets and177 explicit route edges. Every independently computed target
distance is3. Eight delta choices include2^-128. All59 saved records replay
with explicit-point, square-solver and graph producers disabled; five forged
records fail. This consumer checks displayed points and edges, not a new
formal theorem about the Python parser or serialized inputs.

A clean one-script workspace reproduces the complete3548-byte report and31652-
byte fixture exactly. Report SHA25605114a9296c14bd680d1c14279c4cad0262789a9c861e152d6ba053bfd81a2b7;
fixturef72f0b9698aa24f254ce0af05cb4f2fed97dffa1c370106015c08ce514a7ea44.
The full fixture accompanies the export and regenerates:

    python3 scripts/test_moment_six_row_small_gain.py --out /tmp/six-row-check

The544-line accepted namespace prefix through Hirsch.MomentEdges is reused
byte-for-byte from the frozen #303 packet, with all five dependency file hashes
checked. No old public theorem is resubmitted. The new public type has explicit
Mathlib formulas, no local structure in its preamble, and no assumed graph or
feasible-point oracle. Local Lean/Lake is unavailable and the toolchain host
cannot resolve; exact arithmetic and source checks are NOT Lean verification.
The actual requested comment gate and its outcome must be recorded separately.
