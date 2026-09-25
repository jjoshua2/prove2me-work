# Tiny actual gains, not merely a pessimistic transport bound

Use original mean-centered moment rows on a=(-1,0,e,2e,3e,1), with 0<e<1/4. The mean node value is e and the mean square is (1+7e^2)/3. Set D=1+4e^2, E=1+10e^2, F=2-7e^2, G=1+3e+7e^2. The five explicitly constructed points are

    u=(9e/D,-3/D), l=(3e/D,-3/D), r=(15e/E,-3/E),
    v=(0,3/F), b=(-3/G,-3/G).

Their exact ORIGINAL tight sets are {2,3}, {1,2}, {3,4}, {0,5}, {0,1}. All thirty original slacks are proved by rational identities and shown strictly positive off these sets. The accepted tight-row criterion yields actual extremality. The accepted common-row theorem gives the entire exposed original edges u-l, u-r, l-b, b-v. Thus u,l,b,v is a three-edge route.

The proof also excludes any unlisted exposed neighbor of u; this is not a claim based on a sampled graph. A feasible z keeping source row2 or row3 lies in the whole corresponding original edge slice; if z is extreme it must be the other endpoint. If neither source row remains tight, its displacement is a STRICTLY positive combination of l-u and r-u, with coefficients obtained from the two original source slacks and the corresponding neighbor slacks. An exposing functional constant on [u,z] is nonincreasing toward l and r. The positive combination forces it constant toward l, making l a member of [u,z]. Extremality forces l=u or l=z, contradicting distinctness or the assumed lost row2. Hence the two named neighbors are exhaustive.

For the fixed target score f=A_0+A_5, let g=f(v)-f(u). Exact identities give

    g=6(1+2e^2)/(1+4e^2),
    (f(l)-f(u))/g=2e^2/(1+2e^2),
    (f(r)-f(u))/g=2e^2(1-2e^2)/((1+2e^2)(1+10e^2)).

Both gains are positive and strictly below 2e^2*g. Given delta>0, e=min(1/8,delta/4) satisfies 2e^2<delta. The public theorem quantifies over EVERY positive delta and over EVERY exposed original-edge neighbor, while providing a three-edge route. It therefore does not confuse a small guaranteed lower bound with a small actual best gain. The exact best fraction displayed above is also checked independently in the rational suite; the public conclusion only needs the common upper bound.

The previous accepted mass theorem #303 stays unchanged. Its five-row example made mass unbounded but the best actual relative gain approached6/13. This is a different, stronger local-contraction obstruction within the same original moment family. Earlier project #256 already contained written fixed-type radial/angular contraction obstructions on other polytopes; neither the general idea nor classical polygon geometry is claimed historically novel. The present contribution is a complete formal six-row instance with incident-neighbor completeness and an explicit short route.

The full accepted 544-line namespace prefix through Hirsch.MomentEdges is reused byte-for-byte, and its old public targets are not submitted. The new target has an imports/open/options-only preamble and explicit let formulas; top-level solution matches its signature. Five transitive axiom printouts cover geometric construction, neighbor completeness, quantitative bounds, the short route, and the public theorem. No proof admissions, target imports or new conjectural assumptions.

This is NOT a long-route example or a counterexample to Polynomial Hirsch. Small first-step score gains cannot bound the number of required graph edges from below. The supplied three-edge route is not formally asserted shortest. No claim that the same behavior persists at every step or for arbitrary objectives, multi-edge policies, projective normalizations or all carriers.

No local Lean/Lake is installed, and toolchain-host DNS fails. Exact rational tests and source comparisons are not Lean compilation. One prepared final comment gate is requested by the user; any failure must remain visible and must not initiate repeated speculative hosted editing. Pins, workflows, allowlist, duplicate guards and credential separation stay unchanged. Owned #300/#302 and reserved #210 are untouched.
