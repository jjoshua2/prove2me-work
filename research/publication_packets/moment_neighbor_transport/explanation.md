# Quantitative improvement from actual neighboring vertices

This is a new quantitative local interface after accepted #298 and #301, not a resubmission of either target and not a claim of a polynomial route bound.

At an actual source vertex u, the accepted release-edge theorem constructs one normalized direction w_p for each tight original row p, with A_p(w_p)=-1 and zero value on all other source-tight rows. It also constructs the positive first-blocking time t_p. The endpoint z_p=u+t_p*w_p is an actual extreme point and the whole segment is exposed in the ORIGINAL H set. The new proof constructs all these witnesses at once; no direction, neighbor, rank, step or adjacency oracle is assumed.

For a distinct actual target vertex v, let c_p=1-A_p(v). Feasibility gives c_p>=0. Applying the injective active-row evaluation map proves v-u=sum_p c_p*w_p. Define b_p=c_p/t_p and mass=sum_p b_p. Multiplication by the actual positive edge lengths yields the exact identity

    v-u = sum_p b_p*(z_p-u).

This is a NONNEGATIVE LINEAR combination of edge displacements, not a claimed convex combination of neighboring points: mass is generally greater than one.

Use the fixed score f(x)=sum_(i tight at v) A_i(x). The accepted target-score theorem gives f(v)>f(u), and f(z_p)<=f(v) for every constructed neighbor. Therefore the gap g=f(v)-f(u)>0 satisfies g=sum_p b_p*(f(z_p)-f(u))<=mass*g, proving mass>=1. No independent mass lower-bound premise or assumed small mass appears in the public statement.

A finite weighted-maximum lemma constructs an index p with positive b_p and positive gain h_p=f(z_p)-f(u) such that g<=mass*h_p. Equivalently, this actual edge gains at least a 1/mass fraction of the target gap. The selected index has c_p>0, so it cannot release a row shared with the target. Every shared target-tight row is preserved.

The public type spells out the original rows, source and target active sets, score, all neighboring endpoints, coefficients and total mass. The proof internally obtains t_p from the accepted first-blocking constructor; the public conclusion asserts the resulting normalized original-edge endpoints, not an additional separate minimum-ratio formula. It retains arbitrary injective real parameters, unsorted original labels, both dimension parities and all distinct endpoint pairs. Dimension zero is vacuous for distinct actual vertices.

The full accepted source through Hirsch.MomentRelease and the exact accepted row_finite_sum and target_score_strict helpers are reused. Their earlier standalone roots, finite vertex catalogue and finite-ascent assembly are not republished. The new helper and public theorem have no admissions; the target has only imports/open/options in its preamble and its formal signature matches top-level solution.

The quantitative guarantee does NOT bound mass from above. The exact tests already include large mass on two-dimensional five-row examples; no polynomial estimate is inferred from those tests. An edge can perform much better than the guaranteed fraction. Controlling mass along routes, or finding a different argument that bypasses it, remains a separate task. Strict fractional improvement alone also does not provide a coefficient-independent finite step count. No Polynomial Hirsch or historically new simplex-method claim is made.

Supporting exact-rational tests exhaust every ordered distinct endpoint pair on six independently enumerated small H models, check all constructed neighbor records and transport identities, and retain sharp cases, negative gains, spacing-dependent large-mass examples, forged records and producer-disabled replay. These finite checks are not Lean verification or an all-real proof by sampling. The exact report and fixture are preserved separately.

No local Lean/Lake compiler is available and the toolchain-host DNS preflight failed. The user requests one actual NEW top-level PR-comment publication attempt for the complete packet. The existing pinned gate must compile and audit before publication. Preserve any failure; do not use repeated speculative Actions edits as an interactive compiler. #300 and #302, reserved #210, accepted packets, toolchain pin, protocol, allowlist and trusted verify/publish secret separation remain unchanged.
