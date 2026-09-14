# Uniform strict endpoints for the same exposed bridge

## Exact contribution

This packet supplies the strict endpoint objectives needed to connect accepted #240 core-edge bridges to accepted #244 fixed-core fibre routes. Given the actual listed bridge endpoints a_i,b_i with b_i=a_i+eta_i e, eta_i>=0, e!=0, a supporting functional f with f(e)=0, and the finite support-face conditions, it constructs q(e)=1 and ONE delta>0. For EVERY 0<s<delta, f-sq strictly exposes all a_i and f+sq strictly exposes all b_i. The same objectives uniquely expose the respective summed endpoints on the WHOLE Minkowski sum of convex hulls. Both endpoint memberships are proved.

The component endpoints are the SAME ones given by the bridge, not replacements supplied by an unrelated exposer. Point factors, eta_i=0, redundant interior points, empty factor families and lower-dimensional hulls are allowed. No uniform lower bound on delta independent of the input is claimed. A small objective perturbation has no graph-length charge by itself.

## Proof

1. A nonzero vector e admits a nonvanishing algebraic linear functional. Normalize it to q(e)=1 using Mathlib's Module.exists_dual_forall_apply_ne_zero. This lemma and its exact signature were checked in Mathlib/Algebra/Module/Submodule/Union.lean at the committed pin. No finite-dimensional or topological assumption is needed.
2. On a segment [a_i,b_i] parallel to e, a point has form a_i+r e with 0<=r<=eta_i. Its q-value is q(a_i)+r. Equality with either endpoint q-value forces equality of the points, including collapsed segments. Since f is constant there, the two perturbation signs strictly select the corresponding endpoint.
3. Let D be the finite collection of differences a_i-x and b_i-x for every listed point x. For f(d)>0, the radius f(d)/(|q(d)|+1) is positive. For all other differences use radius1; also include a sentinel1 for the empty-family case. Half the finite minimum gives delta>0. Whenever 0<s<delta, both f(d)-s q(d) and f(d)+s q(d) stay positive for every originally positive difference. This proves all off-support comparisons uniformly over the entire open parameter interval, not just sample perturbations.
4. A strict finite maximizer extends to a unique maximizer of the whole convex hull. The proof verifies convexity of the weak-bound-and-unique-equality predicate, including zero coefficients in convex combinations.
5. Sum the component bounds. If equality holds in the total, every component bound must be an equality: one strict summand would make the whole finite sum strict. This proves the global singleton support and handles the empty sum explicitly.

The normalized-coordinate and convex-support arguments adapt the accepted #240 packet generic_minkowski_edge_lift, Git blob884daa33d3890f6d45b8adf8d967aa27eac8f09a. The new formal interface is the uniform two-sided radius and compatibility with the SAME bridge endpoints. Classical finite perturbation and Minkowski support principles are not claimed as historical discoveries.

## Binding to #240 and #244

Apply #240 to an actual core edge u-to-v. Its component support slices imply the finite hface premise here by inserting listed maximizers into their convex hulls. Let e=v-u and choose s=delta/2. The lower objective strictly exposes u in the core and its associated factor endpoints; the upper objective strictly exposes v and the opposite associated factor endpoints.

At an intermediate core vertex, the incoming upper objective and outgoing lower objective satisfy #244's SAME-core strict endpoint assumptions. Injectively enumerate each finite point set when converting these statements to indexed factor dictionaries. Distinct labels must not be allowed to represent the same point in a strict comparison. #244 then provides the connecting fibre leg of cost K=sum_i(k_i-1).

The final indexed binding and concatenation of L actual bridges with L+1 fibre legs remain separate work, with expected cost L+(L+1)K. This packet does not assume or prove an arbitrary core edge, a useful decomposition of every carrier, or a uniform Polynomial Hirsch bound. Another agent has claimed the full core-walk assembly; this PR is only the endpoint lemma and does not duplicate that assembly or resubmit #244.

## Source, execution and status

Prepared from main7302eabfb96bb75f2993270d2b5cdb5aff3a4738. The prior turn's branch request was blocked and no proof was submitted. In this continuation the normal branch creation and source writes succeeded; the 264-line proof was transplanted unchanged from the attached package. Its SHA-256 is ac24ae1ef62c0c29fa7b6bbd5b03320bb365e838385f7e4e8c56bf9c8e9465ea. The public statement was text-matched exactly with the top-level theorem solution. The public preamble is Mathlib import/open/set_option only.

The exact rational suite was rerun:128 cases,383 factors,1166 support-tied and1140 off-support points,18448 component sample comparisons,264616 small full-tuple comparisons,14 rejected controls. The uniform inequalities are checked separately from samples. It includes support gaps down to2^-240 and a64-factor/12D instance without tuple enumeration. These checks are NOT Lean compilation or Lean-extracted certificate evaluation. Full fixtures regenerate from the standalone test in the accompanying package.

No Lean or Lake executable is available in this runtime. Direct public toolchain access failed at DNS, and no compiler plugin was found. Thus local compilation is not claimed. The existing guarded publication workflow must compile the exact frozen packet, verify its target match, and audit all six printed declarations before any platform action. Do not infer acceptance from this explanation. No workflow, pin, permissions, API key handling or unrelated PR is changed.

Use Lean v4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. The source contains no added axiom or admitted proof. On a compiler failure, retain the exact diagnostics and stop rather than treating hosted Actions as a speculative compiler loop.

## Primary context

Antoine Deza and Lionel Pournin, Diameter, decomposability, and Minkowski sums of polytopes, arXiv:1806.07643v1, Section2 and Lemma3.8, DOI10.4153/S0008439518000668. https://arxiv.org/html/1806.07643v1 . The classical support and lifting framework is used, not claimed new.
