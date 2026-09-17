# Mass-preserving extraction of original active rows

## Written claim and current formal-verification status

The argument below is complete as a written proposal, but the new Lean root has NOT compiled successfully. Both comment-triggered attempts failed before publication. This is not an accepted theorem.

Let x be an actual extreme point of Q = convexHull(S) intersect {y : C_j(y) <= b_j for all j}. The support theorem already accepted in #291 selects n affinely independent points v_i of S and strictly positive weights w_i, with n <= d+1, sum w_i = 1 and sum w_i v_i = x. The proposed new theorem selects, as an additional conclusion, exactly n-1 of the original cuts active at x.

Together with the mass row these selected equations form a square nonsingular system. For arbitrary real mass t and arbitrary real selected values z_j there is exactly one real coefficient vector u satisfying sum u_i = t and sum u_i C_j(v_i) = z_j. In particular t=1 and z_j=b_j recover the actual weights w uniquely, even without imposing positivity on the competing vector u.

No support, weights, row subset, matrix inverse, determinant, rank test or desired count is a caller hypothesis. Selected rows are elements of the ACTUAL active subtype. S need not be finite, bounded, closed or compact. The base support points may individually violate the cut inequalities. Singleton support gives an empty selected-row set, while its mass equation alone remains invertible.

## Proof

Use #291's proven independence of the homogenized active-cut image columns. Regard the constant mass row and the indexed active evaluation rows as vectors in R^n. Since n>0, mass is nonzero. Start independent-set extension from its distinguished index, then extend inside this same indexed family. This preserves original row labels, rather than replacing them with arbitrary linear combinations.

Let J be the selected active indices. Independence immediately gives |J|+1 <= n. For the other inequality, let u annihilate mass and every selected row. The functional D(z)=sum_i u_i z_i vanishes on the selected span, therefore on every original active row. The accepted column independence now forces u=0. Thus the selected evaluation map from R^n to R times R^J is injective, giving n <= |J|+1. Equal finite dimension upgrades injectivity to surjectivity. This proves exact unique recovery for every signed datum.

The public theorem composes that helper with the accepted positive-support construction. Classical basis extension supplies existence; the theorem does not certify a particular executable greedy selector. Uniqueness is for coefficients on the constructed support and selected rows, not uniqueness of the support or canonical choice of J.

## Why this advances the cut-image argument

The earlier statement used ALL cuts tight at x to determine coefficients. A finite cut-image catalogue requires an actual square subsystem that keeps mass, so it can enumerate image simplices and solve precisely determined systems. That row-extraction obligation is the new conclusion here. The selected size equals n-1 <= d; it is not an assumed independent-row witness.

A complete finite image-cover construction and its quantitative bounds still need their own proof. Even enumerating every candidate support/row subset can be exponential. Nothing here bounds the number of vertices, all coordinate levels, total catalogue size, or original-edge diameter of an unrestricted polytope. This does not solve Polynomial Hirsch or reopen the disproved universal global-coordinate/refinement strategies.

## Supporting exact checks

The independent script tests 96 finite row systems, 288 arbitrary signed-data recoveries, 2448 inverse-product identities and 1332 small row-subset choices. Seven concrete simplex intersections in dimensions 0,1,2,3,4,8,16 supply actual cut vertices and 74 active rows. They retain redundant rows and base support points outside the cut body. The zero-dimensional case is treated separately as singleton support. Four saved inverses are rechecked with row selection, rank elimination and inverse discovery disabled. Five rank/mass/forgery controls are retained; the missing-mass example is an explicit rank deficiency rather than a parser rejection.

A clean one-script workspace reproduces the entire report byte-for-byte. These finite rational checks are separate from the unverified universal Lean candidate, and the test checker is not a kernel-verified parser. Mathematical classical ingredients are credited without a historical-priority claim.

## Source and verification boundaries

The complete accepted #291 source is reused with only its old root/print name changed. The proposed public target is Hirsch.cut_vertex_selected_active_square_system; it has only Mathlib symbols and explicit original active rows. The first compiler gate35249408324 failed at one scalar normalization in the new auxiliary linear functional. Adding RingHom.id_apply was the only submitted correction. Every theorem signature, condition and conclusion, plus problem.json and explanation.md, stayed unchanged.

The second gate35249850308 resolved proof590764458d8d21659d66363d302f270fd662dcd9. It failed at line415: the mass-row branch's simp only left a literal bundled LinearMap application unreduced. The earlier scalar issue no longer appears, but this does NOT establish all downstream code is correct. Both jobs skipped publication and produced only their resolved-request artifacts. Neither a passing new-root axiom audit nor a platform theorem/submission/ACCEPTED/Proved receipt exists.

A separately preserved proposed-local-repair.patch replaces that mass branch with an explicit change to the finite sum followed by mul_one simplification. It is NOT applied to the submitted solution and has NOT been Lean-tested. There was no third trigger or speculative hosted iteration. The full actual failure snapshots, exact selected diagnostic excerpts, requests and first applied diff remain separate from this proposal.

Local Lean/Lake is unavailable; Python/source checks are not compilation. Keep PR #294 draft. The next executable prerequisite is a pinned local compile/audit of the proposed repair and remaining source before a prepared publication attempt. Recheck ownership and any newer attempts first. No accepted proof, reserved #210, blocked #270 companion, toolchain pin, workflow, allowlist or secret separation changed.
