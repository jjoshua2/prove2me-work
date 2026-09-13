# The checked catalogue is a complete set of linear dual tests

Let A be a rational k-by-n matrix, regarded also as a real linear map, and let C be the actual rational catalogue emitted by the finite checker of accepted PR #229. The checker audits every coordinate support of size at most k+1. Each support carries either a left inverse of the supported augmented matrix [A; ones], or a nonzero supported vector annihilated by both A and the mass row. Its output filter retains the positive normalized null vectors from the left-inverse cases.

The theorem proves that, whenever this arithmetic audit succeeds, for every real linear functional B,

$$
[\forall w\geq0,\ Aw=0\Longrightarrow B(w)\geq0]
\quad\Longleftrightarrow\quad
[\forall q\in C,\ B(q)\geq0].
$$

The rational catalogue is fixed before B is chosen. In particular, the right-hand-side coefficients of a dual test may be arbitrary real numbers. Catalogue completeness is not an additional semantic assumption: the public statement contains the same finite Boolean audit and explicit output filter as #229.

## Proof

The forward direction uses soundness of the checked catalogue. Every emitted vector, after casting to the reals, is nonnegative and belongs to the kernel of A, so any functional nonnegative on that kernel is nonnegative on the catalogue.

For the reverse direction, suppose that a nonnegative null vector w violates the desired inequality, so B(w)<0. The accepted support-pruning argument produces a nonzero nonnegative null vector x with B(x)<0 whose support is minimal among all nonzero nonnegative null vectors. Importantly, the minimality is not restricted to vectors violating B. The pruning argument preserves strict negativity when removing a nonnegative direction on which B is nonnegative, and otherwise uses a smaller negative direction directly.

Set sigma=sum_i x_i. Nonnegativity and nonzeroness imply sigma>0: some coordinate is positive and is bounded above by the total sum. The normalized vector v=x/sigma is nonnegative, satisfies Av=0, and has total mass one. Multiplication by the positive scalar 1/sigma preserves support. Therefore v has the same support-minimality property as x. The new Lean argument explicitly transports this property from the finite-support representation used in the pruning proof to the Function.support representation used by the arithmetic checker.

Completeness of the accepted checker now gives an actual emitted rational vector q in C whose real cast equals v. But

$$B(v)=B(x)/\sigma<0,$$

contradicting nonnegativity on the finite catalogue. This proves the equivalence without assuming that a particular implementation of Gaussian elimination is correct.

The additional checked_rhs_tests lemma specializes B to the pairing sum_i w_i b_i. It is the interface needed for allocation right-hand sides, including their real-valued dependence on an original feasible point.

## Reuse and verification boundary

The standalone packet reuses 443 lines of the accepted #229 catalogue proof and 128 lines of the accepted negative-circuit core carried by #219. Their proof bodies are unchanged; source-manifest.json records the original blobs and exact reused-block hashes. The additional 140 lines contain the normalization/support bridge, right-hand-side specialization, public statement adapter and axiom printouts. The old accepted statements are not submitted again.

The sources came from verified Actions artifacts 10326900522 and 10324553494. This environment has no local Lean executable and its direct GitHub DNS lookup failed. Static inspection and the exact rational checks in exact-sanity.json are not Lean verification. The prepared publication gate must compile the solution and exact statement, audit their axioms, and obtain an authenticated platform verdict before acceptance is claimed.

## Scope

This closes the formal link from the actual checked catalogue to all nonnegative-kernel dual inequalities. It does not yet reindex the allocation rows (-aG, -I, ones) into the checker's Fin-indexed matrix, eliminate the original feasible-point quantifier through sharp support witnesses, or assemble the whole-set Minkowski equality. Those are subsequent compositions with the already accepted allocation and support-budget results. It gives neither a polynomial bound on the number of circuits for unrestricted k nor an ordinary-edge diameter bound. It does not certify arbitrary JSON data without evaluating the Lean checker on the corresponding finite data.
