# Verification handoff: fixed-rank simplex summands from original H-rows

Base: PR #210, `4b82eedf97812059490e545a8a4d02822597f87b`.
All new paths are additions. Older LP, core, segment and wall-lifting code
is reused unchanged. The new Lean file imports Mathlib only.

## Primary target

The extraction has no assumed decomposition or diameter premise. For
S=conv(0,g1,...,gk), form h_i=max(0,A_i g_j) and auxiliary rows C=(-AG,-I,1).
For every nonnegative extreme kernel ray w=(lambda,nu,gamma), the necessary
condition is

    t*(lambda.h-gamma) <= lambda.b-(lambda.A)x.

All extreme supports have at most k+1 rows. Positive-demand rays receive
original-row Farkas upper bounds, and one original feasible point is sharp.
The finite list proves global equality via Farkas and a maximum removable
scale. Nonpositive demands are automatically satisfied and must not be
misinterpreted as upper bounds. Zero auxiliary rows give singleton rays;
discarding larger supports containing one is a complete optimization.

The dimension controlling enumeration is k, NOT ambient d. Only fixed-k
polynomially many LP calls are claimed. Exact Bland simplex is capped and
does not acquire a polynomial pivot bound from that statement.

## Mathematical scope to preserve

The implementation covers supplied independent-generator simplices.
The note derives the more general fixed-rank H-candidate formula (-AG,F),
but does not claim that broader code is implemented.

The blind router proposes local shapes from source-basis edges. Rank-two
proposals are triangular faces; higher-rank neighbor cliques are only shape
suggestions, not automatically whole simplex faces. Every global acceptance
comes from the exact extractor. No complete higher-dimensional catalogue is
claimed. Different simplex removals can compete: the explicit segment-free
pentagon has capacities2/3 and1, and each becomes zero after maximally removing
the other. Do not copy the segment order-invariance claim into this extension.

The triangle with objective(2,1) and antipodal route e1--0 also refutes a
generalized "every simplex edge direction appears" claim. Binary segment
allocation was essential in the earlier completeness theorem.

Core boundedness is certified using original-row coordinate bounds before
point/pyramid recognition. Direct-sum shortestness requires a point core AND
rank equal to the total number of generator columns. Other routes use the
older exact wall lifter, keep ordinary original-edge rank/blocker evidence,
and are not asserted shortest.

## Local commands

```sh
python3 -m py_compile scripts/simplex_summand_certificate.py \
  scripts/local_simplex_routes.py scripts/test_low_rank_simplex.py
for s in extract route order negative large8 large16 dense elimination assemble; do
  python3 scripts/test_low_rank_simplex.py --stage "$s"
done
lake build Solutions.PolynomialSimplexLiftObstructions
```

The 149-line Lean source has SIX axiom printouts and remains UNCOMPILED.
Expected elaboration-sensitive points are linear-map finite-sum rewriting,
the double-sum interchange, and set-membership unfolding. Preserve exact
lift equations and nonnegative coefficients. It proves the finite geometric
reduction and necessary dual inequalities; it does not yet formalize the
complete cone-generation and Farkas-sufficiency bridge. Do not add that bridge
as an unexplained axiom or describe the whole algorithm as verified because
these cores compile.

## Actual evidence

Seven independent whole-H/sum equality tests and seven strict overshoot
failures;43 explicit point decompositions;seven rank-one crosschecks;
144 independent Fourier--Motzkin versus extreme-ray feasibility comparisons.
Three small original graphs give100 all-pair routes, with three larger cases
bringing the total to103 routes/181 edges. Twenty rejected bad/unsupported
certificates. The non-product3D example has eight facets,nine vertices,no
segment factors, but an automatically discovered triangle summand.

The32D example has48 original facets,43,046,721 vertices by explicit product
structure,16 recovered triangle factors and a16-edge shortest test route.
No ambient graph is enumerated. The dense6D example supplies no affine chart.
These are recognition tests, not new classical product-diameter theorems.

The test runner hashes new source files and rejects stale stage receipts.
The standalone ZIP includes unchanged dependencies; the incremental patch
must not add or overwrite those existing repository files. No new hosted
run or Prove2Me action was made. After pinned local compilation and standard
transitive-axiom audit, use the existing final hosted gate only.
