# Continue from confinement, not an assumed small defect parameter

Read current STATUS and actual open PR heads. This is research/code only;
no new Lean proof, axiom audit, Prove2Me submission or acceptance is claimed.
All older accepted results and #258's exact segment code remain unchanged.

The new bound applies to a simple bounded full-dimensional original-H polytope
with m facets,d dimensions,e=m-d. Choose k exceptional facets B. A sufficient
global condition is that ALL inclusion-minimal empty intersections of size>=3
are wholly inside B. Alternatively certify all missing triangles in every
visited recursive link are wholly inside B. Merely hitting each missing
triangle or deleting B to leave a flag induced subcomplex is NOT sufficient.
The protected-label specialization of Adiprasito--Benedetti's induction then
makes every nonexceptional label nonrevisiting.

Erase complete-vertex loops. At a fixed active exceptional subset S, each next
protected active set must introduce a new protected label. This yields

    L <= sum_{s=max(0,d-(m-k))}^{min(k,d)} binom(k,s)*(m-k-d+s+1)-1
      <= (e+1)*2^k-1.

If k<=min(d,e), it is2^(k-1)*(2e-k+2)-1 (k>=1); k0 gives e. Any already-certified
impossible exceptional subset can further remove states. The optional checker
enumeration for that refinement is capped at16 labels; above it the generic
formula remains. Only ORIGINAL empty subsets are used, never a link's empty
S+T misrepresented as globally empty T.

This is linear for fixed k and polynomial for k=O(log m). No theorem establishes
that regime on arbitrary carriers; do not silently add that premise to claim
Polynomial Hirsch. The output bound after loop erasure is not an internal
runtime or raw-path bound. A later arbitrary repair may invalidate protected
intervals, so it must be recertified. k can be large on easy polytopes.

The all-dimensional nonproduct example is

    0<=x_i<=1, S=x0+x1+x2<=5/2,
    S-x_j<=5/2-2^(-(j+1)), j>=3.

It has3d-2 genuine facets, a single high minimal nonface {upper0,upper1,upper2},
and (3d+11)*2^(d-4) vertices for d>=4 (10 for d3). Successive protected-ridge
truncations preserve that defect set by an explicitly proved stellar lemma.
The minimal-nonface hypergraph is connected, excluding a nontrivial combinatorial
Cartesian product. This is not a Minkowski indecomposability claim. Excluding
the impossible whole triple improves the bound to7e-6=14d-20 for ALL vertex
pairs. It remains a structural class bound, not a general solution.

The k parameter is not the published banner threshold. The example has critical
nonface cliques of size d+1 despite k=3; the classical banner bound alone therefore
does not supply its dimension-independent multiplier. Published exponential
examples for EVERY raw combinatorial segment remain explicit limitations.
Sources and the full proof are in DEFECT_CONFINEMENT.md.

Reproduce from the repository or bundle:

    python3 scripts/test_defect_confinement.py --large

Three old dependencies only: original_facet_segments.py, exact_farkas_lp.py,
simple_tangent_policy_audit.py. The new tiny input fixture stores14 historical
A,b,start,target cases from #258, not old proof certificates; all are regenerated
in the current test. No need to materialize any earlier conversation bundle.

The final suite checks83 geometric routes and28568 used-link triangles. Family
d3/d4/d5 has63 pairs and1532 independent square systems, with complete clipping,
minimal-nonface and genuine-facet checks. Casesd6/d8 use generic exact LP; d12
uses an additional family-specific exact witness producer for the SAME segment
recursion. No full large graph is enumerated. d12:34 facets,12032 construction-
proved vertices,12 actual selected edges,148 all-pairs structural bound,22475
triangle checks. Do not call that a completed generic LP run or an all-pairs
numerical test.

Three extra holdouts have REAL exceptional-facet reentries. Two are products
in dimensions4/6; a protected cross-factor ridge truncation gives a nonproduct
4D case with the same six-label defect core. These avoid a test suite containing
only incidental nonrevisiting routes. Seven malformed/unsupported controls fail;
23 complete certificate audits run with LP, inverse,basis and intersection
production disabled (BFS/recursion still replay). The standalone finite-state
count is checked on1638 random interval walks and9466 exhaustive small walks.
No claim that Python/JSON is Lean-extracted or independently formalized.

The next actual task is to control local exceptional signatures or reduce them
with bounded original-edge cost on arbitrary carriers. Do not repeat the
already completed flag theorem, assume all missing-face supports are small,
or claim a polynomial full-inventory bound. #244/#238/#250/#255 work remains
separate and untriggered by this contribution.
