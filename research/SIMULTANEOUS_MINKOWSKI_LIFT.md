# Simultaneous Minkowski lifting with an additive vertex budget

## 1. Why this is a diameter step

The checked allocation/circuit chain establishes exact decompositions, but a decomposition is not a short ordinary-edge route. Repeatedly applying the one-summand bound can multiply the vertex counts of many small summands. The simultaneous construction avoids that multiplication.

Let P,Q_1,...,Q_r be nonempty polytopes in a real finite-dimensional vector space. They may be lower-dimensional, have parallel edges, or have dependent generator lists. Write R=P+sum_i Q_i and K=sum_i(f_0(Q_i)-1). For vertices x,y of R, let p_x,p_y be their uniquely determined P-components. Given ANY L-edge walk from p_x to p_y in P, there is an ordinary-edge walk in R from x to y of length at most

    L + (L+1) K.

In particular,

    diam(R) <= (diam(P)+1)(1+K)-1.

The bound counts core-walk occurrences, including repeated vertices. It does not assert that the lifted walk is shortest. This is a direct simultaneous version of the classical normal-fan fibre argument. No historical novelty claim is made.

Source: Antoine Deza and Lionel Pournin, *Diameter, decomposability, and Minkowski sums of polytopes*, arXiv:1806.07643v1 (2018), pp. 9-11, Lemmas 3.7-3.8 and Theorem 3.5; published Canadian Mathematical Bulletin 62 (2019), 741-755, DOI 10.4153/S0008439518000668. Their one-summand bound is (diam(P)+1)f_0(Q)-1. The construction below keeps separate envelopes instead of replacing sum Q_i by its potentially enormous vertex set.

## 2. Fibre diameter: the essential improvement

Fix a vertex p of P. Let Gamma(p) be the induced subgraph on R-vertices whose P-component is p. Take two such vertices x,y. Each has a unique vertex decomposition into all summands: a functional uniquely exposing a vertex of the sum must uniquely expose a point in every summand, since otherwise that summand could vary while all other maximizing components are fixed.

Choose functionals f_a and f_b uniquely exposing x and y. Each uniquely exposes p in P. These choices belong to nonempty open sets in the ambient dual space. The set of functionals uniquely exposing p is convex: every strict comparison with a different P-vertex remains strict under an interior convex combination.

After perturbing f_a and f_b inside their respective open endpoint cones, their joining segment can be chosen to avoid all cones of codimension at least two in the normal fan of R. There are finitely many such polyhedral cones. For a fixed endpoint outside them, the union of lines through that endpoint meeting any one of these cones has dimension at most ambient dimension minus one; finitely many such sets cannot fill the other endpoint's open cone. Equivalently one may choose a generic pair of endpoints in the two open sets. This is the standard genericity step of the cited fibre proof. For a one-dimensional sum all nonvertex exposed faces are segments, so no higher-dimensional-face obstacle arises. Point factors contribute zero changes. Lower-dimensional summands cause normal-cone lineality, not loss of full-dimensional open vertex cones.

Along f(t)=(1-t)f_a+t f_b, the P-component stays p. Between crossing times each Q_i has one maximizing vertex. At a retained crossing, the exposed face of R is one-dimensional, hence an actual edge, not a circuit direction or a diagonal of a higher-dimensional face. Several Q_i may change together only along parallel exposed segments; those segments sum to a single exposed segment.

For a fixed vertex q of Q_i, every comparison f(t)(q)>=f(t)(q') is an affine inequality in t. The interval on which q is a maximizer is therefore an interval. It cannot disappear and later reappear as the unique maximizer. Hence Q_i changes at most f_0(Q_i)-1 times. Every nonstationary R-edge changes at least one factor. The number of retained crossings in the fibre is thus at most the SUM K, regardless of how many joint tuples of factor vertices exist.

This proves the stronger fibre statement

    diam(Gamma(p)) <= K,

rather than bounding it by the total number of vertices in the whole Minkowski sum of the Q_i.

## 3. Lift the core edges and concatenate

For every edge [p,q] of P, some edge of R joins Gamma(p) to Gamma(q). This is the classical edge-surjectivity lemma (Deza–Pournin Lemma 3.8, applied to Q=sum Q_i). It does NOT require constructing or enumerating that Q.

A direct normal-fan justification also preserves all degeneracies: choose a generic objective in the relative interior of the normal cone of [p,q]. On each Q_i its maximizing face is either a vertex or a segment parallel to q-p. Any nonparallel positive-dimensional maximizing face can occur only on a lower-dimensional subset of this edge-normal cone, unless its direction is parallel to q-p. Avoid the finitely many exceptional subsets. The support face of R is then [p,q] plus parallel segments and points, so is a nondegenerate exposed segment. Its endpoints have P-components p and q.

Choose one such bridge edge for each of the L steps of the supplied core walk. In its L+1 visited fibres, connect the incoming and outgoing lifted endpoints using Section 2. The result uses L bridge edges and at most (L+1)K fibre edges. This proves the stated bound without an assumption about every possible factor tuple or about a product graph.

When r=1 it specializes to the classical one-summand bound. When P is a point it gives diam(sum_i Q_i)<=sum_i(f_0(Q_i)-1). Neither conclusion says that every polytope has a small such representation. In particular one cannot insert arbitrary polytopes as 'small factors' merely because their own diameter is small; the vertex-budget dependence is essential.

## 4. Relation to the current Hirsch framework

The current sum-of-carrier-dimensions estimate alone does not control iterated factor multiplication. Suppose an ACTUAL selected carrier F_j has a certified decomposition

    F_j = P_j + sum_i Q_ji,

where its core route costs at most L0 and its factor budget K_j is at most c*h_j. The result gives a route for that actual pair costing at most

    L0 + (L0+1)c*h_j.

Using the already verified sum_j h_j<=3e and r<=e in the full-availability clipping framework yields the mathematical consequence

    total route cost <= D + [L0+3(L0+1)c] e.

For pyramid cores L0=2 this becomes D+(2+9c)e. These are consequences under REAL decomposition and size certificates for the actual carriers, not a new universal existence assumption. A proof that all arbitrary high-dimensional carriers admit such controlled decompositions is still missing. The module implementing that final clipping adapter is not part of this packet, and no extra open Prove2Me child is introduced to disguise the missing geometry.

#236 owns the actual checked-catalogue/covering/Minkowski equality composition; #238 owns support-witness existence. This work does not modify either. The earlier internal-normal-form candidate remains a separate local draft; none of its uncompiled source is a dependency here. Historical #210 source is not edited or imported as obsolete ancestry.

## 5. Exact implementation and independent verifier

`scripts/simultaneous_minkowski_lift.py` implements the construction for point, box, pyramid-over-box and complete convex-polygon cores. Summands are finite rational point lists. Their generator size is input; the tool does not discover a decomposition of an unrelated original H-polyhedron.

The constructor chooses a core path, constructs generic exposed bridge edges, and runs a SINGLE simultaneous envelope sweep in each fibre. It computes pairwise equality times separately within each factor, discards crossings not on the upper envelope, and merges simultaneous parallel changes. It never enumerates the Cartesian product of factor point choices. A nongeneric higher-rank crossing is rejected, and endpoint objectives are perturbed inside the SAME open endpoint cones, so the requested vertices do not change. Random search has explicit caps: failure reports failure, not a partial certificate or a universal running-time claim.

Every returned edge contains its supporting normal, component endpoints and nonnegative parallel interval lengths. The verifier checks the ENTIRE supporting face in every summand and in the core, rather than checking only that the two endpoints tie. The exact support-face identity from the existing PolynomialMinkowskiExposedEdges argument then gives the whole exposed segment in R. Zero coefficients and collinear listed nonvertices are retained. Empty or duplicate point lists are rejected explicitly; point summands have a one-point list. A user may remove exact duplicates before constructing the model, but the checker never ignores an untested point.

For a box or pyramid core, an analytical support oracle checks all defining inequalities without enumerating its vertices. A box support face is generated affinely by one corner and its free-coordinate flips; if those generators fit a line, there is at most one free coordinate and they are the full segment endpoints. A pyramid adds the apex when tied. Thus a higher-dimensional support face cannot slip through as a segment.

`check_sweep` does not rerun event enumeration: it recomputes exact affine maxima, verifies increasing sample times, checks every exposed edge, and independently recomputes the sum of slope ranks. Each transition increases that integer potential; the total is bounded by K. `check_lift` validates the core projection, bridge/fibre continuity, all original component faces and the total bound. A JSON readback can be checked separately using `--verify`.

## 6. What is and is not formally proved

The standalone Lean target `Hirsch.affine_envelope_exposed_edge_budget` proves the FINITE CERTIFICATE statement. Its maximizer-change lemma derives strict slope increase from actual affine comparisons. The sum of finite slope ranks supplies N<=sum_i(k_i-1), without assuming non-revisiting or the desired count. Exact global supporting slices then prove ordinary adjacency using Mathlib IsExtreme and segments. The supporting-slice proof adapts the already integrated `supportFace_isExtreme` argument; it does not assume a conjectural diameter theorem.

The normal-fan generic-existence, per-core bridge existence and full geometric theorem of Sections 2-3 are mathematical proofs in this note, not silently claimed to be the public Lean theorem. The executable constructor and rational JSON parser are not Lean-extracted. The accepted theorem, should its gate succeed, certifies a finite proof interface, not every JSON file without a Lean instantiation. For a zero-step certificate the public theorem has no edge obligations and does not assert arbitrary endpoint membership in R; for nonzero length the supporting-segment witnesses supply the endpoints and edges.

The local runtime has no Lean/Lake executable; public-host DNS and toolchain preflight failed. The prepared PR-comment gate is the only new compile request. Static source checks and exact Python tests are NOT Lean verification. Actual gate/audit/publication status is preserved separately from this mathematical explanation.

## 7. Reproduce

    python3 scripts/test_simultaneous_minkowski_lift.py --stage small --out /tmp/lift-small.json
    python3 scripts/test_simultaneous_minkowski_lift.py --stage large --out /tmp/lift-large.json
    python3 scripts/test_simultaneous_minkowski_lift.py --stage negative --out /tmp/lift-negative.json
    python3 scripts/simultaneous_minkowski_lift.py --verify research/fixtures/simultaneous_lift_32d.json

The small suite compares every returned edge against ALL explicit point sums, and checks planar routes against an independently constructed complete rational convex hull and graph. Nonshortest routes are retained rather than omitted. The large suite uses explicit factor presentations and support oracles, not a newly discovered original-H equality. The 32-dimensional example has a pyramid core with 2^31+1 vertices and 24 triangular summands; the core vertex count is an exact formula, NOT an enumeration or an asserted vertex count of the final sum. See the execution receipts for the actual path lengths and the conservative additive bounds. Exponential iterated-lift bounds in that table are loose upper estimates, not lower bounds on actual graph distance.
