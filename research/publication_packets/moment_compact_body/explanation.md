# Original moment inequalities form a compact convex body

## Exact new formal target

`Hirsch.moment_curve_compact_body` takes a positive integer k, an integer m with
2k<m, and an injective REAL parameter map a:Fin m -> Real. The original rows are

    row(x,i) = sum_(j=1..2k) (a_i^j - average_l a_l^j) x_j,
    P = {x: every ORIGINAL row(x,i)<=1}.

It proves all of the following:

- P is compact in the original finite-dimensional real space.
- P is convex.
- Zero lies in the ordinary AMBIENT interior of P, so P is full-dimensional.
- Every original row i has a feasible point where that row equals one and all
  other original rows are strictly below one.
- Every feasible coordinate satisfies an explicit parameter-dependent box bound

    |x_j| <= m * sum_i |coeff_(j+1)(Lagrange.basis(univ,a,i))|.

Boundedness, a vertex catalogue, an inverse/rank certificate, compactness,
full-dimensionality, and the supporting points are NOT premises. No coefficient
extension, projection or artificial cap changes P. The nodes need not be ordered,
equispaced, integral or rational; exact rational inputs are used only for tests.

This is the geometric-realization interface left separate by #288 and the
concurrently owned #289 catalogue/count theorem. The latter is not modified
or retriggered. The statement does not yet contain Mathlib's facet-dimension or
simplicity predicates, a complete face-lattice identification, or an asymptotic
or ordinary-edge diameter theorem. The explicit uniquely-tight support property
is reported literally, not as an independently formalized entire facet lattice.

## Accepted dependencies and new proof steps

The namespace proof bodies `Hirsch.MomentSmallFaces` and
`Hirsch.MomentBarycentric` are reused from accepted #288, source
blob e85d05dd4a6208ff8311809d1f456d9c6a84d011, with the old public target and
ordered-sign namespace omitted. One unused local membership binder is named hi
instead of an underscore; all other dependency bytes, types and proof steps
are unchanged. These bodies were already compiled and audited
under the unchanged Lean4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f
pin. They are proof code, not additional axioms; neither earlier public theorem
is submitted again. All new geometric conclusions are proved in MomentCompact.

For a feasible x, the accepted slack polynomial is

    p(T)=1-sum_(j=1..d)(T^j-average_l a_l^j)x_j,  d=2k.

The new coefficient lemma proves coeff_j(p)=-x_j for j=1,...,d. The accepted
centering identity gives sum_i p(a_i)=m. Feasibility gives p(a_i)>=0, hence every
p(a_i)<=m. This is a proved bound on actual slack VALUES, not assumed control of
coefficients or of the original feasible set.

Because deg(p)<=d<m and the nodes are distinct, Mathlib's Lagrange interpolation
identity gives

    p = sum_i C(p(a_i)) * L_i.

Taking each coefficient, applying the absolute-value triangle inequality and
using 0<=p(a_i)<=m yields the displayed coordinate bound. The constants are
constructed from the original parameters. Their size may be very large or
ill-conditioned; no dimension-only, polynomial-bit or uniform numerical bound
is claimed.

P is an intersection of finitely many continuous closed halfspaces, hence closed.
The coordinate bound embeds it in an explicit compact product interval. A closed
subset of that box is compact. The proof applies this to P itself, not to an
unrelated bounded representative or an auxiliary polytope.

For interior, the strict halfspaces row(x,i)<1 form an open set containing zero.
It is a subset of P. Thus zero belongs to interior(P) with respect to the original
ambient topology. Convexity follows by distributing each row over nonnegative
convex combinations. The accepted squared-root small-face construction applied
to {i} gives the final unique-tight-row support points (k>0 is used here).

The core compactness helper is more general: it works in any dimension d<m.
The combined public target specializes to positive even dimension so that all
singleton support witnesses are included in the same exact statement.

## Hypotheses are necessary, not cosmetic

Without enough nodes, centered rows can fail to span the original coordinates.
For d=2 with nodes0,1, their two centered columns coincide; every multiple of
(1,-1) lies in the common kernel, so the feasible set is unbounded. With three
identical nodes all centered rows vanish. Those explicit exact countercontrols
are included in the tests. They do not replace the universal proof under the
actual injectivity and node-count hypotheses.

## Supporting exact computation and publication boundary

The producer constructs rational nodal basis coefficients by synthetic division.
The consumer does NOT rerun that construction: it checks all nodal Kronecker
values, recomputes the ORIGINAL centered rows, verifies every interpolated
coefficient, checks the explicit box, and checks all unique-tight-row witnesses.
An explicit positive inner-cube radius is also checked for each numerical input.
The complete consumer replays with coefficient and witness producers disabled.

The suite has12 nonuniform, scrambled-label small instances plus two samples
in dimensions16 and32. It checks310 feasible points,7902 original inequalities,
7592 reconstructed nonconstant coefficients,4052 coordinate bounds,6318 nodal
identities and198 unique-tight-row supports with6120 strict-other-row checks.
Ten malformed/out-of-domain controls are rejected, and all14 full stored
certificates are rechecked with the polynomial/witness producers disabled.
No full vertex graph, all high-dimensional vertices or exponential catalogue
is enumerated. These are rational interpretation checks, NOT Lean verification
or proof that the Python parser is formally sound.

The originating runtime has no Lean/Lake/gh executable and cannot resolve the
public toolchain host. The prepared source therefore remains uncompiled until
the requested existing PR-comment gate actually runs. The only public preamble
is import Mathlib/open scoped BigOperators. The top-level solution signature
matches problem.json exactly and requests five transitive axiom reports.
No proof admission, imported target, custom axiom, new workflow, permission,
credential or toolchain change is involved. An actual compiler or platform
failure must be preserved, not reinterpreted as success.

Requested publication command on this new packet's OPEN same-repository PR:

    /prove2me publish research/publication_packets/moment_compact_body

A posted comment is a request, not a verdict. Only the exact pinned compile/axiom
audit and authenticated publisher receipt establish acceptance. Do not duplicate
accepted #285/#286/#288 or another agent's pending #289 submission.

## Sources and remaining work

Classical interpolation and compactness are not new mathematics. Primary library
infrastructure checked for the pinned source includes Mathlib/LinearAlgebra/
Lagrange.lean, Algebra/Polynomial/Coeff.lean, Topology/Order/Compact.lean and
Topology/Compactness/Compact.lean. The new contribution is a complete checked
bridge for the project's precise ORIGINAL-H statement with no assumed geometry.

After this target, a full formal simple-polytope realization still needs the
remaining facet-rank/simplicity and face-lattice interfaces as appropriate; #289's
catalogue and #281's counting inequality retain their own verified scopes.
This compact-body result is not a polynomial graph-diameter bound or a solution
of Polynomial Hirsch. It makes the specified bounded geometric object available
without silently assuming the necessary realization facts.
