# Explicit finite-generator Minkowski completion

Let n>0 and v:Fin n -> R^d be arbitrary. Set

    P = conv {v_i},
    Z = sum_(i,j in Fin n) [v_i,v_j],
    Q = intersection_i (Z-v_i).

The claim is that Q is nonempty compact convex and P+Q=Z exactly.
The actual coefficient model of Z uses independent t_(i,j) in [0,1] and
sum_(i,j) [t_(i,j)*v_i + (1-t_(i,j))*v_j]. This is not a supplied completion
or a support-equality hypothesis. It includes duplicates, interior points,
collinear data, n=1 and d=0. See the handoff for the actual Lean run status.

## Direct proof of the missing support witness

Fix ANY real linear f. Choose k with f(v_i)<=f(v_k) for every i. In every
ordered slot(k,i), choose v_k; in all other slots choose an endpoint maximizing
f. Ties are harmless. The resulting z maximizes f over the entire coefficient
cube image Z: each weighted pair value is at most its chosen endpoint value.

For every i, replacing the one endpoint in slot(k,i) by v_i produces precisely
z-v_k+v_i in Z. Put q=z-v_k. Then q belongs to ALL translates Z-v_i at once,
so q is in Q. Moreover v_k+q=z attains the maximum f on Z. The i=k replacement
changes a diagonal coefficient but not its contribution; it causes no exception.

## Why all points, rather than just support samples, are covered

Z is the continuous image of the finite coefficient cube, hence compact. The
coefficient convex-combination identity proves it convex. Each defining
translate of Q is closed and convex. Since n>0, any one translate bounds Q,
which is therefore compact; f=0 in the construction supplies nonemptiness.
If q+v_i belongs to Z for every i, convexity extends this to q+P subset Z.
Consequently P+Q subset Z. The finite hull P is compact and convex, so is P+Q.
A z in Z outside P+Q would have a strictly separating continuous linear f.
The constructed support-attaining v_k+q in P+Q contradicts that separation.
This proves whole-set equality for arbitrary real vectors, without sampling.

## Count the right object

The formula contains exactly n^2 represented ordered slots. Diagonal slots
may have zero length; off-diagonal slots repeat unoriented directions. No
minimality, optimal number of directions, full dimension, or irredundant facet
count is inferred. The direct construction was chosen to make the replacement
argument uniform, not to optimize its inventory.

For an arbitrary H-polytope, n may be the size of its full vertex inventory,
which is not bounded here in terms of original rows. The result therefore does
NOT give a facet-polynomial completion. A large inventory for this formula is
also not an obstruction to all other completions. Applying the construction
to dual generators would require a separate, proved transfer back to primal
ordinary-edge routes; duality does not identify those two vertex graphs.

The theorem does not supply a zonotope edge path. An edge of the coefficient
cube is not declared an original edge of its image. Accepted #309/#310 cover
the contraction and original-H endpoint-lift steps once an actual compatible
sum-route theorem is present. Here the new contribution is the explicit whole
completion itself, not a re-publication of either transfer. A genuine short
sum-route proof and a useful original-input complexity bound remain separate.
No unrestricted Polynomial Hirsch, improved best classical diameter, or
historical priority is claimed. The classical normal-fan/Minkowski-summand
viewpoint is credited in the publication explanation.

## Exact independent arithmetic checks

A single Fraction-only script builds the complete planar Z by actual segment
addition, derives Q independently from the translated supporting inequalities,
solves all planar basis intersections, and compares the whole hull P+Q with Z.
All46 models pass, including repeated/interior/collinear generators. Across
these models it records1208 support witnesses,6627 exact replacement identities
and42189 coefficient bounds. The totals759 Z vertices and759 Q vertices are
sums over separate models, not one combined polytope or a universal count.

Nine additional support-witness instances include d0 and reach d64. Their
complete high-dimensional bodies and graphs are NOT enumerated. Nineteen saved
records replay with witness/hull/intersection discovery disabled. Four forged
records are rejected. Clean script-only replay reproduces the entire12437-byte
report and33706-byte fixture byte-for-byte. These are not Lean-extracted code
or a verified arbitrary-JSON implementation.

    python3 scripts/test_pair_segment_completion.py --out /tmp/pair-completion

The complete report/fixture are in the export; repository readbacks are clearly
labelled derived summaries. Compilation, axiom auditing, authenticated ACCEPTED,
and publisher Proved are distinct events and must be checked in the handoff.
