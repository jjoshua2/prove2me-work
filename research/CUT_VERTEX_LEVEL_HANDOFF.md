# Aggregate-cut vertex levels: handoff

Base main338d1f9e1cc20df86998efa5f0dc6e92916329e8; coordination on #272
comment5691694671. This is an add-only research contribution, not Lean or a
platform verdict. #274 and #275 are preserved and credited, not duplicated.

## Exact result

Every new vertex after cuts lies in a base face F whose dimension equals the
rank of some active cut restrictions. Choose an affine basis of base vertices
containing it convexly, allowing zero weights. Cut images determine its unique
barycentric weights. Enumerating those small systems gives a complete coordinate
alphabet, not just one learned from sampled vertices.

For ell base levels, s cuts, cut rank R and an M-element cover of their vertex
images, the alphabet has at most

    ell + sum_(r=1..R) binom(s,r)binom(M,r+1)ell^(r+1).

If the cut matrix has p distinct nonzero COLUMN vectors, cuts depend on p
variable-group totals, R<=p, and M is polynomial in d for fixed ell,p. This
allows arbitrarily many cuts, arbitrary real coefficients and arbitrarily bad
numerical separation. For fixed grid alphabets the final full-dimensional
facet-only diameter bound is O(m^((p+1)^2)), after mathematical removal of
redundant added cuts. No efficient arbitrary hidden-base recognition is claimed.

The consumer reconstructs the entire alphabet, verifies original-H vertex
and edge right inverses, phase supporting duals and rank drops. It uses no LP
or tangent discovery, but DOES recompute image elimination. Construction uses
successive exact objective optimizations to isolate a true tangent extreme
ray, not the signed-normal-only lexicographic denominator bound from #274.
The old Bland engine is unchanged and has no polynomial internal-pivot claim.

## Important adverse control

The clique/cardinality family has exponentially many actual edge directions
but a linearly bounded post-cut coordinate inventory when 3/2<B<2. The actual
8D/16D/24D routes have10/26/42 edges. They are shortest ONLY in their minimal
common face. The unrestricted distance is THREE, via e0 and elast, for d>=5.
Do NOT relabel the in-face distance as global. The complete proof includes
both bounds and the original three-edge comparison packets. The earlier chat
update briefly conflated the two; it was corrected immediately and the final
sources/receipts preserve the proper distinction.

A rank-one cut of a cube can also create2^(d-1) distinct coordinate levels when
its coefficient columns all differ. The cut polytope is still a combinatorial
cube with diameter d. Low rank alone is not a small image-spectrum certificate.

## Reproduce exact final stages

    python3 -m py_compile scripts/cut_vertex_levels.py scripts/test_cut_vertex_levels.py
    for m in cube_one cube_two cube_slice cube_point triangle_cut clique4_cut cycle_two tiny_two many_rank_two; do
      python3 scripts/test_cut_vertex_levels.py --stage small --model "$m"
    done
    python3 scripts/test_cut_vertex_levels.py --stage small
    for s in clique8 clique16 clique24 extra obstruction negative; do
      python3 scripts/test_cut_vertex_levels.py --stage "$s"
    done
    python3 scripts/test_cut_vertex_levels.py --stage assemble

A no-argument invocation also runs the whole suite, including each small model.
The separately named model stages avoid a tool-timeout ambiguity; the earlier
combined process stopped at45seconds and is NOT counted as a completed suite.
SymPy is a small-reference test dependency. Production and auditing require
only exact standard-library rational arithmetic and the frozen old modules.

Dependencies: cut_direction_routes.py, exact_farkas_lp.py,
endpoint_transfer_routes.py and simple_tangent_policy_audit.py, copied without
changes. All new input rows must match the recognized base plus actual cuts;
unknown kinds, floats, missing levels and caps fail explicitly. The complete
reports and fixtures regenerate; committed summaries are labeled derived.

There was no local Lean/Lake executable and public release/GitHub DNS failed.
No uncompiled proof skeleton, speculative Actions gate, new registration,
Prove2Me submission, pin change, credential operation or owned-branch edit is
part of this packet.

Concurrent finalization: main af9d1ea0e2d8d07c2b1021083e2e6cfe81b20e32 adds the
OTHER agent's AFFINE_LEVEL_BARRIER.md. It proves an exponential global-level
obstruction over EVERY injective affine chart of classical bounded Klee--Minty
cubes of diameter d. Our one-rank-one-cut example is not that all-chart theorem.
The new result and its adaptive prefix-face positive comparator are preserved.
Do not seek a universal globally small alphabet by affine preconditioning.
The next unrestricted target must be face-adaptive or route-local levels, or
another invariant, with its cost derived rather than assumed. Do not declare
the boxed arbitrary-polytope representation polynomial when p grows with d.

All final stages also passed after the five core additions were applied as a
patch in a fresh FOUR-dependency Git workspace. Every nontiming field and all
THIRTEEN full fixtures match. One combined replay command timed out before the
many-rank-two model finished; that model then completed in its separate call.
Only the individually completed records are assembled. Subsequent changes are
proof/handoff reconciliation prose, not executable changes. The final six-file
research patch has an additional source-bound derived replay manifest.
