# Disjoint face-cut routes: continuation handoff

## Scope and ownership

Baseline main `f2957916eee3d28e407253d0ff8fec6271747f26`; branch
`research/disjoint-face-cut-routes`. Read current STATUS, instructions and LIVE
PRs again before starting work. Coordination comment5690955296 on #272 was
actually posted and read back. This work does not alter its global cut-direction
cover, #271's exclusion logic, #270's blocked companion, any accepted/pending
packet, other active branches, or retired/reserved #210.

Written theorem and exact research code ONLY. No Lean source, local compile,
axiom audit, Actions run, Prove2Me theorem/submission, or fresh authenticated
root/leaf poll is produced. Local lean/lake are absent and release-host DNS
failed. Do not post a publication trigger for this research-only package.

## Completed result

For a nondegenerate explicit box with k shallow, pairwise disjoint cuts of
original faces of codimension>=2, construct a genuine original-edge path for
ANY two vertices. The algorithm recognizes the class from the actual cut
coefficients. A cut may remove a whole exponentially large box face. Every
original inequality has a strict relative-interior witness; the final polytope
is simple, full-dimensional and bounded with m=2d+k genuine facets.

The route lifts a single-flip coordinate order through caps of the form
simplex times box. Each cut face is visited at most once. It preserves the
least common original face and never revisits an original facet. Conditional
expectation chooses the coordinate order: an internal face is visited with
probability1/binom(a+b,a), where a fixed coordinates must first flip and b must
not yet flip. Endpoint-port contributions are computed exactly. Thus

    actual route <= floor(exact expected spliced length),
    diameter <= min(d+k,2d).

The 2d bound is sharp for opposite same-port vertices in the fully truncated
cube. This is a CLASS construction, not a universal representation theorem or
new best-known-diameter claim. Classical truncation and derandomization
principles are credited in the complete note. The explicit data-dependent cost,
raw-H recognition, general face-cap state transitions and saved original-row
certificate integration are the work supplied here.

The algorithm uses no LP, global direction inventory, graph enumeration,
minimal-nonface classification or random retry. Its conditional decisions take
O(d^2) candidate evaluations, each inspecting k cut patterns; arithmetic and
certificate checking are polynomial in explicit input size. Hidden affine-box
recognition and arbitrary intersecting cuts are not supported.

## Actual results and adverse case

SAME #272 deterministic capped_box inputs in d4/8/16: new paths4/8/16, versus
independently rechecked reverse-coordinate comparisons7/15/31. The d32 extension
of that generator is NEW, with32 versus63. The old shadow LP runs are historical,
not rerun here. The new d-edge routes are shortest by missing-target-facet count.

NEW noncorner cases truncate x0=x1=0 while keeping disjoint other corner cuts.
The32D input has89 genuine facets and one cut removing2^30 old cube corners.
It returns32 original edges with no common endpoint facet, expected-length
floor32, and an all-pairs CLASS bound57. The5,368,709,864 vertex count is a
formula, not graph enumeration. The8D companion has23 facets and8 edges.

The10 small exact H references cover2079 active bases,156 vertices,256 edges,
and615 route pairs. All615 are nonrevisiting;1497 delivered edges equal BFS
on those pairs. Exact averages match1572 coordinate permutations. Separate
sharp examples attain d+1 and2d. A5D/17-cut adverse instance returns6 when a
saved5-edge route is shortest; all120 orders were tested. Never claim greedy
optimality from the small suite. Tiny cut depths through2^-160 and positive
row rescaling are checked. Twenty-one invalid/unsupported controls fail.

## Source integrity and verification limits

Two NEW scripts:
- disjoint_face_cut_routes.py, blob9afe4739a6a9878fb67e4a667fccb5bfa7f994fa,
  SHA2568d9d39a080e3dddf2597b1cde9d6f5cec8d460406b477b474791f176416ce4ce.
- test_disjoint_face_cut_routes.py, bloba95e8877241025b7e69975bfde9cff845ed6dc46,
  SHA256c0158dae222003bea0561bc8d7842df3e55de0555ca2e4233eff19bb8dd5aa07.

They import UNCHANGED #271 original_route_exclusion.py,
bloba764196e54970825823cad4575b947b507f95951,
SHA256b0e5eff7a96ca336f62d69a1ad24ddf2919d8ea43077b6150e76ecf6f7c869fe.
The remote blobs were read back and match tested local bytes.

Saved verification disables order selection, inverse/elimination discovery,
path and facet-anchor production. It rechecks24 full route records and five
saved comparison paths/121 comparison edges. The consumer still computes
explicit class membership and the given finite splice; it does not trust
expected lengths, rank claims, adjacency or facet genuineness from metadata.
No universal correctness of Python/JSON is claimed as Lean-verified.

A fresh three-source workspace reproduced ALL four raw reports and17 full
fixture files BYTE-FOR-BYTE, without ignoring timing fields. Sources/manifests
and compact summaries are derived local research records, not server receipts.
Full raw reports and fixtures accompany the download and regenerate as below.
No existing source is replaced by the dependency copy in the standalone bundle.

    for s in small large negative audit; do
      python3 scripts/test_disjoint_face_cut_routes.py --stage "$s" \
        --out "/tmp/$s.json" --fixtures /tmp/face-cut-fixtures
    done

For a single input use scripts/disjoint_face_cut_routes.py INPUT --output OUT.
For saved verification pass only the nested certificate via --certificate.
Consumers need only Python standard-library arithmetic; SymPy is test-only.

## Next conjecture-facing obligation

Overlapping cut neighborhoods or cuts not localized at a single original box
face invalidate the state/port description and the simple precedence-event
probabilities. Arbitrary polytopes do not come with a certified cubical base.
A useful next step must prove route-local visit/transition control in a genuinely
larger class, not assume a small global catalogue, a low-overlap representation
or a polynomial expected number of detours for arbitrary carriers. #267's
complete forward-stellar-size obstruction remains intact. Reuse #271 for exact
negative controls and keep unrestricted versus restricted exclusions separate.
