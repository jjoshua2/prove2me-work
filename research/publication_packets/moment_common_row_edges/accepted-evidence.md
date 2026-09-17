# ACCEPTED: original common rows expose the entire moment edge

Public theorem: `Hirsch.moment_common_rows_expose_edges`.
Theorem ID: `d727e34d-b52e-4bfa-8291-947010b1f130`.
Submission ID: `27db3c8f-ba4b-4b18-8740-dc9f979266dc`.
Trusted publisher verdict: ACCEPTED; authenticated readback: Proved.
Accepted proof SHA: `2e5a27346baa0c00f5329bcb6e8c44a67278281a`.
Successful run: `35250192632`; PR #295.
Corrected trigger comment: `5718229252`; verdict comment: `5718278278`.
Verdict time: `2026-09-17T17:05:18Z` (13:05:18 America/New_York).

## Exact formally verified content

For d<m and injective real parameters on m original labels, let P be the
original d-dimensional mean-centered moment halfspace intersection. Let I,J
be the EXACT tight-row sets at feasible points u,v. If |I|=|J|=d and
|I intersection J|+1=d, then:

- u and v are distinct actual Mathlib extreme points;
- the entire common feasible equality slice is exactly segment R u v;
- the sum of the common ORIGINAL rows is at most |I intersection J| throughout
  P, attaining equality exactly on that segment;
- the segment is an actual Mathlib IsExposed and IsExtreme subset of P;
- each strict interior convex combination has exactly the common rows tight.

The proof derives vertex status and active-row independence, not a rank, vertex
list, adjacency, support-functional or edge oracle. Given an arbitrary point z
in the supporting slice, its affine coordinate is recovered from a source-
private row. A target-private row bounds that coordinate by one. This proves
WHOLE-slice equality, not just equal objective values at endpoints, and hence a
nondegenerate exposed segment of the original system. No projected edge is used.

The public conclusion is a sufficient edge criterion, not the converse or a
polynomial route count. It does not construct a sequence of feasible tight-row
exchanges or prove Polynomial Hirsch. The boundary case d=1 correctly allows
the zero sum over empty common rows to expose the entire interval. Not every
one of the m inequalities is claimed an irredundant facet in every boundary
case; the theorem is stated on exact original row sets.

The complete namespace proof prefix from ACCEPTED #293 is reused byte-for-byte;
its old public solution and prints are excluded. Its verified artifact and all
five frozen hashes were checked. It is a proved dependency, not a new assumption.
#293's original PR/integration and all other agents' branches are untouched.

## Real two-gate history, not a first-attempt-success claim

The initial591-line proof reached Lean in run35249570081. All FOUR new helper
lemmas compiled with only standard axioms, including common-slice equality and
actual exposedness. The public wrapper alone failed at line582 because a
rewrite pattern did not match its inlined row expression. Publication was
SKIPPED; no theorem registration or submission existed from that run.

The only mathematical-source edit adds `change` to restate that public goal
with the already-defined row/active names and gives the rewrite its explicit
common-row set. Every substantive helper, the accepted dependency prefix, the
public signature, problem.json and explanation.md remain unchanged. The first
diagnostic and exact source diff are preserved. No admission was introduced.

The corrected596-line solution, driver and target all compiled with exit0.
All FIVE transitive audited declarations use only propext, Classical.choice and
Quot.sound. The corrected proof's FIRST actual platform submission was accepted.
Harmless linter warnings remain in the raw driver log; no warning suppression
or post-verification proof cleanup changed the frozen source.

The user-requested NEW top-level comments invoked the existing workflow:

    /prove2me publish research/publication_packets/moment_common_row_edges

No workflow_dispatch, workflow, pin, permission, token, protocol or trusted-main
secret split changed. Local Lean/Lake was unavailable; compilation is the pinned
hosted run. The rational tests are not being relabeled as Lean verification.

## Original artifacts and independently checked identities

Original ZIP archive digests, recomputed after connector download:

    first request: 9af9c7b10a289ea059ff8009417027d9a42945e394ea0571f3b1d01bd20af657
    corrected request: 4e609317eb3ff9137eeb6a652688e1605b4c9177afd58a4a60454247ce07d999
    verified: 0b4bd54a643462ce571dd34de07c616354daf5e8b3ad77a66d0e55eee7f903fd
    publication: 3b80adca200dccc078ad5c35d41901013b533f0867f67baa23346c7da292750c

All FIVE frozen source/driver/statement/metadata hashes were recomputed. Solution,
problem and explanation match the corrected local packet byte-for-byte. Source:
`a0e6bb32eca92681ed7e526f68c66d75348421f9863a11aa0ccbc11016bfcc34`.

Raw packet audit, driver log, verified manifest and aggregate publication receipt
are committed unchanged. The artifact-readback record is labeled a local derived
check, not a fresh direct platform API response. The original publication ZIP
contains the aggregate receipt and generated bot comment, not individual API
responses. Proved is the authenticated trusted publisher's observation. No
missing raw responses or compiler logs are fabricated. The failed run's note
is explicitly a diagnostic excerpt/summary, not its complete raw job archive.
Post-verification commits add only supporting/evidence files; the submitted
proof and metadata are not altered. Historical prepared status is superseded.

## Reproduction and limitations of supporting software

    python3 scripts/test_moment_common_row_edges.py

Nine complete small references solve411 exact square systems and recover125
vertices,265 adjacent pairs and928 diagonals. All adjacent pairs have exactly
two maximizing reference vertices for their common-row objective; all diagonals
have additional maximizers. The tests include28816 objective evaluations,
1060 interior points,1060 outside-line rejections,21850 original-row evaluations
and286 excluded infeasible full-tight solutions. Repeated parameters produce a
real counterexample to row-count-only reasoning; injectivity is not decorative.

Four larger samples through dimension64 check original root-polynomial vertices
and every original inequality, without full graph enumeration. Thirteen saved
consumers pass with production disabled; eleven malformed cases are rejected.
A clean standalone workspace reproduces the full5104-byte report and54653-byte
fixture exactly. Python, the JSON parser and those tests are not Lean-extracted.
The bundle preserves original ZIP artifacts, both initial/corrected proof bytes,
the correction diff and the complete numerical fixture.

## Next interface

This accepted result turns an actual feasible one-row exchange in the moment
system into a genuine exposed original edge. A future route proof can reuse it
instead of assuming adjacency from labels. Existence and a uniform polynomial
bound for such a sequence are separate obligations; no claim to them is made.
The other catalogue, compactness and vertex results have their own exact scopes.
Do not resubmit this theorem or restart #293's already accepted vertex proof.
