# ACCEPTED: construct the minimal projected face from fibre duals

`Hirsch.projected_minimal_face_from_fibre_duals` is ACCEPTED with the trusted
publisher's authenticated live status Proved.

- Theorem: `2e10b83d-9a75-4d41-a7e5-95a483d787aa`.
- Submission: `4f1c0864-fd8d-47d1-96b6-2c823601c987`.
- Proof head: `6dbd85efa51b866151301d4255ecb268db8efcfb`.
- Successful run: `34896633534`.
- Real top-level command: https://github.com/jjoshua2/prove2me-work/pull/247#issuecomment-5670781232
- Authenticated verdict: https://github.com/jjoshua2/prove2me-work/pull/247#issuecomment-5670825890
- Solution blob: `5c2935e1f2bd6831cfc9c9df119038e71df74666`.
- Solution SHA-256: `f06d51585f7741405e8adffdd2012c8844c224110672df9c5d70e4648f39804a`.
- Verification artifact: `10369011887`, ZIP SHA-256
  `e40df88f18acd7216501c8f36f570cbec7940122ec3e06515efe06a3662e2dcd`.
- Publication artifact: `10369402650`, ZIP SHA-256
  `5a9163c2f35948537fbd57dc5d0a9f15c2da05662089ac33650abeaadc73e8a9`.

The ORIGINAL 288-line proof passed its FIRST prepared compiler/axiom gate and
FIRST platform submission unchanged. Driver, solution and statement exit codes
are all zero. All six printed declarations depend only on propext,
Classical.choice and Quot.sound. The unused-section-variable linter warning is
retained verbatim in solution-compile.log; it is not a proof failure.

Both archive digests and all five frozen packet hashes were independently
recomputed. Frozen solution, original problem metadata and explanation bytes
equal the prepared local files exactly. packet-audit.json, verified-artifact.json,
solution-compile.log and publication-receipt.json are RAW downloaded records.
This Markdown is a derived summary, not a fabricated raw API response.
The post-gate additions are software, tests, receipts and handoff documentation;
no accepted source, statement or problem metadata changes.

## Exact result and remaining limits

From a finite strict anchor and original-row fibre optimality identities, the
proof constructs the image exposing objective, WHOLE exposed face equality,
Mathlib IsExtreme, minimality among every extreme subset containing the anchor,
and all-submodule equivalence of face directions with images of the selected
row kernel. No exposer, source vertex/edge, boundedness or one-dimensional
preimage is assumed. These properties are not imported as unknown oracles.

The separate executable algorithm discovers those witnesses from A,b,G,u,v and
uses #246 for positive edges; explicit convex-decomposition witnesses reject
nonedges. It requires no graph or given selected face. The exact tests classify
222 queries:39 edges and183 nonedges, with17 rejected malformed/capped cases.
These are not route counts or Lean-extracted/kernel-evaluated JSON results.
Polynomially many LP calls for one edge query do not bound simplex pivots or
the number of edges in a path. The full arbitrary-carrier Polynomial Hirsch
bound remains unproved. The distinct #244 core-walk concatenation stays with
its existing owner; this proof and software do not replace that assembly.
