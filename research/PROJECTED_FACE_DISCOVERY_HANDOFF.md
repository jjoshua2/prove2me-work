# Accepted projected-face discovery: next use, not another reproof

PR247 extends accepted #246 without editing its source/auditor or the separately
owned #244 core-walk assembly. Read the exact accepted-evidence.md and raw receipt
under research/publication_packets/projected_face_discovery/. The packet passed
its first prepared gate and first platform submission unchanged. Do not resubmit.

Theorem Hirsch.projected_minimal_face_from_fibre_duals:
2e10b83d-9a75-4d41-a7e5-95a483d787aa; submission
4f1c0864-fd8d-47d1-96b6-2c823601c987; authenticated ACCEPTED/live Proved.
Run34896633534, frozen head6dbd85efa51b866151301d4255ecb268db8efcfb.
The 288-line Mathlib-only proof has six standard-logical-axiom printouts.

## The now-proved bridge

A feasible anchor is tight exactly on J and strict off J. Exact row-dual
identities certify that each selected row is universally tight in its image
fibre. Summing the duals CONSTRUCTS the image exposer with positive original-row
weights. The whole selected face image is the smallest extreme subset containing
the anchor image. Every selected-kernel direction has feasible two-sided local
representatives. Hence the image face's direction tests are exactly the image
of that kernel, not merely bounded above by a guessed rank.

No image exposer, source vertex/edge, compactness or bounded preimage is assumed.
The finite witness-production/exact-LP existence argument is separate from the
formal certificate theorem. Its Python producer and JSON parser are not extracted
from Lean; generic acceptance does not separately kernel-evaluate all fixtures.

## Reproduce the original-image edge queries

    python3 scripts/test_projected_face_discovery.py
    python3 scripts/projected_face_discovery.py input.json --output decision.json

Input is only A,b,G,u,v. Endpoints must be distinct feasible IMAGE points.
The --certificate option expects the inner certificate object. All finite input
numbers must be exact integers or rational strings, not floats.

The routine finds preimage lifts, the midpoint fibre's forced original rows,
a strict anchor and the image exposer. It then either produces #246's actual
whole-image edge certificate or an explicit geometric NO_EDGE witness. The
negative witness is a feasible transverse midpoint decomposition or a feasible
point beyond a purported endpoint. Infeasibility or a computation cap is an
INCOMPLETE-query error, not a negative edge verdict. The exact Bland engine has
no asserted polynomial pivot bound, despite polynomially many LP calls.

The LP module was absent on current main and is transplanted BYTE-FOR-BYTE from
historical blob ea511a79164d953792942d8be3dd3537646738d6, without merging retired
ancestry. Its SHA256 is65a8731600a6750b5334307415cd37c79d201d47e179bea5cdcbd511363006d0.
The #246 auditor remains unchanged at bloba2a4305c22ded1b8040bab617db5ddef956867be,
SHA256bdfc632d6f14e36d953d51e0017de926ba7d0659341e522aa17a1f46d08e6bf4.

Exact regression:222 queries,39 image edges,183 nonedges,17 rejected forged or
capped cases. Six independent small hulls check209 pairs, including133 queries
with a nonvertex image point;47 true source edges project to NONedges. The13
additional cases include lineality/no source vertices, unbounded fibres and
images, lower-dimensional images, unknown dense affine coordinates, duplicate
rows and projection gaps2^-120. The auditor is rerun with all discovery/linear
algebra entry points disabled. The tests regenerate full fixtures and detailed
receipt; the committed EXECUTION JSON is labeled as a derived summary.

## Conjecture-level next task

A complete per-pair edge test is NOT a polynomial-length route construction.
Future work must select a sequence of genuine image edges with polynomial
TOTAL cost measured in the original IMAGE facet count. A smaller auxiliary
H-description and a short source walk are not substitutes. Use the explicit
nonedge witnesses to prune wrong projected transitions rather than trusting
source adjacency. Preserve the existing Klee--Minty/shadow warning.

This work does not claim that every carrier has a useful low-cost decomposition.
#244 retains the independent core-bridge/fibre route assembly, and #238/#241
retain their own source/compactness lines. Do not duplicate or resubmit them.
No workflow, pin, permissions, credential or secret-separation change was made.
