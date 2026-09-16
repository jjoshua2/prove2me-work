# All-affine coordinate-level barrier: continuation handoff

## Scope, ownership and verification status

Baseline main `338d1f9e1cc20df86998efa5f0dc6e92916329e8`; branch
`research/affine-level-barrier`. Read current STATUS, all five project instruction
files and live PR comments again before continuing. Coordination comment
`5691688010` on #274 was actually posted/read back. #275 owns the distinct
all-affine ANGLE-conditioning and gain-cycle work; do not duplicate or trigger
it. #270's blocked companion, other active branches and reserved #210 are
unchanged by this contribution.

This is written research plus exact software. There is no new Lean source,
compilation, axiom audit, Actions verification, theorem registration, platform
submission or fresh authenticated root/leaf poll. Local Lean/Lake are absent.
Source tests and the classical-family derivation do not become Lean verification.
No existing code, pin, workflow, credentials or permissions were modified.

## Main mathematical result

For the standard triangular Klee--Minty cube Q_d(epsilon), 0<epsilon<1/2,
there are2^(d-1) PARALLEL original edges with distinct positive lengths. Prefix
last-coordinate values obey X_n=epsilon X_(n-1) union (1-epsilon X_(n-1)); the
two injective branches have disjoint ranges, so |X_n|=2^n for ALL real epsilon
in the interval. Final-bit edges have length1-2epsilon*x_(d-1).

If a real affine functional detects the common direction, its K levels provide
at most binom(K,2) positive differences. Hence K(K-1)>=2^d. EVERY invertible
affine chart has at least one such coordinate. The same applies to EVERY
finite-dimensional injective affine embedding, since its image of that
direction cannot vanish in all coordinates. Thus some coordinate has at least

    ceil((1+sqrt(1+2^(d+2)))/2)

levels, and sum of coordinate-level rank budgets is at least that number+d-2.
The obstruction already holds at fixed epsilon1/4 with2d genuine facets and
constant small coefficient magnitudes. It is not inferred from sampled charts.
No claim that this lower threshold is the exact optimal level count is made.

The TRUE graph diameter is d, by the classical cube adjacency classification.
Thus this rules out a universal polynomial GLOBAL coordinate-level certificate
obtained by affine preconditioning; it is not a graph-diameter lower bound or
counterexample to Polynomial Hirsch. Classical family/edge attribution is
Gaertner--Helbling--Ota--Takahashi arXiv1308.2495v1 Section4. No historical-priority
claim is made for the counting lemma or the cube routes.

## Explicit positive escape within the same family

The original-H constructor decodes the endpoint bit strings and flips each
differing bit once, constructing a shortest nonrevisiting original-edge path.
All common original facets are retained. Every point carries a full original
active-row inverse, and every edge a right inverse on d-1 common original rows.
All2d genuine facets have independently checked relative-interior anchors.
Dense affine charts and positive original-row rescalings are supported when
the chart and its exact inverse are supplied and bound to the actual H rows.
No hidden representation discovery or arbitrary projection is assumed.

After fixing the target's first i-1 facet choices, the actual remaining face
has only TWO levels in canonical coordinate i. The certificate records both
and verifies their exact binding. In a dense chart that objective is the row
of its inverse, not a claim of two levels in an arbitrary physical coordinate.
This gives a direct adaptive prefix-face path of at most d edges despite the
global exponential obstruction. Other shortest bit orders are accepted, but
the prefix interpretation belongs to the increasing-coordinate construction.

Projective maps, other combinatorial realizations, arbitrary extended
formulations with projection, nonlinear coordinates and adaptive face-specific
objectives are not ruled out. Do not conflate an injective affine embedding
with an arbitrary extension. The family itself can be diagonally balanced into
signed-root normals, so a good angle chart and a bad global level inventory
can coexist; #275's general gain recognizer is not reimplemented here.

## Executed exact checks

Seven complete original-H graphs (d1..4 with the listed epsilon values):194
active bases,58 vertices,97 edges. All324 tested endpoint pairs use552 edges,
match Hamming/reference distances, and pass #271's UNCHANGED arithmetic auditor.
Twenty-eight additional affine-chart cases in d2..8 pass both the new consumer
and the old original-edge checker. One rectangular5D-to7D embedding is checked.

Directly enumerated4,351 parallel edges in small dimensions have distinct
positive lengths. Deliberate half-collapse charts merge half the vertex values
but still leave2^(d-1)+1 levels in the relevant coordinate. These are adversarial
sanity checks, NOT optimization over all affine charts or a proof by sampling.

Actual large routes d16/32/64 use16/32/64 original edges, with32/64/128 facet
anchors, no shared endpoint facets and all target-prefix two-level records.
The universal lower level thresholds are257/65,537/4,294,967,297 respectively.
Large edge and level counts are PROVED FORMULAS, not full graph enumeration.
The d128/256 entries are formula-only; no large route is claimed there.

Twenty-four invalid records fail, including a coordinate annihilating the
parallel direction, wrong original H binding, singular/false inverse charts,
invalid epsilon, false rank products, prefix-face records and missing anchors.
Fourteen saved records replay with vertex, route, inverse, facet-anchor and
old elimination/search producers disabled, checking153 original edges.

A fresh three-source workspace reproduces ALL EIGHT reports and FOURTEEN full
fixtures BYTE-FOR-BYTE. No timing fields are excluded. SymPy is used only for
independent test references. The producer and consumer use exact standard-
library rational arithmetic. Python/parser correctness is not formalized.

## Exact source integrity and reproduction

New source blobs, read back and matched to tested local bytes:
- scripts/affine_level_barrier.py: b98625e40acebcf99488c8973f489ed72292b34a;
  SHA2567e2fb2df835130b438c8158a04cc69128cd95dc468bc74007d6a884faf5ab54b.
- scripts/test_affine_level_barrier.py: ee07201e2288c4133804722da672e31111518142;
  SHA256fb676a6c94c97f910dfbb337751fd3f81296e426bf0a6df5def0f5c81aa07389.

Unchanged dependency original_route_exclusion.py:
a764196e54970825823cad4575b947b507f95951. It is included in the standalone ZIP,
not added or overwritten by the research patch. The optimized sparse consumer
checks the same matrix identities; small/charted instances are cross-accepted
by the unchanged prior consumer.

Full proof: AFFINE_LEVEL_BARRIER.md. AFFINE_LEVEL_CHECK.json is an explicitly
derived compact summary. AFFINE_LEVEL_SOURCES.json and AFFINE_LEVEL_REPLAY.json
record exact source and full raw-record hashes. All raw reports and fixtures
are bundled and regenerate. The research contribution does not replace root
STATUS under other agents; its completion comment links this durable handoff.

    for s in small parallel charts large16 large32 large64 negative audit; do
      python3 scripts/test_affine_level_barrier.py --stage "$s" \
        --out "/tmp/$s.json" --fixtures /tmp/affine-level-fixtures
    done

## Next conjecture-facing step

Do not spend another continuation looking for a globally small affine
coordinate alphabet for all polytopes: the precise premise is false. Count
adaptive face-specific levels or route transitions instead, but derive their
bound from actual geometry rather than supplying it as an assumption. The
prefix-face comparator is a necessary easy test such a theory should handle.
It does not establish that arbitrary carriers have such a sequence. Existing
#267 total-refinement and #275 angle limitations remain separate, with their
own quantifiers and ownership. The unrestricted ordinary-edge polynomial
bound is still not proved by this contribution.
