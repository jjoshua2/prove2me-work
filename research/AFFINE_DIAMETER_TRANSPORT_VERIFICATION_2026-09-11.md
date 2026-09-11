# Injective affine transport: verified 2026-09-11

## Evidence

- Frozen source commit: `be54654435d3c317d676f3ea03c79d07f089992a`.
- Source file: `Solutions/PolynomialAffineDiameterTransport.lean`.
- Source Git blob: `ada90a58fe876f5e0b31ec20a0f8c22b1c408dd1`.
- Lean: `v4.30.0`; Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Successful verification run: `34611873550`; job: `103304108860`.
- Artifact: `10268937391`, `affine-diameter-transport-verification`.
- Artifact digest: `sha256:4e030dd2893d88e17d3e34d39b050768661558a3c87e6a96a0138e670e94968e`.
- `lake build Solutions.PolynomialAffineDiameterTransport`, direct Lean execution, and the required eight-declaration axiom audit all succeeded.
- Permitted axioms only: `propext`, `Classical.choice`, `Quot.sound`.

The preceding run `34609870682` failed in the final injective-map diameter pullback. The repair replaces endpoint rewrites beneath unreduced lambda applications with explicit equality composition, and explicitly selects the adjacency branch before rewriting pulled-back endpoints. No theorem statement or assumption was weakened.

## Audited declarations

1. `Hirsch.affineEquiv_isExtreme_image`
2. `Hirsch.affineEquiv_image_extremePoints`
3. `Hirsch.affineEquiv_adj_iff`
4. `Hirsch.affineEquiv_diamLE_image_iff`
5. `Hirsch.affineMap_isExtreme_image_iff_of_injective`
6. `Hirsch.affineMap_image_extremePoints_of_injective`
7. `Hirsch.affineMap_adj_iff_of_injective`
8. `Hirsch.affineMap_diamLE_image_iff_of_injective`

The last four do not require surjectivity onto the target ambient space. For any real modules E,F, injective affine map f, set P, and natural bound B:

`DiamLE (f '' P) B ↔ DiamLE P B`.

This is the form needed by dimension-changing slack-coordinate embeddings. It preserves and reflects genuine extreme points and segment-face adjacency, rather than merely mapping paths between arbitrary feasible points. It applies to arbitrary subsets, without extra boundedness, convexity, nonemptiness, finite-dimensionality, or positive-B assumptions. In particular B=0 and empty/no-vertex cases are covered.

The backward proof uses a total left inverse of f; on actual edge steps, both endpoints belong to the affine image by the definition of adjacency, so their pullbacks are justified. Stay steps transport by equality. Values of a padded walk after B are irrelevant.

## Scope

This closes the graph-semantics transport part of the excess-two program. It does not construct the slack normalization or infer that every circuit carrier has row excess at most two. The separate required geometric input is an injective affine slack map whose feasible image is a normalized two-moment slice.

The concrete next interface remains: a bounded strictly feasible h-dimensional H-presentation with at most h+2 rows admits the relevant slack-coordinate normalization, hence has graph diameter at most two. Combine that with the existing common-face coordinate and row-count-invariance results to obtain the M_min ≤ h+2 carrier base case.

No Prove2Me acceptance is established by this CI receipt alone; a separate authenticated publication receipt is required.

## Runtime note

The preexisting public compiler cache was downloaded in seven connector-sized parts from run `34607315868`. Container/Python execution subsequently returned transport timeouts while mounting the large attachments, including for trivial commands. Local restoration, archive hash checks, and local Lean compilation were not confirmed. The isolated repair above therefore used one final run of the existing verification workflow; this was not a successful local build. Do not report the local cache as installed until `lean --version` actually runs.
