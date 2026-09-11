# Injective affine diameter transport: Prove2Me publication receipt

Verified transaction completed 2026-09-11 at 14:57:19.999140 UTC.

## Public result

- Theorem: `Hirsch.injective_affine_image_diameter_iff`.
- Theorem ID: `c4b0c852-981b-4bd7-8578-07e72315c3c9`.
- Submission ID: `d0300dfb-691d-4388-8d4d-878c28b9cddf`.
- Registration: **PUBLISHED**.
- Authenticated proof verdict: **ACCEPTED**.
- Authenticated final theorem status: **Proved**.
- Prove2Me version: **0.10.1**.
- Lean: **4.30.0**.
- Mathlib revision: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

For real modules E,F, an injective affine map f:E→F, any subset P of E, and any natural B, the theorem states

```lean
Hirsch.DiamLE (f '' P) B ↔ Hirsch.DiamLE P B
```

The published statement quantifies `E F : Type`; the internal source is universe-polymorphic. No surjectivity onto F, equal ambient dimension, convexity, boundedness, finite dimensionality, nonemptiness, or positive B is assumed. The graph uses genuine extreme points and adjacency defined by a distinct-endpoint extreme segment.

## Verification provenance

- Source file: `Solutions/PolynomialAffineDiameterTransport.lean`.
- Frozen source commit: `be54654435d3c317d676f3ea03c79d07f089992a`.
- Frozen source Git blob: `ada90a58fe876f5e0b31ec20a0f8c22b1c408dd1`.
- Source compilation / eight-declaration axiom audit run: `34611873550`.
- Source verification job: `103304108860`.
- Source verification artifact: `10268937391`.
- Source artifact digest: `sha256:4e030dd2893d88e17d3e34d39b050768661558a3c87e6a96a0138e670e94968e`.
- Exact standalone solution SHA-256: `3036e68ec71afc54cf927b4daf40062a26eb62fee9b8b1891b8ccd5b6f403032`.

Publication and independent standalone gate:

- Workflow run: `34612388187`.
- Job: `103305832568`.
- Publication branch head: `277ee4112f24aeda32b31096497a8edb0d0cce9d`.
- Publication artifact: `10268884785`, `affine-diameter-publication-receipts`.
- Artifact digest: `sha256:f0f960e369dd4041716d11ff3b7c76c9ed8ff7b9d3e986f935232e8d7a241c05`.
- Artifact size: 20,177 bytes; archive contains 18 proof, manifest, log, and receipt files.

Before credentials were exposed, this run checked the frozen source, regenerated the standalone file, compiled it, and audited `solution`. All nine printed axiom reports (eight source declarations plus solution) used only `propext`, `Classical.choice`, and `Quot.sound`. The subsequent authenticated preflight confirmed DNS, health, API-key refresh, and environment access. The publisher checked theorem-name/type collisions, submitted the exact audited proof, and required ACCEPTED plus live Proved.

The standalone builder and publisher are preserved in `scripts/publish_affine_diameter_transport.py`. The client is loaded from immutable commit `1692538ba9f7661ca079a86f2963fb48ac2270d1`, blob `7da71d03920b59b688bae7cc8b4f9c15432adc4a`, with theorem-specific metadata and exact version guard 0.10.1. No credentials are included in the source or receipt.

## Mission linkage and scope

- Mission: The Polynomial Hirsch Conjecture.
- Mission ID: `6078cb2d-3594-44b1-a01a-fd452ddae274`.
- Mission reference comment: `77e5b93c-2e87-4444-aded-11d6e75f15ae`.
- Both theorem and accepted-solution references were resolved in the comment.

The authenticated transaction read
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) as **Open** before and after publication. The publisher made no frontier-graph modification and created no conjectural children.

This finishes the dimension-changing graph-transport tool needed by slack-coordinate normalization. It does not construct the positive slack weights or prove an arbitrary carrier is a rank-two moment slice. The separate derivation in `research/EXCESS_TWO_SLACK_NORMALIZATION_BRIDGE_2026-09-11.md` is a mathematical handoff, not a Lean-verified normalization theorem. The concurrent branch `formal/slack-two-moment-normalization` should reuse the repaired transport source rather than the earlier incomplete pullback.

## Runtime provenance

The PR90 publication conversation could not confirm local Lean execution because its container and Python calls returned transport timeouts. The source and standalone verifications above are GitHub-hosted, followed by authenticated Prove2Me verification. Separately, PR89's owning normalization workspace reports a successfully installed and hash-verified local compiler; PR89 is closed unmerged. These are distinct workspaces and should not be conflated.
