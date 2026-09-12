# Target-tight unique-vertex outer — Prove2Me publication receipt

Date: 2026-09-12.

## Platform verdict

- Theorem: `Hirsch.target_tight_outer_unique_vertex_zero_diameter`
- Theorem ID: `aa3abbb2-203b-41ab-86b6-f45ab734c57a`
- Status: **Proved**
- Proof submission ID: `9903527d-a915-4c03-9109-5142f582d801`
- Proof verdict: **ACCEPTED**
- Prove2Me platform version: `0.10.3`
- Mathlib revision: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Mission: `The Polynomial Hirsch Conjecture`, mission ID `6078cb2d-3594-44b1-a01a-fd452ddae274`
- Mission comment ID: `77df1e11-80a5-43ed-9c7b-173d171f76af`

## Audited source and run

- Standalone theorem source commit: `36dd12b00cee1593dc2e88bff21b060f13a223b6`
- Git blob: `577a1131671cc6dcb98055209b398e65f9d65659`
- Actions publication run: `34675442900`
- Job: `103504370109`
- Artifact: `10291917813`, `target-tight-outer-publication-receipts`
- Artifact digest reported by GitHub: `sha256:d1dc385d49a4f5a3aa703360a60a3978439c050c6dd9daf89df346ca61e02636`
- Exact submitted `solution.lean` SHA-256: `90489f91783f912730fa2295d372f3fbcdf03c2dca66e2e4f66c15ad38e038d9`

The one-shot workflow generated the exact standalone server proof from the immutable source, built the public `Definitions.Def_Hirsch_model`, compiled and transitive-axiom-audited both the named theorem and wrapper before credential access, then authenticated and submitted the already-audited file.

The final Lean audit used only `propext`, `Classical.choice`, and `Quot.sound`. No private `Solutions/*` theorem imports are required by the public proof.

## Formal statement represented publicly

Every vertex `v` of a finite H-polyhedron has a subpresentation consisting exactly of the inequalities tight at `v`. In that relaxed outer, `v` is the unique vertex, and therefore the padded vertex-edge graph diameter is zero. The outer is allowed to be unbounded and may contain infinitely many nonvertex points; no boundedness, irredundancy, or full-dimensionality premise is used.

## Frontier integrity

Authenticated reads before and after publication both returned

- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
- theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
- status **Open**.

`frontier_graph_modified` was false and `new_conjectural_children` was zero. Thus publication did not alter or falsely close the remaining Polynomial-Hirsch frontier.

This theorem removes the old-vertex graph-cost term in the target-tight outer strategy. It does not imply that restoring omitted inequalities is free; the merged target-cone batch theorem handles that geometry conditionally on final parent-face route budgets, and bounding those budgets uniformly remains the main mathematical problem.
