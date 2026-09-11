# Irredundant row-count publication receipt — 2026-09-10

Mission: **The Polynomial Hirsch Conjecture**  
Platform: Prove2Me **0.10.0**  
Lean: **4.30.0**  
Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Public theorem

`Hirsch.irredundant_rows_card_le_any_equivalent_presentation`

- theorem ID: `8538150b-8afe-47ad-94b0-d72189b80264`
- submission ID: `9194432c-54e2-4e6a-9aaf-d7c27fb9934e`
- verification verdict: **ACCEPTED**
- live theorem status after verification: **Proved**
- registration result: **PUBLISHED**

Formal content: if an `n`-row finite H-presentation is strictly feasible and
irredundant in the repository's row-deletion sense, then every equivalent
finite H-presentation has at least `n` rows. The comparison presentation may
use unrelated normals and may contain redundant rows, duplicates, or
zero-normal tautologies. Boundedness is not assumed.

The proof constructs, for each indispensable source row, a feasible point where
that source row alone is tight. A nonzero comparison row must be tight there.
Two different source rows cannot choose the same comparison row because their
midpoint is strict for every source row and therefore for every nonzero valid
inequality. This gives an injection from source rows to comparison rows.

## Frozen source / kernel gate

Frozen source commit:

`1ff86eb9c69679c6355c6fa968b6601482b046a1`

Source + standalone verification:

- GitHub Actions run: `34559027640`
- artifact: `10183697315`
- standalone source:
  `Solutions/Sol_Hirsch_irredundant_rows_card_le_any_equivalent_presentation.lean`
- standalone SHA-256:
  `33be3fdd17714bc1439b0bef73489c571ae41b14f5b06443c4ab6f85e905af55`
- `solution` axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`

The same gate compiled and audited the internal reusable developments:

- `HirschRowCount.irredundant_rows_card_le_any_equivalent_presentation`
- `HirschRowCount.equivalent_irredundant_row_counts_eq`
- `HirschRowCount.exists_globally_minimal_irredundant_subpresentation`
- `HirschCircuitLocalization.commonFace_minCount_eq_irredundant_subpresentation`
- `HirschCircuitLocalization.commonFace_minCount_eq_any_irredundant_presentation`

The exact rational regression suite also passed: 42 source models, 252 exactly
certified equivalent comparison presentations, 278 singleton-tight witnesses,
1,724 strict pair midpoints, and 2,582 nonzero tight blocker incidences.

## Authenticated publication gate

Successful publication run:

- GitHub Actions run: `34559453698`
- receipt artifact: `10183894675`
- artifact digest:
  `sha256:e2d5f54b586b267bb625f1d394f7028bb22debc68e8b34063008ab6830581f95`
- publication branch head:
  `91eb702c14ad3b6fff229caa360649acb35645f2`

Before exposing the repository secret, the publication workflow checked that no
`Solutions/`, `Definitions/`, or Lean-pin bytes differed from frozen source
commit `1ff86eb9c69679c6355c6fa968b6601482b046a1`, rechecked the exact standalone
SHA-256, compiled it under the pinned environment, and re-ran the axiom audit.
The credential was sent only to `https://prove2.me/api/v1`, with authenticated
redirects disabled.

The publisher collision-checked the theorem name/type, registered it, submitted
the exact audited `solution.lean`, polled the server, and required both
**ACCEPTED** and live **Proved** before succeeding.

## Mission linkage and frontier preservation

Polynomial Hirsch mission ID:

`6078cb2d-3594-44b1-a01a-fd452ddae274`

Mission discussion comment:

`33f2c225-aae0-458b-8c98-8575c4e453c5`

The comment links the public theorem and accepted solution and explicitly says
that this is a representation-semantics result, not an edge-routing theorem.

The publication transaction authenticated the formal frontier both before and
after publication:

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

- theorem ID: `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
- before: **Open**
- after: **Open**
- graph modified by this transaction: **false**
- new conjectural children: **0**

Therefore this publication is a reusable structural contribution to the
common-face row-count/defect program. It does **not** solve Polynomial Hirsch,
does **not** prove a graph-distance bound, and does **not** by itself identify
an abstract geometric facet type. The separate common-face adapter does prove
that the existing minimum original-row count equals the row count of any
equivalent strictly feasible irredundant coordinate presentation.
