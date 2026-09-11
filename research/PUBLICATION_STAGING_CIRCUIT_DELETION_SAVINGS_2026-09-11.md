# Publication staging only

This branch exists only to trigger the owner-only Prove2Me publication gate for
the already integrated and hosted-verified theorem
`Hirsch.row_circuit_selected_excess_defect_savings_identity`.

Do not merge this marker. The branch is based on current `main` so the gate uses
the current frozen standalone publisher and workflow. After an authenticated
ACCEPTED/live-Proved receipt is durable, close this PR unmerged and remove the
temporary publication workflow from `main`.