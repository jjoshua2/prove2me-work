# Publication gate for the already-verified rank/weighted face-cover results

The user has explicitly assigned this agent formalization AND submission; this continuation completes publication rather than extending the research hierarchy. No new conjectural child or frontier dependency is introduced.

Proof source is frozen at `681314640b6f84792d8ae011c3534a6e8c456930`, verified by run `34532572816` (17 audited declarations, core axioms only). The builder reads the complete Solutions import closure from that commit, not from mutable main or another agent's work. It leaves only Mathlib and the existing public Hirsch model as imports. Four thin adapters expose all hypotheses through public types and set literals:

- `Hirsch.weighted_geodesic_face_cover_diameter_bound`.
- `Hirsch.tight_rows_outside_subspace_cardinality_bound`.
- `Hirsch.rank_selected_row_face_diameter_bound`.
- `Hirsch.weighted_cover_improvement_requires_smaller_child`.

The final gate compiles each exact public statement, compiles each standalone solution, audits its transitive axioms, and hashes all source and output bytes. Only after all four pass does it use the scoped repository Prove2Me credential. It runs the repository authentication preflight, checks environment/version, reuses exact matching registered theorems, skips already-Proved statements, polls every registration and verification, and records live statuses. A same-name different-type or different-environment theorem is rejected rather than overwritten. No key/token is printed, persisted, or included in an artifact; authenticated redirects are disabled.

The original source already passed Lean. Local syntax, eight offline submission guards, and the repository Actions-policy check passed for the publication code. There is no local Lean installation/network in this session, so this is a final publication/standalone-adapter gate using the cached pinned environment, not an interactive proof-edit compiler. It is triggered only by opening the explicitly named owner-authored same-repository publication PR or manual dispatch; never by ordinary pushes or synchronize events.

Until the authenticated receipts say otherwise these are NOT newly claimed platform-accepted theorems. The graph-routing conjecture remains separate. In particular the rank-selected statement makes no implicit claim of properness for arbitrary normal subspaces, and the counting barrier is not a lower bound on actual graph diameter.
