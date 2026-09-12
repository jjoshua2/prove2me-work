# Target-slack uniform parent-face budget verification

Date: 2026-09-12.

Hosted verification passed on frozen head `00779ee7537f49293503875a1b52397af7b13253`.

- Actions run: `34676070853`
- Job: `103506050811`
- Artifact: `10291803631`
- Artifact digest: `sha256:08e76c3f4bc113aa9b21dfbe0ec76c7a5c1cc35fa5917a21538f2adebfb6dd41`
- Lean: `4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused gate compiled `Solutions.PolynomialTargetSlackUniformBudget` and transitive-axiom-audited:

- `HirschTargetDeletion.target_slack_rows_card_le_rowExcess`
- `HirschTargetDeletion.target_slack_batch_reinsertion_uniform_parent_face_bound`

Only the repository-allowed logical axioms `propext`, `Classical.choice`, and `Quot.sound` occur.

## Result

At a vertex of an `n`-row H-presentation in dimension `d`, at most `n-d` describing rows are strictly slack. Combining this with the verified target-cone batch reinsertion theorem gives the uniform-budget specialization:

- full padded graph diameter at most `2 + (n-d) * B`;
- target-rooted padded route length at most `1 + (n-d) * B`,

provided every final target-slack face has an ambient parent-edge route budget `B`. Replacement routes may leave their corresponding face.

The theorem deliberately does not supply `B`; it identifies the exact remaining multiplicative resource as row excess rather than raw row count. A naive same-excess lower-dimensional recursion for `B` can still grow faster than any fixed-degree polynomial, so weighted/global face amortization remains the frontier.

No Prove2Me mutation or credential access occurred in this verification.
