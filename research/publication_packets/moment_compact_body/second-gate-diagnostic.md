# Second compiler gate: coefficient fixes passed; incidental convexity edit reverted

Actual run35209173536, verify job105162300327, compiled proof
9767da92ed853f1522d89eddc925fe8e302d8fbe under the unchanged pinned environment.
At2026-09-17T10:12:35Z, all four audited helper results (coeff_slack,
coordinate_bound, compact_feasible, zero_interior) printed ONLY propext,
Classical.choice and Quot.sound. The two diagnosed coefficient repairs worked.

The root solution still failed because the incidental two-step spelling of the
convexity estimate used add_le_add_left in the wrong argument orientation.
The actual diagnostic at driver.lean548 was:

```
add_le_add_left (mul_le_mul_of_nonneg_left (hy i) hs) ...
has type s * row a y i + ... <= s * 1 + ...
but was expected to have type r * 1 + s * row a y i <= r * 1 + s * 1.
```

This was an assistant-introduced proof-spelling error, not a mathematical gap
or a changed hypothesis. The final correction RESTORES EXACTLY the original
first-gate convex_feasible proof, which had no diagnostic in that run:

```
add_le_add (mul_le_mul_of_nonneg_left (hx i) hr)
  (mul_le_mul_of_nonneg_left (hy i) hs)
```

No new tactic or proof design is tried for that lemma. The final source differs
from the original prepared packet ONLY by the two diagnosed coefficient
simplification repairs. All theorem signatures, hypotheses, accepted dependency
bodies, problem.json and explanation.md remain unchanged from the first gate.
Final600-line source SHA256:
8b23e18ad0830ed6cfb668f4ee397ad19f443d11919c89b7c58cfab64fb8eb47.
Git blob:102c497a564229c64f1f083f85dfe48268004c89.

Publish was SKIPPED on both failed runs. Neither run registered or submitted
a platform theorem. The second failed root audit's sorryAx is Lean's recovery
from the type error, not a source proof admission or a verified conclusion.
The partial helper audit is not an acceptance of the full public theorem.

This record is derived from actual decoded workflow logs. It does not claim
that the full raw run log or a successful verified artifact was produced by
a failed run. The second resolved-request artifact is10491377604, with actual
archive digest bfca84c3c83dc6ff193eb0a7dbb801bb9923ce087f374b76e865c3f4f6e11016.
The final requested gate rechecks the complete statement and proof together.
No workflow, pin, permission, credentials or secret split is changed.
