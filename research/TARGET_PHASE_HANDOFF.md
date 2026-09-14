# Next continuation: quantitative phases, not another edge-validity theorem

Read live STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and open PRs.
This branch is research/code only. #250 already obtained an authenticated
ACCEPTED face-locking verdict; its owner retains that projected-image line.
#244 retains the separate supplied-core assembly. Neither is modified or
retriggered here. #241/#248 and earlier allocation interfaces stay accepted.

The new target_phase_pivot.py is for SIMPLE bounded ORIGINAL-H polytopes.
It does not replace the source-lineality/nonsimple-image code in #248/#250.
It locks every acquired target facet, builds a reciprocal-target-slack phase
objective, and permits an objective-decreasing step or complete two-edge block
when a new target facet is acquired. A phase ends at the FIRST acquisition.
A fixed improving objective controls fallback steps only. The tie-break uses
target-slack ratios, giving full affine equivariance and row-rescaling
invariance with fixed row labels. Original edge identities are checked; no
supplied graph, neighbor, or target objective is required.

Current evidence:614 original pairs plus600 additional pairs. Depth-two results
1230/1529 edge totals versus1228/1499 shortest totals and1258/1564 previous
baseline totals. Two original and27 additional routes are not shortest. Nine
pairs become worse than the prior baseline even though totals improve. Keep
those failures. The code verifies2506 local first-hit decisions; exploration
cost and route length are separate. The prior target_slack_pivot.py is an
unchanged transplant of the previous conversation bundle so the baseline can
be rerun from this repository.

The written note proves finite termination and affine equivariance, a family
where losing1/2 objective value gives a two-edge shortest route instead of
N+1 monotone edges, and a fixed-horizon family giving N+1 edges versus h+2
shortest. The latter is linear in ORIGINAL facets, not a Hirsch counterexample.
At depth2,N64 this is65 versus4 on69 facets. No finite lookahead or phase-count
argument alone closes the root. These written deductions are NOT Lean verified.

Run the two parts of test_target_phase_pivot.py. Its independent graphs and
BFS are reference-only; the producer uses local original-row certificates.
Fourteen bad/capped controls fail;24 audits run with discovery disabled.
One generated nonsimple model is explicitly outside scope, not a negative
claim about its geometry. The positive product tests reach dimension16 without
constructing its full graph. No new registration, audit gate or accepted
formal theorem belongs to this research branch.

Do not spend the next turn merely replaying these exact small examples or
claim that a successful selector benchmark proves a polynomial phase bound.
A useful next target is a global ORIGINAL-facet charging bound for constant-
face phases or a structural method that avoids them, tested against the
finite-horizon family and the preserved nonshortest examples. If trying a
larger-radius search, report O(d^h) neighborhood work separately; it is not a
polynomial algorithm merely because the displayed route is short.
