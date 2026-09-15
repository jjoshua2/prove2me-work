# Continue from weighted retirement, not another polygon selector

Read live STATUS, the open PR queue and #253 before choosing work. The initial
STATUS snapshot named #252; checking the actual base commit revealed newer
merged #253. This turn withheld its duplicate complete-polygon implementation.
The committed new work only analyzes/tests #253's EXACT unchanged selector.
The earlier independent duplicate's numerical comparisons are not mislabeled
as #253 trajectories and are not proposed for main.

New files: three_dimensional_face_accounting.py, test_weighted_face_retirement.py,
the mathematical note, executed JSON, source manifest and this handoff.
Dependencies already on main and unchanged:
- two_face_acquisition.py: Git blob aa562f02dd492ecc47479381d637c6292757ebd3;
- simple_tangent_policy_audit.py: Git blob73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976.

## Actual mathematical progress

For the #253 route with at most three missing target facets, charge each distinct
chosen fallback polygon its own q-1 cost. In a retained simple three-face the
selected facets have no target-facet neighbors. Its induced dual graph on at
most e=m-d non-target facets is planar. This proves

    L <= 6e-12+2 floor((e+2)/2), r=3;
    L <= floor((e+2)/2), r=2; L<=r for r<=1.

No route-existence or short-phase premise is added. The unchanged algorithm's
whole-face maximum/retirement property is essential: a weaker one-pivot fallback
does NOT automatically inherit this argument. The general bound replaces the
old quadratic final-tail term but still has higher-dimensional binomial terms.
This is an algorithm-specific written proof, not a new classical diameter result.

The explicit rational stacked-polar family has m original facets, dimension3,
all polygon sizes<=6, no shared source/target facet and forces at least
ceil((m-8)/3) whole fallback MACROS before acquisition. Label span proves the
bound for all m, not by extrapolating numerical experiments. Together with
#253's upper charge, the fallback order is Theta(m); that does not contradict
Polynomial Hirsch. The m32 actual route has23 edges versus20 shortest, so the
code is not quietly labeled optimal.

## What was executed and what was not

Five corridor models and808 ordered pairs on four independent small graphs,
plus embedded intrinsic-three-face tests in dimensions4/8/16. Two corridor
models get an independent all-active-subset reconstruction; larger ones use the
exact complete stacking transcript. Every original edge and all weighted
retirement data are checked. Nine search-disabled audits and seven negative
controls pass. Generic large-dimensional graph enumeration is not claimed.

Run python3 scripts/test_weighted_face_retirement.py. The JSON and worked fixture
regenerate. The fixture is bundled, not needed as a trusted producer input.
Python is not Lean-extracted; no new Lean declaration, axiom audit or platform
submission exists for this contribution. Do not trigger a publication workflow
merely to give research-code tests a green check. Keep pins and security unchanged.

#250 retains general projected-face locking, #244 the core/fibre assembly,
and #238 support-witness existence. None is modified or retriggered here.
Next work must bound weighted retired faces in intrinsic dimension>=4, or give
a different global original-edge argument. Planarity is unavailable there;
calling the unchanged binomial sum polynomial would be incorrect.
