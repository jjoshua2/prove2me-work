# Continue from the polytopal budget plateau and counted macros

Read the LIVE STATUS and exact open heads before choosing work. This is research
and exact software, not a Lean/Prove2Me theorem. During pre-merge review #262 had
already merged the shared shielding criterion, full one-step budget and cyclic
distance-two schedule. The final #263 implementation IMPORTS its source unchanged:
  stellar_defect_budget.py, blob b51e2c3edec2c85026344566978561eb430050ec.
No second production accounting engine or priority claim is retained. Five
existing dependencies are byte-identical; all three stages were rerun after
reconciliation. The earlier independent source is historical, not final.

DISTINCT RESULT: an actual rational5D/10-facet polytope with36 vertices reaches
a state where NO individual stellar edge subdivision decreases W=sum_high(|N|-2).
The exact #262 budget policy on the original input chooses01,56,08 and returns
stalled at W3,n13. Its three remaining high defects are234,278,457. Every
productive edge gives W3 or4; an edge inside no high defect cannot remove any.
A fresh unchanged #262 call on the residual returns stalled with0 steps. This
is stronger than merely a shielding/twin stall, but does not assert all greedy
choices from the original input must hit this state.

The new macro takes one arbitrary edge and then shielded moves, accepting a
sequence of at most ell ONLY when its final W strictly decreases. All original
nonfaces, intermediate updates and checkpoint weights are audited. Hence total
t<=ell*(W0-Wres). If flag is reached, original diameter<=m-d+t; otherwise the
old explicit residual-block cost remains. A neutral edge34 crosses the actual
plateau via3->3->2->0. The full six-move refinement has M16 and bound11, versus
old#261's M266. #262's incomplete output is called stalled, not that fallback.
No universal ell3 completion, small initial W, cheap residual or runtime bound.

The cyclic first stage is shared with #262. The DISTINCT two-half completion
gives T_n<=C(floor(n/2),2)+C(ceil(n/2),2)-n+6 instead of n(n-3)/2. The all-size
proof is in MIXED_DEFECT_ABSORPTION.md. Repeated geometric wedges and safe clone
compression give original bound m-4+T_n with d=4+m-n. This is a cheap refinement
class, not a newly discovered polynomial-diameter class: the ordinary wedge
graph already increases diameter by at most one over its fixed4D base.
Distinguish the smaller greedy n7/n8 counts4/6 from the explicit schedule5/8.

Reproduce in separate calls when the runtime has short timeouts:
  python3 scripts/test_mixed_defect_absorption.py --stage abstract
  python3 scripts/test_mixed_defect_absorption.py --stage geometry
  python3 scripts/test_mixed_defect_absorption.py --stage family

All original-H routes are checked through carrier maps at every subdivision,
then original inverse/maximal-edge identities. Common original facets survive.
Generic complete minimal-nonface discovery may enumerate all original vertices
and be exponential. The verifier replays finite classification and BFS, but no
geometric LP, inverse or planner search. Python/JSON is not formally verified.

Actual post-reconciliation suite:324 abstract complexes,3189 exact updates,
1013 shielded moves,546 unequal-incidence cases,10550 carrier adjacencies.
Geometry:58 pairs,123 original edges vs129 old#261 and122 shortest; one
nonshortest and one original reentry remain. Six full audits disable geometric
production and planner selection;13 malformed types fail. The test explicitly
runs unchanged #262's full budget on all six inputs and preserves its packets.

Family:11 cycle sizes n6..16;9 wedge instances up to dimension20. Only one
10D/12-facet wedge additionally gets full final-H graph/nonface reconstruction.
Other larger models use exact wedge construction plus actual original edges;
they are not generic full-LP or full-graph tests. Full detailed reports and
certificates regenerate and are bundled. The clean replay has two new scripts,
an integer fixture and FIVE frozen dependencies; every nontiming result/hash
and both complete generated fixtures agree byte-for-byte.

The shared result belongs to #262. The new plateau is polytopal, unlike its
separate abstract budget stall. No existing owner branch, accepted result,
pin, workflow or secret is changed. No Actions or publication gate is needed.

LITERATURE GUARD: arXiv1303.5885 is withdrawn for a mistake in the main proof,
despite the strong surviving abstract. Do not import its missing-face-size
bound. The classical normal-flag theorem from arXiv1303.3598 is the short-path
input. The unresolved task is controlled successful refinements for arbitrary
polytopal spheres, or another original-edge argument; bounded checkpoints
escape this specific plateau, not every possible obstruction.
