# Mixed stellar-defect continuation handoff

Base: `13fd398df7dc224deccef4cd2c1506069ed042a3`.
Coordination: #261 comment5685784251. This work is research/code, not Lean.
The new scripts do not overwrite or monkeypatch the previous compressor.

## Reproduce

    python3 -m py_compile scripts/stellar_defect_budget.py scripts/test_stellar_defect_budget.py
    python3 scripts/test_stellar_defect_budget.py --stage algebra
    python3 scripts/test_stellar_defect_budget.py --stage geometry
    python3 scripts/test_stellar_defect_budget.py --stage family
    python3 scripts/test_stellar_defect_budget.py --stage negative
    python3 scripts/test_stellar_defect_budget.py --stage assemble

Only unchanged dependency: scripts/simple_tangent_policy_audit.py, blob
73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976. Bundled for standalone execution, not
added or modified in the incremental patch. No external Python packages are
required; exact rational arithmetic is from the standard library.

The production CLI takes a COMPLETE complex {vertices,minimal_nonfaces} and
returns a trace. --policy twins, shielded, or budget selects the restriction.
--certificate expects the INNER trace object, not the result wrapper. Full
original-H classification is not implemented in this new CLI. Partial caps or
local stalls never imply nonexistence of other flag refinements or long diameter.

## Exact proof interfaces

For a FACE edge E with fresh z, the new z-nonfaces are z union the minimal
residues N minus E of old nonfaces meeting E. The no-new-higher iff test requires
a blocker for EVERY one-sided higher nonface: either an old missing pair or
old common higher defect with its residue contained in the candidate residue.
Identical endpoint incidence is sufficient but no longer required.

W=sum_higher(|N|-2) obeys W'=W-c+D EXACTLY, c=#old higher containing E and
D=weight of new higher descendants not inherited from common defects. Common
descendants cannot be suppressed by other residues, by old antichain minimality.
Permitted budget steps have D<c; t<=W0-Wt. Do not call mere membership of E in
one high defect a decrease proof: C(7,4), E03 has W7->8.

When the completed subdivision is flag, normality of a polytopal sphere
and the classical Adiprasito--Benedetti theorem give M-d. Every edge stellar
carrier, including splitting moves, maps refined adjacent facets to equal or
adjacent original ones. Compatible lifts retain common original facets. The
reference path finder enumerates the entire refined graph; it is NOT a hidden
polynomial-cost general path constructor.

## Positive results and sharp qualifications

The greedy shielded rule resolves C(7,4)/C(8,4) in4/6 steps versus zero available
twin moves. A DIFFERENT explicit two-phase cyclic4D schedule has t<=n(n-3)/2
for every n>=6. It first eliminates triples containing a distance-two cycle
pair; thereafter every productive original pair is shielded. Its recorded
counts5/8 at n7/8 are not the greedy4/6 counts. No best-known low-dimensional
diameter improvement is claimed. The family schedule is tested through n20.

A rational six-dimensional simple polar with14 facets has57 higher defects,
W97, and no shielded move. Starting from C(10,6), its dual is four actual edge
stellar subdivisions, in the exact order36,27,03,58, with fresh labels
10,11,12,13. The budget rule completes in29 moves, ten with births: total
consumed114, new weight17, terminal0. Its M43 gives a sufficient original bound37.
Do not count the four INPUT-defining subdivisions as new refinement work.

The abstract six-label local budget stall in the negative suite is NONPURE,
not a polytopal counterexample. There is no proof here that a descending budget
move always exists for polytopal states. W0 itself need not be polynomial in m,d.

## Executed evidence

1,120 abstract complexes;11,501 exact stellar updates;880,128 whole-face checks.
Seven original rational polars;397 route pairs;881 refined and866 original edges;
15 stationary carriers. True original distances sum843, with22 nonshortest
routes. Original/refined full graphs ARE enumerated in this test stage. Family
nonface schedules avoid that graph enumeration but do receive the known class.
Seventeen negative/capped controls; sample original audits pass with inverse
discovery disabled. The candidate-count field in a trace is diagnostic metadata,
not a verified complexity certificate; proof verification checks the actual
set identities and every strict weight decrease.

The next task is controlled cost/existence for mixed refinements beyond these
classes, NOT a claim that a conditional e+W0 bound proves Polynomial Hirsch.
No new Lean skeleton, CI job, packet registration or platform verdict is included.
