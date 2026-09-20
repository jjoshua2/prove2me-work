# PR #318: every compatible opposite-cube lift — ACCEPTED

Read the five project instruction files and live exact PR heads/comments before
continuing. Baseline main was ca97e0b2c26597ea55e069e4a26a0698bc6a9df8.
The live check found #316 and #317 already accepted; neither was resubmitted.
Coordination on #317 was comment5749988491, posted and read back. Reserved
#210 and other owned proof branches were not changed or triggered.

## Authoritative status and proof binding

Hirsch.cube_fibre_lift_exponential_barrier is ACCEPTED. The trusted publisher's
raw receipt records Proved. Theorem0ca69a92-2b6d-43ea-857c-0e684e8b7248,
submission4581df96-9ce6-4bdd-bb5e-5e974589db39.
Frozen proof fa8e95312f1a159ff5731e0ea2b7f228d5d8cfec;
run35513219311. NEW top-level request5750059036, resolved acknowledgement
5750060017 and authenticated verdict5750075010 were read back.

Gate106084679779, verify106084707014 and publish106084846191 completed
successfully; report-verify106084846913 was skipped. All three compiler modes
exit0; five transitive reports use only propext, Classical.choice and Quot.sound.
This is FIRST compiler gate and FIRST platform submission, exactly one trigger.
No proof repair, post-gate proof change, target change or additional trigger.

The774-line/31504-byte accepted source is blob
a1508b05e446aa9323554c521c53c9381b290dbd, SHA256
8ba3abdf0fdd055be52ea3e15fa4b8cfb583ad340ea1a086145efbafbbd29d25.
The540-line accepted #317 prefix through exists_change is byte-identical;
only its old antipodal theorem/root are omitted and the namespace is closed.
All five dependency hashes and all five new frozen hashes were recomputed.
Local Lean/Lake was absent and toolchain DNS failed; actual compilation is the
pinned hosted gate, not source inspection or Python tests.

## Exact new mathematical conclusion

Z is an original coefficient segment sum containing [0,1]^d+Q. Its generator
list contains the indicator of EVERY nonempty coordinate subset. For ANY q0,q1
in Q with q0 and1+q1 extreme in Z, EVERY feasible-point walk between those lifts
through nondegenerate whole exposed Z segments satisfies2^d<=L+1. Thus choosing
a better compatible lift pair cannot reduce the unweighted cost below2^d-1.
This is stronger than #317's existence of a globally distant antipodal pair.

No objective, coefficient saturation, Boolean injectivity, graph, direction-per-
edge assignment or route lower bound is supplied. A feasible forward generator
segment at an extreme point forces its coefficient to0 in EVERY representation:
otherwise setting the coefficient to0 supplies a backward feasible point and
midpoint extremality gives a contradiction. A reverse segment forces coefficient1.
Translated cube containment provides the needed segments for every Boolean
indicator at the two respective lifts. Distinct nonempty zero-one vectors are
nonparallel, proved coordinatewise. The accepted whole-edge changed-coordinate
lemma then makes the assignment of one changing step per nonempty subset
injective. Exact powerset cardinality gives the bound.

Cube containment, generator representation and actual extreme endpoint lifts
remain explicit structural hypotheses. Q need not be convex, closed or compact;
equality with the Minkowski sum is unnecessary. Compatible lift existence is
NOT asserted here. The label function is defined on all subsets (its empty value
is unused), so the presented generator index type must be nonempty even for d0.
The dimension-zero conclusion is trivial when those inputs exist. Unselected
zero/parallel/opposite generators are unrestricted.

## Canonical completion application and surviving route problem

The #311 all-ordered-cube-pair segment construction becomes Z with generators
b-a after a fixed translation. The pair0,b supplies every Boolean indicator.
The known cube-summand decomposition translates to cube+Q inside Z. This is a
written application of the established construction, NOT an additional Lean
translation/equality theorem in this packet. It shows the all-pairs inventory's
exponential unweighted problem persists for EVERY compatible lift above the
specified opposite original cube corners, not merely global worst endpoints.

The lower bound is on the enlarged Z, NOT the cube. The original cube has a
d-edge route, and many Z steps are stationary under contraction. A smaller
completion (the cube itself has d generators) is not obstructed. Polynomial
Hirsch is neither proved nor refuted. No historical-priority claim is made.

The unweighted best-lift escape for this rich completion is now CLOSED. Reuse
this result rather than reopening the same saturation/endpoint question. A
useful next quantitative argument must either avoid the rich generator
inventory or charge only genuine nonstationary original steps. Simply bounding
all enlarged edges, even after choosing the best lifts, cannot succeed here.
A bound on contracted steps has NOT been derived for arbitrary original inputs.

## Evidence, tests and reproduction

Raw packet audit/manifest, full compiler logs, driver/statement, request,
verified aggregate and publication receipt are preserved separately from derived
source/run/replay summaries. Three original ZIPs were downloaded and rehashed;
all five frozen files agree with the prepared source. Both job logs were read
through cleanup. Proved is publisher-authenticated readback, not a second direct
platform or mission-root poll. Individual API bodies and complete runner logs
not exported here are not invented or labelled as committed.

The standalone Fraction suite checks ALL99 compatible pairs over11 complete
planar models,502 original hull-edge occurrences and297 injective required-
direction assignments. There are205 additional events; actual cube-component
cost is198 versus304 collapsed steps. The canonical ordered square-pair model
has4 compatible pairs and distances3..4. Complete cube+Q hull equality is checked
in every small model, independently from route generation.

Selected Boolean-direction systems in dimensions1,3,4,5,6,8 have1,7,15,31,63,255
completion edges but1,3,4,5,6,8 cube-component edges. The d8 example has247
stationary contracted steps. No large graph is enumerated. Eighteen saved
records/424 edges audit with sweep construction disabled; five forgeries fail.
Full4443-byte report and901216-byte fixture reproduce byte-for-byte in a clean
single-script workspace. A combined command timed out during its second replay;
the separate clean replay completed successfully. Tests are not Lean-extracted
software, a universal parser theorem or extra formal results.

    python3 scripts/test_cube_lift_barrier.py --out /tmp/cube-lift-barrier

The full report and fixture are in the downloadable bundle and regenerate;
repository summary/hash records do not masquerade as the entire fixture.
Report SHA25696132e025c1bf3e3de858d5703f1373a9a81ce1f47366abc754e4e88feadaddd;
fixture SHA256c93a25d4117d85da63be60332c2f8d4b4cc96f99a925a02a8653dee049bd2689.

The committed Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f,
strict0.10.6 guard, workflows, allowlist, duplicate checks, secret isolation and
all pre-existing main files are unchanged. Live PR metadata supplies the later
evidence/merge SHA, distinct from the frozen proof above. Do not resubmit.
