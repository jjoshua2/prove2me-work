# PR #313: regular zonotope sweep — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
heads/comments before further work. This continuation resumed existing #313;
no duplicate proof packet was created. Other owned work and reserved #210 remain
untouched. The separate protocol maintenance was #314.

## Authoritative result — do not resubmit

Hirsch.zonotope_regular_sweep_original_edges is ACCEPTED, with authenticated
publisher readback Proved. Theorem 4713ca26-d458-47e6-9ae0-4654b0322f39;
submission b56d6fcd-3014-4068-8734-41611b8028ad.
Accepted proof 7dbeccc586323fb67ce565dec401306304bfeb9d;
run 35461651928. Actual new top-level trigger 5744394367, exact-SHA
acknowledgement 5744395232 and verdict 5744414337 were read back.
Gate/verify/publish completed successfully; report-verify skipped.

All three compile modes exit zero. All five transitive reports use only propext,
Classical.choice and Quot.sound. Read the packet's raw publication-receipt.json,
packet-audit.json, manifest and compiler logs, plus accepted-evidence.md and the
labelled verification/zonotope-sweep/resume-publication-readback.json.
Proved is the trusted publisher's authenticated readback, not another direct
platform or mission-root/leaf poll. Missing raw API bodies are not invented.
Local Lean/Lake was unavailable; actual compilation is the pinned hosted evidence.

## Unchanged proof and resolved protocol history

The first successful compiler gate was 35460242988 at proof
caf342b4679820b8e8b12633493884938536135d. Its publisher failed before registration
on protocol compatibility. Both original request and verified ZIPs, compiler logs,
scoped error and no-receipt bot comment remain. Old compile-evidence.md and
PROTOCOL_REFRESH_REQUIRED.md describe that historical state. The old handoff and
manifest are copied verbatim to handoff-before-acceptance.md and
manifest-before-resume.json; this receipt supersedes their current-status labels.

Maintenance #314 reviewed official version-only upstream release
32b755663224d6c3f572406e893e9b10ca652202, synchronized SKILL to 0.10.6 and changed
only the runtime expected version literal. Exact mismatch rejection stayed intact.
Ten offline actual-method tests passed without network or real credentials.
Merge 51d0be383b4eca6a8709a9017dc9230278f71367 was the trusted main used by the
successful new gate. API-host/redirect restrictions, actor allowlist, duplicate
checks, workflows, secret separation and Lean/Mathlib pin were unchanged.
Source review was by the working agent, not an independent human approval.

There were TWO successful compiler gates and ONE actual platform submission,
with exactly ONE new trigger this continuation. No proof edit or mathematical
strengthening was made. The 726-line / 30146-byte source remains blob
097c1df64a2eea944613a4a62eb63edbe9d5ccea, SHA256
3d233db7a1ce78a9376a758af92ce71634f9a0a45887d48384b99dfbc30153f4.
All definitions, hypotheses, public root, accepted prefix, problem.json and
explanation.md are unchanged. No further submission is needed for this target.

## Closed sweep construction

Let Z=sum_i[0,w_i]. Given f,g regular on all nonzero generators, construct k
with the same generator signs and entire target face as g. The straight sweep
h_t=(1-t)f+t*k has an EXACT finite set T of interior nonzero-generator ties,
with |T|<=m. Every event exposes a whole nondegenerate ORIGINAL exposed/extreme
edge with actual extreme endpoints. Every other t in [0,1] exposes one vertex.

Include generators and contrasts f(w_i)w_j-f(w_j)w_i in a finite test set.
Finite-subspace avoidance supplies a functional nonzero on its nonzero vectors;
finite margins make a small sign-preserving perturbation of g. Simultaneous ties
force contrast evaluations to vanish, so the contrast vectors vanish. Regularity
of f then gives collinearity. Parallel/opposite ties remain allowed. Every crossing
comes from the explicit ratio f(w_i)/(f(w_i)-k(w_i)); the image/filter proof
establishes both directions and the count. Accepted #312 gives whole original
edges, and coefficient saturation gives singleton faces and target-face equality.
Its complete 425-line prefix is unchanged; no accepted dependency was resubmitted.

## Remaining route and original-input complexity obligations

The sweep/event-face obligation is CLOSED, now also on the platform. Do not
create a child that merely assumes or repeats the same perturbation/edge result.
Still required for an all-pairs zonotope route: sort T, prove constant chamber
vertices on its complementary intervals, identify the two adjacent chamber
vertices with each event edge's endpoints, and assemble the bounded walk.
Regular exposing objectives for arbitrary specified actual vertices must also
be derived. Those are not conclusions of this packet or of the Python examples.

The parameter m counts generators, not original H facets. Even a generator-linear
zonotope route needs a controlled generator budget for the #311 completion to
imply an original-input polynomial bound. No such budget or unrestricted
Polynomial Hirsch result is supplied here. Do not replace original complexity
by an exponentially expanded list. No shortestness, new best classical diameter
bound or historical-priority claim is made.

## Reproduction and raw evidence

Five original packet ZIPs were hash-checked and are in the export; raw extracted
files are committed separately from derived run summaries. The old dependency
ZIP is retained too. Both new job logs were inspected through cleanup, without
claiming complete runner logs or individual API responses were committed.
All five frozen file hashes agree between the first and new verified archives.

The unchanged Fraction suite reran: 165 sweeps, 125 crossings, 46 parallel-tie
events, 39 zero generators, 9462 Boolean representations, 369 whole-face and
19832 singleton-support checks. Selected d8/16/32/64 systems do not enumerate
full graphs; 34 construction-disabled saved audits and four forgeries remain.
The complete report (1791 bytes) and fixture (38439 bytes) match prior bytes:
390664da822e557169ffa0de181b509962c55114a757112da5e7ea79949fe670;
fef9b004e1b0593b968311f9732e5d607f97a98c0e2000dab99567b62b72e4eb.
These are supporting checks, not Lean-extracted Python/JSON or an all-pairs proof.

    python3 scripts/test_zonotope_sweep.py --out /tmp/zonotope-sweep

Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f remains pinned.
Use live PR metadata for the later evidence and merge SHAs; they differ from
the accepted proof and trusted workflow SHAs above.
