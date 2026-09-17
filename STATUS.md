# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`. Keep Lean `v4.30.0` and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Read AGENTS.md, CLOUD_AGENT.md,
SKILL.md, CONTINUE_HIRSCH.md, actual main and LIVE PR heads/comments before work.
Do not duplicate accepted or pending submissions.

This refresh records NEW FORMAL ACCEPTANCE #286. The previous COMPLETE frontier
is preserved verbatim in immutable history:
[pre-#286 STATUS](https://github.com/jjoshua2/prove2me-work/blob/fcc7f68febc372ccce3c8a8c4649638758c25374/STATUS.md),
blob `65e5a5e70f388e856946fa21d08ac3b7264d482d`.
Its archives retain #284/#281, earlier proofs, research, receipts and ownership.
Check live commits as well as this index; accepted work can precede a status update.

## Root and scope

The last preserved authenticated mission audit records root
`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` and high-dimensional common-face leaf
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e` Open. This is NOT a fresh platform poll.
The objective is still a uniform polynomial number of genuine ORIGINAL ordinary
edges for arbitrary carriers. Count original image facets, not smaller extension
rows. A new incompatibility theorem is not a universal route upper bound.

## NEW #286: explicit barycentric moment nonfaces ACCEPTED and merged

Theorem: `Hirsch.moment_curve_barycentric_nonfaces`.
Theorem ID: `e37928aa-132f-4b32-ba91-47b4a1f75fa4`.
Submission: `7fe04fd6-07d9-4ffc-83d0-bc44f67374a6`.
Trusted publisher: **ACCEPTED**, authenticated readback **Proved**.
Accepted proof: `5b44ad2795b85acb693e6e9f44039e9d9c425e85`.
Evidence-only head: `cfe1b3d419ee637f2a13ade550432742d044ba28`.
Merge: `84bafd3c2b39ed5b7a5c6a91e8599f6a3133a35b`.
Run: `35173820765`; verdict: `2026-09-17T02:20:20Z`
(September16 at22:20:20 America/New_York).

[Accepted proof and scope](research/publication_packets/moment_barycentric_nonfaces/accepted-evidence.md),
[raw publisher receipt](research/publication_packets/moment_barycentric_nonfaces/publication-receipt.json),
[raw compile/axiom audit](research/publication_packets/moment_barycentric_nonfaces/packet-audit.json).
The original source, target, explanation, frozen manifest, full driver log,
source-hash readbacks and first-failure history are preserved. Earlier pending
metadata is historical and superseded by acceptance. Do not resubmit.

### Exact formal content

For ANY injective real parameter map a on m labels, dimension d and selected
s with |s|>=d+2, construct

    w_i = inverse(product_{j in s minus {i}}(a_i-a_j)),
    row_i(x) = sum_{j=1}^d (a_i^j-average_l a_l^j)*x_j.

The theorem proves every selected w_i is nonzero and

    sum_{i in s} w_i*a_i^r=0, 0<=r<=d.

For EVERY feasible x satisfying ALL original inequalities row_i(x)<=1, it
finds a strictly slack negative-weight selected row AND a strictly slack
positive-weight selected row. Neither sign side can all be tight. The weight
sign classes are nonempty by the x=0 instance.

The original mean remains over all m labels, not only s. No dependence/rank
certificate, optimizer, interior point, sign-order hypothesis or support witness
is supplied. Lagrange's highest coefficient derives the exact annihilation;
root uniqueness and finite zero-sum signs force positive values on both signs;
the actual slack polynomial is nonzero because its full-label average is1.
The valid d0 case is included. The public target uses explicit let formulas,
with import/open-only preamble and no separately assumed custom definitions.

This is the complementary exclusion mechanism to #285's accepted small-face
witnesses. It does NOT newly formalize ordered parity signs for every odd-label
family, the minimal-nonface catalogue/cardinality, geometric realization or
assembly with #281. Classical interpolation is credited, not claimed as new
historical mathematics. No new original-edge bound or Polynomial Hirsch proof.

### Actual comment/compile/submission history

First224-line candidate, run35173425528: one coefficient-lambda rewrite failed.
Publication was skipped and no theorem registration/submission occurred.
The sole proof correction inserted `dsimp only at hc` before the existing
finite-sum coefficient rewrite. All theorem types/hypotheses, problem.json,
explanation and other proof bodies are unchanged. Original source, selected
actual diagnostic and one-line diff remain under research/verification/moment-barycentric/.

Corrected225-line proof, driver and target all compile with exit0. All FIVE
transitive proof reports contain only propext, Classical.choice and Quot.sound.
Harmless deprecated-push_neg and unused-ring warnings remain in the raw log.
No proof admission or target import is present. Its first ACTUAL platform
submission was accepted; the first compiler attempt is not described as passing.
Local Lean/Lake was unavailable: this is pinned hosted verification, not exact
Python relabeled compilation.

Both real requests were NEW top-level comments on the open same-repository PR:

    /prove2me publish research/publication_packets/moment_barycentric_nonfaces

Initial comment5707380638; corrected comment5707435094; verdict5707465522.
No dispatch, workflow, token, permission, toolchain or secret-split change.
Accepted source SHA256:
`5f5799763c8754777e3b227865a4eb7faf1c4670cfc697288c37dec09f5b3ace`.

Both original verification/publication ZIPs and both resolved-request ZIPs were
downloaded and independently hashed. All FIVE frozen hashes were recomputed;
solution/problem/explanation match the corrected source bytes. Raw aggregate
receipt and driver/audit/manifest files are preserved unchanged; derived local
records are labeled. Proved is the trusted publisher's authenticated readback,
not an additional direct API query. No missing raw API responses are invented.

Nine post-verification evidence/replay additions change ZERO accepted proof or
target bytes. All21 PR files are additions; no earlier repository source changes.
Rational tests:1125 cases,6577 moment equations,11261 original-row checks,8647
inverse weights,76 small odd-set applications,354 proper-face checks,selected
large cases through dimension64. Nine invalid controls fail;15 audits run with
witness generators disabled. Clean corrected report and fixture reproduce
byte-for-byte. Python/JSON and the sampled sign application are not Lean proofs.

    python3 scripts/test_moment_barycentric_packet.py

## Existing accepted work: reuse, do not restart

During this continuation the LIVE #285 comments already showed ACCEPTED for
`Hirsch.moment_curve_exact_small_face_witnesses`, theorem
d8214487-c5aa-446b-8e75-f485979b94f3, submission
bd1595ff-d987-4a5b-8f0c-017dec561971, run35167030696. Its accepted proof head is
c8589a1fee999c8497ebd2d1e6e9601ce739ec8b. The packet/owner's integration was
not edited, merged or retriggered here; read its own current state and receipts.
It gives original-H feasible points making exactly each small selected set tight.

#281's `Hirsch.stellar_persistence_count` remains ACCEPTED:
5d525d51-5d42-4dac-a3dd-91ea83902e77 /2807f578-7ed5-4be8-aa4a-4bc036ac3101.
It proves q+t<=choose(m+t,2) for actual finite forward stellar sequences. It does
not by itself formalize the separate large moment-family incompatibilities.

#284's `Hirsch.protected_facet_state_count` remains ACCEPTED:
37330e52-f970-45f1-9d48-d53617ec7c9a /e7971398-7465-4b52-b8bc-8bd07fd31f4a.
It proves the finite protected-interval signature counts, including an arbitrary
finite allowed-signature registry. It does not supply geometric intervals,
a small registry or original adjacency for arbitrary carriers. The complete
statement and first-attempt verification history remain in the previous index.

#267's written obstruction concerns exponential total COMPLETE forward-stellar
flagification, not long original paths or paths inside huge implicit refinements.
Earlier positive class refinements and accepted allocation/Minkowski interfaces
remain valid. #268 direct budget search, #271 checked finite exclusions, #269
coordinate-simplex routes and #272 cut-direction covers retain their stated
hypotheses. Finite search success or a polynomial formula size is not a universal
sufficient polynomial budget. Read newer live formalizations before adjacent work.

## Next substantive interface and ownership

The small-face feasibility theorem and the constructed sign-side incompatibility
mechanism are now both accepted. The next FORMAL application on this line is to
identify the odd/even sign partition, assemble minimality, and count the finite
family before reusing #281. Do not claim those steps from numerical examples.
This would formalize an obstruction to one strategy, not solve Polynomial Hirsch.
A general solution still needs a uniform original-edge UPPER bound, perhaps via
path-local protected signatures or a different valid global construction.
Do not assume a small exceptional parameter, cheap repair or universal small
full refinement as an unproved premise.

#282 triangular original-edge work and #270's deliberately partial draft remain
separate. Do not bypass blocked companion integration. #264 energy, #255 shortening,
#250 projected-image integration, #244 fibre assembly and #238 support witnesses
retain their owners. #208 needs its existing approved poll, not a resubmission;
#210 stays retired/reserved. No other owned branch or accepted/pending proof
was changed by #286.

Keep written mathematics, exact software, Lean compilation, axiom audit,
ACCEPTED and authenticated Proved distinct. Preserve toolchain and trusted
publisher isolation; a final publication gate is not a speculative edit/compile
loop. Read actual heads and receipts before selecting the next obligation.
