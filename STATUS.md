# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`. Keep Lean `v4.30.0` and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Read AGENTS.md, CLOUD_AGENT.md,
SKILL.md, CONTINUE_HIRSCH.md, the actual main commit and LIVE PR heads/comments
before choosing work. Do not resubmit accepted or pending packets.

This refresh records a NEW FORMAL ACCEPTANCE, #281, rather than upgrading an
entire research direction to a proved conjecture. The immediately preceding
COMPLETE frontier is preserved verbatim in immutable Git history:
[pre-#281 STATUS](https://github.com/jjoshua2/prove2me-work/blob/66d6956e27daa877cd7e513a41af5c74eaba9e15/STATUS.md),
blob `154ad703f47011d72eff2e04c1363f91eb88e83c`.
It retains the full #268/#269/#271/#272 descriptions, cut-direction formulas,
older accepted-result archives, quantitative limitations, tests and ownership.
No older research result or receipt is discarded by this shorter index.

## Root and scope

The last preserved authenticated mission audit records root
`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` and remaining high-dimensional common-face
leaf `87a8b4f4-8b58-4340-8cb9-5fd1b548d01e` Open. This is NOT a new platform poll.
The objective is still a uniform polynomial ORIGINAL ordinary-edge bound for
arbitrary carriers, with genuine original image facets as the size parameter.
An auxiliary edge may project to a chord; an accepted counting lemma does not
establish the missing universal route bound.

## NEW #281: finite stellar persistence count is ACCEPTED and merged

Public theorem: `Hirsch.stellar_persistence_count`.
Theorem ID: `5d525d51-5d42-4dac-a3dd-91ea83902e77`.
Submission ID: `2807f578-7ed5-4be8-aa4a-4bc036ac3101`.
Trusted publisher verdict: **ACCEPTED**, authenticated readback **Proved**.
Accepted proof SHA: `97d58b7d247c4661e437058e2ca2be34c15e63d5`.
Final evidence head: `b9422a22e250956b274edc30205bfd8140a15088`.
Merge: `66d6956e27daa877cd7e513a41af5c74eaba9e15`.
Successful run: `35154778307`.
Verdict time: `2026-09-16T21:56:19Z`.

[Accepted packet and provenance](research/publication_packets/stellar_persistence_count/accepted-evidence.md),
[raw publication receipt](research/publication_packets/stellar_persistence_count/publication-receipt.json),
[raw compile/axiom audit](research/publication_packets/stellar_persistence_count/packet-audit.json).
The proof, target, explanation, frozen manifest, driver axiom output, failure
history and independently checked artifact hashes are preserved alongside them.

### Exact formal conclusion

For a finite sequence of t actual forward stellar subdivisions on finite
supported downward-closed face families, subdividing genuine faces of size at
least two and adding fresh labels, any certified finite initial subfamily A of
inclusion-minimal nonfaces satisfies

    |A| + t <= choose(|V(0)| + t, 2)

if every terminal minimal nonface has cardinality two. The public statement
includes the ACTUAL stellar face-membership rule. It does not assume persistence,
injectivity, cardinality growth or completeness of A. The proof derives canonical
minimal descendants, their injectivity, one additional born nonface each step,
an exact tracked family of size |A|+i, and the terminal pair count. Empty A and
t=0 are included. The public preamble is only `import Mathlib`.

This formalizes the finite combinatorial COUNTING CORE of research #267. It does
NOT formally verify the cyclic-polytope exponential family, geometric carrier
transport, original-edge constructions, or Polynomial Hirsch. Those boundaries
must remain explicit. Inverse moves and arbitrary non-stellar subdivisions are
outside this statement. Do not republish another copy of the accepted core.

### Actual verification and publication history

The initial295-line candidate reached pinned Lean in run35154274683 and failed
on ONE redundant successor rewrite at line255. Three substantive helpers compiled;
the final theorem did not. Publish was skipped and no platform registration or
submission was created. The error record is preserved, not hidden.

The correction removed only Nat.succ_eq_add_one from the rewrite list, since
the goal already used i+1. All theorem types, hypotheses, problem.json and the
explanation remained unchanged. The corrected295-line proof, driver and statement
all compiled with exit0. All FIVE audited declarations use only propext,
Classical.choice and Quot.sound. Its first actual platform submission was accepted.
The original candidate is not claimed to have passed unchanged on its first gate.

The user-requested NEW top-level PR comments launched the normal existing gate:

    /prove2me publish research/publication_packets/stellar_persistence_count

No dispatch, new workflow, token, permissions, toolchain or secret-split change.
The initial local runtime had no Lean executable; this is actual pinned hosted
compilation, not Python/source checks described as verification. Proved comes
from the authenticated trusted-publisher receipt, not a separate direct platform
poll by the chat. The raw publication ZIP contains an aggregate receipt and bot
comment, not individual raw platform API responses; none were fabricated.

Both original verification/publication ZIP digests and all five frozen file
hashes were independently recomputed. Source hash:
`2b579f45c887c6ccc44b1caaf2a0686c90c9634fd080cb4010af36da18f83959`.
The two post-verification commits add EIGHT evidence files and do not change
accepted proof bytes. All15 PR files are additions. The finite semantic/signature
regression also reproduces byte-for-byte in a clean directory; it is supporting
software, not a formally verified Python implementation.

## Preserved strategy limitations and next work

#267's written geometric example rules out a universal polynomial TOTAL SIZE
for full forward-stellar flagification. #281 now verifies its finite counting
core; it does not by itself formally instantiate the exponential moment-curve
family. The written obstruction does not refute short original routes, inverse
moves, other subdivisions or paths inside huge implicit refinements. Existing
class-specific positive refinements remain valid under their stated conditions.

Direct original-H budget search #268 and independently checked tangent-star
exclusions #271 remain available. A polynomial-size formula for an input budget
is not a proof that a polynomial budget always succeeds. Solver UNSAT and a
checked finite exclusion certificate are different evidence. The complete prior
index retains the known forced-reentry unbounded controls and bounded-cap caveat.

#269 supplies direct routes for supplied coordinate-simplex sums; #272 supplies
cut-stable direction-cover routes with exact overlap certificates. Their input
structure, direction counts and overlap hypotheses are not established for
arbitrary carriers. A bounding box does not silently produce bounded overlap,
and using the original polytope as its own base can require exponentially many
directions. Read their current proof packets and newer live commits; this index
is not a new audit of other agents' ongoing formalizations.

A next formal extension of #281 would supply the separate large minimal-nonface
family and connect its parameters to this accepted count. A conjecture solution
still needs a polynomial original-edge upper bound or another valid global
construction. Neither the accepted auxiliary theorem nor another experimental
suite supplies that missing unrestricted step.

## Ownership and execution discipline

#270 private-marker work is deliberately draft with only engine/handoff pushed;
its blocked companion integration must not be bypassed or merged as complete.
#264 energy, #255 shortening, #250 projected-image integration, #244 fibre
assembly and #238 support witnesses remain separately owned. #208 needs its
existing approved poll, not a duplicate submission; #210 is retired/reserved.
No other branch or accepted/pending submission was modified by #281.

Distinguish written arguments, exact Python, Lean compilation, axiom auditing,
ACCEPTED and authenticated Proved. Preserve pins and trusted-publisher isolation.
Use local compilation when available; a final hosted gate is not a speculative
proof-editing loop. Read live heads and receipts before resuming old obligations.
