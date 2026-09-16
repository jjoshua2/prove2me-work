# ACCEPTED: positive protected-facet visited-state count

Public theorem: `Hirsch.protected_facet_state_count`.
Theorem ID: `37330e52-f970-45f1-9d48-d53617ec7c9a`.
Submission ID: `e7971398-7465-4b52-b8bc-8bd07fd31f4a`.
Trusted publisher status: **ACCEPTED**, authenticated readback **Proved**.
Accepted proof head: `bf3db81677d9ec5e0e668bb39d558c789ec5e704`.
Run: `35163537520`.
PR: https://github.com/jjoshua2/prove2me-work/pull/284
Trigger comment: 5706196719; bot verdict comment: 5706237170.
Verdict timestamp: 2026-09-16T23:48:43Z.
Source SHA256: `6ea99bbb05ef86b965cbc558cfc744c05503a16effb7e704832c04f8de965739`.

## Formal result and its hypotheses

For an injective sequence of n distinct d-element subsets P(i) of a finite
original-label set V, suppose every label outside an exception set B has
interval membership. Then

    n <= (|V|-d+1)*2^|B|.

For ANY finite registry C covering the exceptional signatures P(i) intersect B,
the theorem also proves

    n <= (|V|-d+1)*|C|,
    n <= sum_{S in C} (|V minus B| - (d-|S|) + 1).

Natural-number subtraction is truncated. The proof includes empty sequences,
zero dimension, empty exception sets and irrelevant exception labels outside V.
It derives the injective encoding by (current exceptional signature, number of
previously seen protected labels no longer active). No bounded number of visits
per signature, global vertex count, or desired route-length inequality is an
assumption. The weighted conclusion is part of the SAME accepted theorem.

For a supplied nonempty loop-free simple-polytope route, n=L+1 gives the intended
conditional original-edge count. This packet does NOT prove adjacency, geometric
protected-interval existence, loop erasure or small exceptional signatures for
arbitrary carriers. It is the positive finite counting core of research #259,
not the entire geometric class theorem or Polynomial Hirsch. Accepted #281's
separate lower-count theorem was not resubmitted or changed.

## First compile and first submission succeeded unchanged

The original220-line candidate compiled at its first gate. Driver, solution and
statement all exited0. All FIVE audited declarations use only propext,
Classical.choice and Quot.sound. One harmless unused-simp-argument warning is
preserved; no proof edit or linter suppression was made. The actual solution
contains no proof admissions or extra axioms. The statement file's expected
target placeholder is not imported by the solution.

Exactly ONE new top-level publication comment was issued:

    /prove2me publish research/publication_packets/protected_facet_state_count

The normal same-repository workflow resolved the exact SHA, compiled without
Prove2Me secrets, froze the files and published through trusted main. No workflow,
pin, permission, credential, dispatch or secret-handling change was used.
Local Lean/Lake was unavailable; the compilation evidence is the pinned hosted
gate, not the independent Python tests. First actual platform submission was
accepted. No duplicate registration/resubmission was requested.

## Original artifacts and independent readback

Verified ZIP artifact10473897822 SHA256:
a445641f107c988b180194db38ca3702232e1804138caa27a9fdd7bca6b01dc6.
Publication ZIP artifact10473823512 SHA256:
0983485dd6afc3c8f5145235a8f6aba0a10bc881128f14b8956c23dce988a4f9.
Resolved request artifact10473359472 SHA256:
8b25bb5ab3d6aecbdfe6c6d94d0ca43fa9209fbc7ecdc92ed46493b175f64d40.

All three original archives were downloaded and independently hashed. Every
one of the five frozen file hashes was recomputed, and solution/problem/
explanation match the original prepared packet byte-for-byte. The raw audit,
verified manifest and aggregate publication receipt are copied unchanged.
Derived readbacks are explicitly labeled. The full driver/solution logs remain
in the original verification archive included in the delivered bundle.

Proved is the trusted publisher's authenticated observation, not another direct
Prove2Me query by this chat. The publication ZIP contains the aggregate receipt
and rendered bot comment, not individual raw API response objects. No missing
response is fabricated. Earlier prepared/compile-only metadata is historical
and superseded by this accepted record. Do not resubmit the packet.

The independent finite regression and separate clean patch replay also pass:
9502 exhaustive valid cases,400 random exchange paths,5 boundary cases and5
rejected malformed assumptions. Both the report and worked-example bytes match
across clean runs. This supports interpretation, not formal verification of the
Python code or a geometric realization of those abstract paths. The algebraic
applications note is a written deduction, not a separately published theorem.

## Next interface

Reuse the accepted count as a final accounting lemma. The next substantive
geometric task is to construct original-edge routes with protected intervals
and a controlled allowed-signature registry, or prove that condition for an
existing concrete construction. Do not assume polynomial registry size for
arbitrary polytopes or call the finite counting theorem an unrestricted diameter
bound. Other agents' existing branches and accepted/pending proofs are unchanged.
