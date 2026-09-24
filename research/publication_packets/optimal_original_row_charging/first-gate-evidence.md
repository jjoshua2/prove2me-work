# PR343 first gate: necessary counting clean; complete Hall assembly failed

Target: Hirsch.optimal_original_row_edge_charging.
Tested proof: 0df4d0d81d317c9858876aad5308f3c3dc952d6b.
Main at gate: b59bda5572a09cdfba2ebac74a6cb275281136c7.
Source: 345 lines / 14453 bytes, blob4e68e6ea665e5e57002fa7fd0808cef4c8c4601d,
SHA256796e8df8257a7643ea80f7983b5787dfbb3fe449087447a6dd812367dcc6bf37.
PR343 is OPEN/DRAFT and unmerged. No post-gate packet-input edits.

## Actual outcome

New top-level request5813901345, acknowledgement5813905359 and run35998089588
were read back. Gate107627746296 succeeded; verifier107627828683 failed driver
compilation with eight displayed diagnostics. Separate standalone solution and
exact target statement were not reached. Publish107628256923 and
report-verify107628257669 skipped. One hosted attempt, zero registrations or
actual proof submissions. No IDs, verified artifact, receipt, ACCEPTED or Proved.

Inherited exposed_edge_row and new forced_le have standard-only reports:
propext, Classical.choice, Quot.sound. capacity_iff, optimum and public solution
retain failed-elaboration sorryAx. No admission was written. A clean necessary
counting lemma does not establish the complete equivalence or optimum theorem.

## Repair areas and exact saved proposal

1. At204, Finset.card_product expects product notation. Add the pinned
   Finset.product_eq_sprod rewrite before card_product.
2. At277, the guessed eq_empty_iff_forall_not_mem constant is absent. Use the
   already available not_nonempty_iff_eq_empty and destruct a nonempty witness.
   The no-goals diagnostic at278 is a cascade.
3. At329/336/337/338/339, the public explicit Classical filters differ from the
   automatically synthesized decision procedures, and duplicated let bindings
   do not supply the expected definitional equalities. Introduce the ACTUAL
   four public let bindings with intro I S F Cap, establish membership and set
   equalities extensionally, and transport the load/Capacity expressions by
   those equalities instead of rfl. The public theorem TYPE stays identical;
   this part changes its proof body, not just an internal helper.

The pinned Mathlib product_eq_sprod declaration and Lean4.30.0's introN handling
of letE were read directly before preparing this proposal. That is API inspection,
not compilation. The saved patch adds28 lines and removes17. Complete proposed
source:356 lines/14566 bytes, computed blob1344d0a53a5dd6b45d5c08583a1a9b856dbb382d,
SHA2561f062f05c02f14cd713d64e3cfa467758b4d85f2bd7fd4e9e8be21acb569bdb9.
It is UNAPPLIED to the publication source and UNCOMPILED. Patch apply/check/reverse
passes. All declaration statements, accepted helper bodies, problem.json and
explanation.md are unchanged. Further errors may appear. No second gate was posted.

Patch: research/verification/optimal-original-row-charging/first-attempt/
proposed-local-repair.patch. Full uncompiled proposal is in the downloadable
export, not a second publication packet. Resume this same PR after live checks.

## Mathematical progress and exact limit

The complete written argument derives the lowest possible maximal ORIGINAL-row
load for a given finite original exposed-edge family. Every eligible supporting
row is derived from actual target slack and endpoint tightness. Capacity k is
characterized by every row subset J having at most k*|J| forced occurrences,
where an occurrence is forced if ALL its eligible rows lie in J. Classical Hall
supplies sufficiency. Minimal feasible K yields a matching upper assignment and
a nonempty overloaded J for every k<K. No small-capacity premise is supplied.

The original edge family, target and endpoint extremality and genuine nondegenerate
exposed segments remain inputs. Repeated occurrences are allowed. The finite
H-body may be unbounded and dimension is arbitrary. This is not a route constructor,
uniform polynomial congestion bound or Polynomial Hirsch solution. A terminal
target-incident edge is not chargeable in this positive-slack scheme. The next
geometric obligation is controlling forced-row density along a chosen route,
not merely selecting better labels on an arbitrarily long walk.

## Actual executable tests

The NEW standalone charging script was successfully uploaded as blob
725f23c4ab8d9a3e8c0b3b4b68bcbba03733ca12; its supporting commit records it as
scripts/test_optimal_row_charging.py. It is not the previously blocked radial-
envelope script and contains no dependency on that script. No blocked action
was retried or rerouted.

Exhaustive finite tests cover2928 eligible-set families and22968 assignments.
Both brute assignment and all-subset density agree with the flow optimum.
Geometric tests cover67 ledgers/1269 original-edge occurrences, with843 original
H square systems checked in eight small models. Nine malformed controls fail.
All four complete output files reproduce byte-for-byte in a clean single-script
workspace. The consumer checks assignments and overloads without calling flow.
Python, JSON and the exact-geometry implementation are not kernel-verified.

On the fixed64D short cube walk, least-row greedy load63 becomes optimal load1.
The8D Gray detour still forces load32 over254 preterminal edges, although its
endpoints are adjacent. Seventeen repeated copies of one edge force load9 with
two available rows. These adverse cases are retained: relabeling cannot turn a
bad supplied route into a polynomial route argument. No full64D graph enumeration.

Only request artifact10806004749 exists:316 bytes, SHA256
460c61231c8164672216a6947990adfe277fd3fbb45208dfe03138edac6c6012.
It was downloaded/rehashed and resolved.json preserved. The complete decoded
verifier log was read through cleanup; the stored error transcript preserves
all eight displayed errors/contexts and five reports, omitting timestamps,
the push_neg deprecation warning and setup/cleanup. It is not a full raw archive.
No unavailable verified/publication artifact or platform API body was invented.
Local compiler/cache absence and failed toolchain DNS are recorded separately.
Keep the Lean4.30.0/Mathlib pin, strict0.10.9 and all publication safeguards.
