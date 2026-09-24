# PR343: optimal original-row charging — first gate failed

Read live main, current instructions, PR comments and ownership before resuming.
Continue this SAME target, not accepted #341/#340 or reserved #210. Respect
#326, #282 and every other active claim. No further gate was posted after failure.

Branch: proof/optimal-original-row-charging.
Packet: research/publication_packets/optimal_original_row_charging.
Target: Hirsch.optimal_original_row_edge_charging.
Tested proof:0df4d0d81d317c9858876aad5308f3c3dc952d6b.
Source345 lines/14453 bytes, blob4e68e6ea665e5e57002fa7fd0808cef4c8c4601d,
SHA256796e8df8257a7643ea80f7983b5787dfbb3fe449087447a6dd812367dcc6bf37.
Coordination5813719775; request5813901345; acknowledgement5813905359;
run35998089588. Later evidence commits do not change the tested proof identity.

## Verification state

Gate107627746296 success; verify107627828683 driver failure. Standalone solution
and exact statement not reached. Publish107628256923/report107628257669 skipped.
One hosted attempt; zero registrations/submissions, no IDs/receipt/ACCEPTED/Proved.
Inherited exposed_edge_row and new forced_le have standard-only reports.
capacity_iff, optimum and solution retain failed-elaboration sorryAx. No admission
was written. The full theorem is NOT verified.

## Exact repair and next action

Use first-attempt/proposed-local-repair.patch. It repairs three areas:
- Product notation at204 via Finset.product_eq_sprod before card_product.
- Absent empty-set lemma at277 via not_nonempty_iff_eq_empty;278 is a cascade.
- Public binding/filter conversions at329/336/337/338/339: introduce the actual
  four public let definitions with intro I S F Cap; prove membership, forced-set
  and load/Capacity conversions extensionally instead of assuming rfl.

Proposal356 lines/14566 bytes, computed blob1344d0a53a5dd6b45d5c08583a1a9b856dbb382d,
SHA2561f062f05c02f14cd713d64e3cfa467758b4d85f2bd7fd4e9e8be21acb569bdb9.
The patch adds28 lines/removes17. All declaration statements, accepted helpers,
public TYPE and metadata are unchanged; the public proof body is changed.
This is UNAPPLIED to publication input and UNCOMPILED. Apply/reverse and exact
statement checks pass, not Lean. Further errors may appear. After current live
checks, apply exactly, compile locally where possible and use one complete
prepared gate. Do not rename or weaken the theorem. Current publication source
must remain the preserved failed input until that deliberate repair step.

## Mathematical scope

The written proof combines actual original-edge supporting labels with classical
capacitated Hall. It derives an optimal maximal row load and a nonempty forced-row
overload certificate for every smaller capacity. No favorable load bound is a
premise. BUT the edge family is input, possibly repeated, not a constructed route.
No polynomial load bound or Polynomial Hirsch result is concluded. The meaningful
next route obligation is to bound forced-row bottleneck density along a selected
ordinary-edge route; a large arbitrary walk can remain unavoidably overloaded.

## Reproduction and stored evidence

    python3 scripts/test_optimal_row_charging.py --out /tmp/charging-small
    python3 scripts/test_optimal_row_charging.py --large --out /tmp/charging-large

The new standalone script is committed, not a retry of the blocked radial-envelope
script. Exhaustive2928 set families/22968 assignments agree;67 geometric ledgers
contain1269 edge occurrences, including nonsimple/unbounded cases and selected64D
short walks. All four complete outputs repeat byte-for-byte;9 controls fail.
The original64D route's greedy63 becomes1, while a bad8D Gray detour still forces32
despite adjacent endpoints. Python/JSON and geometry checks are not kernel-verified.

Packet first-gate-evidence.md and research/verification/optimal-original-row-charging/
retain exact tested inputs, diagnostics, original resolved request, proposal and
labelled source/dependency/test records. The downloadable export includes the
original request ZIP, full proposed source and all four full outputs. Only artifact
10806004749 exists (316 bytes,SHA256460c61231c8164672216a6947990adfe277fd3fbb45208dfe03138edac6c6012).
No raw verified/publisher receipt exists. Diagnostic excerpts are not full raw
runner archives. Local Lean/cache not found; toolchain DNS failed. Keep pins,
strict reviewed0.10.9, accepted sources and secret separation unchanged.
