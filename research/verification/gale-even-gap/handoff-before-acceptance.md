# PR #307: selected-set even-gap route — first gate blocked

Read live STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and actual open
heads/comments before continuing. Starting main fcb4dae2a66cd420a181c5412e369ec4b0f744b8.
Coordination5736936505 on #302 was posted and read back. #300/#302 remain their
owners' work. Accepted #304/#306 and reserved #210 were not modified or retriggered.

## Last observed verification and publication state

Target: Hirsch.gale_even_gap_exchange_routes.
Packet: research/publication_packets/gale_even_gap_routes.
Exact tested proof: 055056470469fed116fcf64b0308ef2817d40634.
Actual NEW top-level conversation command5737018270; acknowledgement5737019581.
Run35402347556 completed with failure. Gate105784752243 succeeded;
verify105784785370 failed driver compilation with exit1. Publish105785121901
and report-verify105785121972 were skipped. There was NO theorem registration,
submission ID, ACCEPTED verdict, live Proved, verified packet or publication receipt.
Exactly one gate was triggered. No proof edit or further trigger followed it.

The full compiler log was inspected. One error is reported at line590, in the
last image equality of enumerate_complement. After the image_image rewrite the
goal is

    Finset.image (fun i => ↑(e i)) Finset.univ =
      Finset.image (Fin.val ∘ ⇑e) Finset.univ.

The rank_balance and even_gaps_iff_phase helpers print only propext,
Classical.choice and Quot.sound. enumerate_complement, selected_routes and the
public solution report sorryAx from FAILED elaboration. Do not call this a
passed packet or count the two helper reports as platform acceptance.

## Minimal proposal, not an already-verified repair

verification/gale-even-gap/proposed-local-repair.patch appends `rfl` immediately
after that rewrite, closing the displayed definitional function-composition
identity. It applies and reverses byte-for-byte against the exact tested source.
The proposed689-line source SHA256 is
5443bdf2da19e0d0ebbd69686e5488abbfb98fd20e01467b37de9ac50c1afd28.
The public statement AND assembly suffix, all definitions/assumptions/bounds,
accepted dependency and target metadata remain unchanged in this proposal.

The patch is NOT applied to the publication source, NOT Lean-compiled and NOT
submitted. Another error could appear after it is applied. Next action is full
local pinned compilation and the complete transitive audit, not a speculative
hosted edit/compile cycle. Local Lean/Lake and toolchain-host DNS were unavailable
in this session. Source comparisons and Python are not Lean verification.

## Actual mathematical progress and scope

Inputs are S,T : Finset (Fin m), cardinality d, and the literal selected-set
Gale predicate: between every two unselected labels, the selected gap count is
even. The target constructs <=2*(m-d)+1 nontrivial one-selected-label exchanges;
every intermediate set has size d and the SAME predicate. No increasing list,
parity phase, admissible schedule or bounded path is supplied.

The new rank identity partitions labels below the i-th hole into selected labels
and the i earlier holes: C_i+i=h_i. Selected prefix differences are the selected
gap counts, so even gaps are equivalent to indexed alternating parity in BOTH
directions. The empty complement case is included. These two core helper chains
emitted standard-only reports in the actual failed run.

Mathlib orderEmbOfFin enumerates the actual complement of size m-d. The accepted
#306 proof constructs its short natural-label route; exact encoding/decoding
and intersection/cardinality identities transfer to Fin m without modulo
wraparound. Reverse parity then establishes the gap predicate at each intermediate
selected set. Empty/full universes, d0, d=m and equal endpoints remain included.

The entire accepted #306 proof is reused unchanged except the standalone root
name (accepted_alternating_routes) and omitted old printouts. The accepted source
is382 lines with SHA256f92e3db7370b14aad8c27fe6648891742b4ed47f7c3def06ac9bb232878f472f;
all five old manifest hashes were recomputed. No prior accepted theorem is submitted
again. #302's still-unaccepted numerical/parity proof is NOT imported. This new
packet has688 lines/28836 bytes, blob225149d5193b8e46bada71b51b29d762df5cf849,
SHA256b09c648a87d714c517b9d33ca8378e0bc23e3a22831cd0b88c8bf07e13317117.

This is ORDER-ONLY and remains a candidate until full compilation/acceptance.
Its purpose is to bridge the literal selected-set #302 interface to accepted
#306 without assuming the missing enumeration/phase. The numerical catalogue
and all-original-vertex exposed-edge composition are separate tasks. No new
best classical bound, shortestness, target locking, score monotonicity, global
injectivity, nonrevisiting or arbitrary-carrier Polynomial Hirsch is asserted.

## Reproducibility and durable evidence

The actual request ZIP10570712987 is310 bytes, SHA256
48df3df0721b6250b8787ab3470ec96ca67e9e5b80efca2992df876c8fdd32a0.
It was downloaded, hashed, and its raw resolved.json checked against the exact
proof. The original archive, source snapshot, selected EXACT compiler excerpt,
labelled derived run readback and proposal are preserved. The excerpt is not
misrepresented as the whole runner log; no platform receipt is fabricated.

The new test imports the UNCHANGED scripts/test_alternating_complement_routes.py.
It independently checks literal gaps on2047 subsets,596 legal/1451 illegal,
9217 rank and18943 gap identities,13724 endpoint routes/77806 exchanges and91530
visited selected sets.6072 endpoint pairs have opposite phases.3651 walks repeat
vertices and11264 lose a target label; stronger properties are not claimed.
Three selected larger cases reach m257,d193 without full graph enumeration.
Sixty-nine saved records/463 exchanges replay with the packing producer disabled;
seven malformed endpoints or paths fail.

A clean two-source workspace reproduces the COMPLETE7089-byte report and437889-byte
fixture byte-for-byte. Full data accompany the export and regenerate. Report
SHA25684847b48a26a583b349f136e2900386cef69c791e8830d0aafb64f4383863cf1;
fixture941975b53160bdbeaedfab25cd9577949b8e48dabf35a8776636d4d0cd2f4aeb.
These tests are supporting finite arithmetic, not an all-size proof or formal
Python/JSON implementation. Run:

    python3 scripts/test_gale_even_gap_routes.py --out /tmp/gale-gap-check

Root STATUS and all pre-existing main files remain unchanged. Preserve the
committed Lean4.30.0/Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f pin,
strict0.10.5 platform guard, workflows, actor allowlist, duplicate checks and
trusted verify/publish credential separation. No fresh authenticated root/leaf
mission poll is claimed. Keep #307 open/draft with this concrete blocker.
