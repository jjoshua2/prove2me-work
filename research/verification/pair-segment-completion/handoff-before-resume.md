# PR #311: explicit pair-segment completion — first gate failed

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and LIVE heads,
comments and receipts before continuing. This turn started at main
24b519ae1e7907a0d063cd36731d435da9918765. The saved #310 repair was already
ACCEPTED/Proved and merged; it was NOT resubmitted. Other owned #244/#300/#302
and reserved #210 were not edited or triggered. This distinct completion work
was coordinated on #310 in comment5739226372 and read back.

## Authoritative state: OPEN/DRAFT, not accepted

Target: Hirsch.finite_hull_pair_segment_completion.
Packet: research/publication_packets/pair_segment_completion.
Branch: proof/pair-segment-completion.
Frozen failed proof:97581dffabdfd0a0553460e17df06875a705b575.
Actual NEW top-level command5739279584 and bot5739280398 were read back;
the acknowledgement resolved that SHA and run35420782170.

Gate105837948439 succeeded. Verify105837968753 failed driver compilation with
exit1. Publish105838188574 and report-verify105838188519 were skipped. The run
is completed/failure. There is NO registered theorem or submission ID, complete
passing audit, ACCEPTED verdict, live Proved or verified/publication artifact.
ALL FIVE requested axiom reports contain sorryAx from failed elaboration.
None is an independently passing theorem audit. No second trigger was posted.

The original273-line/11238-byte solution stays unchanged after the gate:
blobfbff4ac9cd9a0f066e316b04d67cb17bca11fb0b,
SHA256c62c84689cabd67695dacfaee9e9c79d3f8af5f1c979b774787c95ea4d136fef.
Original problem.json and explanation.md are unchanged too. Prepared-source
comparisons are not Lean verification. Local Lean/Lake was absent and compiler
host DNS failed; no local compilation or axiom audit is claimed.

## Actual compiler diagnostic groups and a separate proposal

1. The sum notation takes too short a body without explicit parentheses around
   additions. The second term escapes the e binder in point at line17 and in
   the combo/replacement sums. This also affects the explicit public target
   and its local Z at lines247/255. There were unknown-e and cascading goals.
2. Function.update_same and Function.update_noteq do not exist at this pin.
   The actual pinned TensorPower/Pairing.lean (blob18816895d34ceee2191e3d4b06cc2fb41362f4b6)
   uses Function.update_self and Function.update_of_ne in the same equality cases.
3. translate_hull must expose set membership before rewriting shift_combo:
   change (a • x+b • y)+q ∈ zonotope v.

The separate proposed-local-repair.patch addresses all three groups, with no
hosted retry. It is UNAPPLIED to the publication files and UNCOMPILED. The full
proposed files are in the local bundle; the patch applies/reverses byte-exact.
Source274 lines, SHA25647ac25515cdbff7270a285f9906399aca4aa63750d3de7315764c6887d454a8a,
blob9790db8a54ee6640c4e5d902c53b6b03e187d3d7. Proposed problem SHA256
bf6d1ca55dbb24d725299e9ed390d9659a8ed22e6abf921259733e1c9bc88e42.
Further errors may appear once the sum expressions elaborate correctly.

IMPORTANT: the proposal changes formal_statement BYTES as well as Lean source
because the public sum body itself needs grouping. Do not falsely claim an
already elaborated target type or a byte-identical public statement. The intended
mathematical formula, hypotheses, named target and n^2 slot count do not change.
No platform target was registered by this run, so no immutable live theorem is
being edited. Recheck live receipts before any future normal comment gate.

## Concrete written completion, not a supplied equality

For arbitrary n>0 real generators v_i in R^d, define P=conv{v_i},
Z=sum_(i,j)[v_i,v_j], and Q={q:q+v_i in Z for every i}. The candidate's intended
conclusion proves Z,Q compact/convex, Q nonempty and WHOLE-SET equality P+Q=Z.
The construction includes n=1,d=0, repeated/interior generators and rank-deficient
families; no genericity, full dimension, independence or summand oracle.

For any f choose k maximizing f(v_i). Select v_k on every ordered slot(k,i),
then maximize each other segment independently. Their sum z maximizes f on Z.
Changing just slot(k,i) to v_i produces z-v_k+v_i in Z. Thus q=z-v_k belongs
to every required translate and v_k+q attains Z's support inside P+Q. This
is an actual erosion witness, not just matching one inequality. Cube compactness
and explicit coefficient convexity give Z. Q is closed/convex and bounded by
one translate; the zero-objective witness makes it nonempty. Convexity extends
all generator translations to P. Strict separation of compact convex P+Q
then yields the reverse inclusion. See PAIR_SEGMENT_COMPLETION.md for the proof.
This written argument is not upgraded to Lean verification by the rational tests.

The n^2 count is the number of represented ordered segment slots, including
diagonals and duplicate directions, NOT an irredundant facet count or an optimal
completion. If n is a large vertex inventory of an H-polytope, no polynomial
original-row budget follows. A large count for this formula is not a lower bound
for all completions either. There is NO short genuine Z-edge route in this
packet; coefficient-cube edges are not assumed to project edge-for-edge.
Accepted #309/#310 transfers remain available but are not resubmitted. A useful
original-input budget and actual sum routing remain beyond this completion.
No unrestricted Polynomial Hirsch or historical-priority claim is made.

## Durable evidence and reproducibility

The sole request archive10577217846,308bytes was downloaded and hash-checked:
bdf820108f50381bd83c34d31b236c5fb4854afa994d7bbeb9e69ce60dbbbec6.
Its raw resolved.json is retained. No missing publication or verified archive
is invented. The full runner log was inspected; the committed diagnostics file
is explicitly SELECTED exact compiler/error/audit lines, not the entire log.
Original source and target snapshots, failed-run readback and proposed patch
are separate from derived test/source records.

Standalone Fraction-only script150 lines/7169bytes:
blobf8355ddbd033300c6670025c370374bcbe3b4c81,
SHA256be58ec91035a2b9415aea5e319267e2142824487e70030c19628758c20f73816.
46 complete planar completion models,1208 support witnesses,6627 replacements,
42189 coefficient checks. The759 Z and759 Q vertices are totals over models,
not a universal count. Nine selected instances reach d64 without full-body/graph
enumeration. Nineteen saved witnesses replay with construction disabled; four
forgeries are rejected. These tests are not a formally verified Python/JSON parser.

Clean script-only replay reproduces the full12437-byte report and33706-byte
fixture byte-for-byte:
report978578e2dd9cc9edee710aecd9a9ec86babc7661f5ed2ac995bde887670bdd5b;
fixtureefc7e10a8b59cd961323e85556ac6f5919c001d0c2f2d8c3a4f26ea2343ce625.
The full files and original archive accompany the bundle; repository summaries
are labelled derived and the full results regenerate with:

    python3 scripts/test_pair_segment_completion.py --out /tmp/pair-completion

No existing main proof, root STATUS, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.5 guard, workflow, allowlist,
duplicate safeguards or credential isolation was changed. Read live metadata
for the later evidence head, rather than confusing it with the failed proof SHA.
