# PR #306: alternating complements, constructive 2r+1 exchange routes

## Actual current result: compiler-blocked draft

Target Hirsch.alternating_complement_exchange_routes.
Packet research/publication_packets/alternating_complement_routes.
Prepared proof48bf4e31182dbd6c17bd31d9414814682804bad8, based on main
ec1f9940496d8cb0ed9308ede632d0ec3b62de67. The first and only NEW top-level
publication comment5736389668 was posted/read back; bot5736391459 resolved
that exact SHA and run35396849974. Gate105767547472 succeeded; verification
job105767601862 FAILED with exit1. Publish105767831839 and report-verify
105767831860 were skipped. No platform registration, submission, ACCEPTED
verdict, live Proved readback, verified packet or publication receipt exists
from this run. Keep this PR OPEN/DRAFT until its full proof actually verifies.

The 378-line publication source remains UNCHANGED after the gate. Its blob is
f1496d3605dc61caf85d5465176544dc00f5e125; SHA256
0df8004b9262f6052d8d991a7dfa129e7f96bf1cd4408da9be54f673ad737fe1.
All three original packet blob identities match the prepared local files.
Local Lean/Lake was unavailable and compiler-host DNS failed. Supporting
arithmetic and patch application checks are NOT Lean compilation.

## Exact diagnostics and an unsubmitted proposal

Three root sites were reported, with many parser cascades:

1. Line53: omega treats the two constructed Fin-value projections as unrelated
   arithmetic atoms. The proposed correction explicitly changes the comparison
   to n<n+1 and supplies Nat.lt_succ_self.
2. Line58: prefix is a reserved Lean syntax keyword. Its declaration and all
   uses fail parsing. The proposal renames this INTERNAL helper to packedPrefix.
3. Line203: dsimp only at hi made no progress because the expression was already
   reduced. The proposal supplies an explicitly typed natural equality before omega.

The one_coordinate helper printed only propext, Classical.choice and Quot.sound.
The OTHER FOUR final printouts include sorryAx due to failed elaboration, so
there is no complete theorem audit. Parser failure means later route steps have
not all been checked; correcting these sites may expose further diagnostics.

verification/alternating-complement/proposed-local-repair.patch applies and
reverses byte-for-byte against the frozen source. It has NOT been applied to the
publication source, NOT compiled, and NOT submitted. Proposed source SHA256:
f92e3db7370b14aad8c27fe6648891742b4ed47f7c3def06ac9bb232878f472f.
The full public theorem statement AND assembly suffix remain byte-identical;
only the private helper identifier and two diagnosed reductions change.
The full proposed source accompanies the export, not a claim of verification.
No second hosted trigger was issued. The next compiler work belongs in the
committed local/cloud Lean environment, not a speculative Actions edit loop.

The original request ZIP10567942442 has316 bytes and SHA256
3db4d46656ac1884484b06f063c1d5d0fc7ac2d645d872134e583b1954e35cd1.
Downloaded bytes were checked and resolved.json was read. This is the only run
artifact. Selected exact compiler excerpts are explicitly labelled, not passed
off as a complete runner log. Derived run-readback.json is not a raw verdict.

## Concrete positive mathematical construction

The written proof is an order-only theorem about r unselected labels (holes)
h_0<...<h_(r-1) in {0,...,m-1}, with alternating indexed parity. Either starting
parity b=0 or1 is allowed, independently for source and target.

Strict order and parity give h_i>=b+i. Left-pack by replacing h_i with b+i,
one index at a time, starting from the left. Each intermediate configuration
is strictly increasing, remains in the universe and keeps indexed parity.
A stage changes one label or stays still, so each endpoint packs in at most r
exchanges. The two phase anchors {0,...,r-1} and {1,...,r} differ by ONE label.
Concatenate packing, the anchor crossing and reversed target packing, then
remove stationary steps by finite induction. This CONSTRUCTS a complete walk
with at most2r+1 nontrivial single-label exchanges; no path is a premise.

Complementing every configuration gives m-r selected labels. A hole exchange
has union size r+1, so the selected complements have intersection size m-r-1
and are distinct. Those cardinalities and every intermediate legal enumeration
are explicit in the public target. r0, r=m, m0 and equal endpoints are covered.
There is no claim of shortestness, no-reentry, target locking, or score monotonicity.

## Geometric connection and remaining obligation

For a sorted root set, between holes h_i<h_j the number of selected roots is
h_j-h_i-(j-i). Evenness of all such gaps is therefore alternating indexed parity.
The classical Gale-evenness/numerical-to-geometric equivalence is the separately
owned #302 packet. The written composition with accepted #299 reconstruction
and #295 original-edge geometry would use r=m-d and give the class bound
2(m-d)+1 for actual moment vertices. Input enumeration, parity transport and
original-space route assembly are NOT formally supplied by this packet.
No arbitrary-carrier Polynomial Hirsch result follows, and classical cyclic-
polytope diameter bounds are sharper (Maksimenko2009, DOI10.1515/DMA.2009.003).
This is a project interface, not a historical-first or best-bound claim.

Do not replace the alternating-endpoint hypothesis by a short supplied path,
or declare the geometric composition done because arithmetic examples pass.
Once this source compiles, the exact next integration is to transport the FULL
parity catalogue, including both phases/normalization signs, through the accepted
original vertex/edge interfaces. Respect #300/#302 ownership when assembling it.

## Executed regression and its limitations

All13724 ordered endpoint pairs across66 small models were constructed and
checked:596 configurations,77806 edge occurrences, versus30480 independent
shortest-edge occurrences.12593 walks are nonshortest,3651 repeat a vertex and
11264 lose an acquired target row. These adverse cases are preserved, not hidden.
The smallest such example moves hole1 to hole0 to hole2 in a three-label universe,
although1-to2 itself is a valid single exchange.

585 rational moment interpretations check5011 original row identities and exact
tight sets, including221 negative means. The r0/d=m cases are excluded from that
geometric interpretation, not from the combinatorial statement. Another phase-
changing 13-label example checks8 configurations/104 rows, with4 negative means.
Eight selected large models reach m10000 without complete graph enumeration.
53 saved records with638 edges replay with construction disabled; six forgeries
fail. Python, JSON and these instances are not Lean-extracted or kernel-certified.

The complete24690-byte report and536352-byte fixture reproduce byte-for-byte
in a fresh single-script workspace. Script blob28767c9b18134ad396a51e32c6a069536bda01a9;
SHA256229922781bbc8e84c91e4ee35fcd71dc2dcea809551bbfa0079f260dbe8bdcb5.
Report SHA256fda50f2890b7ca82751505b8f6913d6da34ce30ee2fdec29233f62fa82ac8f64;
fixture933eb66f2f6222f077ba56cdbac6e7a0d5cd93395b57d8bd4fdac8abb548fb3d.
Full raw files are in the export and regenerate with:

    python3 scripts/test_alternating_complement_routes.py --out /tmp/alternating

## Ownership and preserved state

All five project instructions and the live open queue/heads/comments were read.
#304 was found ALREADY ACCEPTED after #305 protocol refresh: theorem
9771bc05-8eb9-4606-a21e-79715873624e, submission07282fd9-6960-4e2e-bb91-c94a4d994362.
Its raw publisher receipt says live Proved. It was not resubmitted or modified.
Coordination comment5736281296 on #302 was posted/read back. No #300/#302 run or
source, other owned branch, reserved #210, Lean4.30.0/Mathlib pin, strict0.10.5
version guard, workflow, allowlist or verify/publish credential split changed.
Root STATUS was not overwritten during concurrent work. This handoff records
the concrete blocker and next action for the open draft.
