# ACCEPTED: selected original active cuts and a square weight system

Theorem: `Hirsch.cut_vertex_selected_active_square_system`.
Theorem ID: `d01a7a03-fda5-4dd3-a058-7f38127c3228`.
Submission ID: `6f3c3e48-8375-4dbd-a965-c296859574e8`.
Authenticated verdict: **ACCEPTED**. Trusted publisher readback: **Proved**.

## Actual new comment, exact source and completed run

On open same-repository PR #294, new top-level conversation comment5720225598
started with `/prove2me publish research/publication_packets/cut_vertex_active_square`.
Bot5720227881 resolved proof053cc6ac62a489b6d104968f72a2c1e8e1b9c4b4 and
run35266694176. The authenticated verdict was posted and read back in
comment5720271472 at2026-09-17T19:48:42Z. Trusted workflow main was
baa437ee2241fedb32028f9ac140c7770036ec0c, distinct from the candidate proof SHA.

The run completed successfully: gate105355537691, verify105355603905 and
publish105356096045 succeeded; report-verify105356097320 was skipped.
All three driver/solution/target-statement compile exit codes are zero.
All six transitive proof reports contain only propext, Classical.choice and
Quot.sound. The source is506 lines, blob04ac0dda22a4ff0776d11f90885391aaacd5dfc7,
SHA2564071a0a4b03f17e7704078b1e9c3fda81f936fa6a6e504cfa24734a906a2a15f.
No proof or target change followed this successful verification/submission.

## Historical failures, unchanged mathematics

The two earlier runs35249408324 and35249850308 failed before publication;
neither registered or submitted a theorem. The first needed RingHom.id_apply
in a scalar simplification. The second left the bundled evaluation map applied
to the constant-one vector unreduced. This continuation applied exactly the
saved proposal: an explicit change to sum_i u_i*1=0, then simplification of
mul_one. No other proof code, theorem type, assumption, bound, metadata or
accepted dependency body changed. The earlier failed files/log excerpts remain.

This was the THIRD lifetime compiler gate and FIRST actual platform submission,
not a first-attempt compile success. Exactly one new publication trigger was used
in this continuation. Fresh runtime checks found no local Lean/Lake; compilation
is specifically the pinned hosted evidence, not a source/Python check relabeled.

## Raw evidence, independently checked identities

Downloaded original archives and SHA256:
- request10516074744: 8872ecbe29672931a2fc989b52c7ce502d72d3a36ee1f174df5ea5abb9fadde4;
- verified10516119901: 7a5b8f2e0e32c26e5dd885aa2c30c9398af4441be36372d4c0400794e3045b9f;
- publication10517385226: 0db50cc79c57a0daa8443c2ed9f1183129f004c2677bc3d73f64dadbfcea7762.

All three digests and all five frozen packet file hashes were recomputed.
The solution/problem/explanation match the prepared source. Complete compiler
logs, immutable audit/manifest, resolved request, verified-artifact summary,
raw publication receipt and publisher comment are preserved unchanged. The
publisher job log was read through verdict, archive upload and posted comment.
Derived readbacks are separate. Proved is the publisher's authenticated readback,
not a separate direct API poll. Missing raw individual API bodies are not invented.
The deliberate statement placeholder is separate from the admission-free solution.

## Exact new result and what it does not say

For every actual extreme point of convexHull(S) cut by finitely many original
halfspaces, construct a positive independent n-point support, n<=d+1, and exactly
n-1 ORIGINAL cuts active there. Together with mass their square system has one
and only one real weight vector for EVERY prescribed real mass/selected values.
The original right sides and mass one recover the actual positive weights.
Neither support, row subset, inverse nor rank certificate is a premise.

S need not be finite or compact, and support points can individually violate
the added cuts. A singleton support needs no selected cut. Uniqueness is for
weights on the selected support, not canonicity of that support or row set.
Arbitrary selected values do not promise positive weights or a feasible point.
The complete accepted #291 source is reused except its old root/print name.
Classical basis extension and convex geometry are credited; no priority claim.

The unchanged exact test suite was rerun byte-identically:96 row systems,
288 signed recoveries,2448 inverse identities,1332 small row-subset checks,
and seven simplex-cut examples through dimension16. These are supporting tests,
not another Lean theorem or certified parser. The next finite-catalogue work is
owned separately in #294 comment5720255040. This theorem does not yet bound its
full recipe count, prove a polynomial global alphabet for arbitrary carriers,
or solve the ordinary-edge Polynomial Hirsch question. Do not resubmit.
