# ACCEPTED: active-cut injectivity on a positive convex support

## Authenticated outcome

The trusted publisher returned ACCEPTED and authenticated live status Proved
for `Hirsch.cut_vertex_active_support_injectivity`.

- Theorem ID: `c3781e27-7eb2-4ffc-bb5b-e85ffe60c480`.
- Submission ID: `68ad9f06-cdc9-4a25-85fc-b62c5e9b711d`.
- Registration: PUBLISHED, not an accepted-result resubmission.
- Frozen proof head: `533bfb63678730eed6559e512e560ee71713f341`.
- Successful run: `35179232678`.
- Publication command: https://github.com/jjoshua2/prove2me-work/pull/290#issuecomment-5708130529
- Authenticated verdict: https://github.com/jjoshua2/prove2me-work/pull/290#issuecomment-5708156250
- Solution blob: `56e38bebb4d5b3501ee47c05df59631d5c5c0543`.
- Solution SHA256: `3dd3f72bd43461fc68baadd0e12b0dad7526c0cedeece628ca9cdf256b1dd499`.

## Actual verification evidence

Driver, solution and target-statement compile exit codes are all zero.
All four printed transitive theorem reports contain only
`propext`, `Classical.choice` and `Quot.sound`. The target stub intentionally
uses `by sorry` to specify the problem; the submitted solution and its root
axiom report contain no such admission. Do not confuse these two files.

The verified archive (artifact10479811009) was downloaded and independently
hashed as `645fb78c6c05df0d3e89dc05aa44417c1674e722bcd3abd3dc84139da33c8424`.
Every one of its five frozen packet hashes was recomputed. The frozen solution,
problem JSON and explanation equal the prepared files byte-for-byte.
The publication archive (artifact10478694358) has independently recomputed
SHA256 `1552373c079ca3c71b3df5e1bf6aaf3949e80f8a8ef7c62c7eca5e465d4e485c`.
The raw gate manifest, packet audit, compile log and publication receipt are
retained alongside the separately labeled derived readback and this summary.

## Initial failure is preserved, not counted as a submission

Run35178901194 checked head0fc4ee426fd66ea1cc67fce60b1cfe557ce872bf and failed
before publication. The publisher was skipped. Two Lean elaboration causes
affected five sites: unintended variable substitution in a pattern, and finite
sum product projections not simplifying automatically. One consolidated repair
made substitution explicit and proved the two sum/projection identities.
Every old helper signature and the public target remained byte-identical;
problem.json was unchanged. The corrected205-line proof passed the next gate
and its FIRST actual platform submission. See first-gate-repair.json and the
raw first-resolved-request.json. The initial manifest is preserved verbatim
as initial-source-manifest.json; it describes the old candidate, not this one.
No local compiler existed; no local Lean build is claimed.

## What has been formalized

For a convex base and an actual extreme point of its finite halfspace cut,
strictly positive barycentric support cannot have a nonzero affine motion
annihilated by all ACTIVE cut evaluations. Both signs of a sufficiently small
motion preserve the support weights and every inactive strict slack, so such
a motion would contradict extremality. If the support is affinely independent,
its active-cut image stays affinely independent and has at most |active cuts|+1
points. Compactness, simplicity and independence of the cut normals are not
assumed. This is a classical local rank argument, not a historical novelty claim.

This supplies the geometric injectivity step needed by the written #277
cut-image alphabet result. It does not assume that injectivity as a new oracle.
It also does not yet choose a positive independent base-vertex support, select
a minimal independent active-row set, enumerate the full coordinate alphabet,
or prove a uniform polynomial diameter for arbitrary carriers.

The next concrete composition is to choose a positive affinely independent
support using a finite convex-hull/Caratheodory theorem, apply this exact
accepted result, and extract enough independent active coordinate functionals
to determine the weights uniquely. That avoids re-proving a minimal-face
motion lemma and leads into the existing finite cut-image enumeration.
Do not turn a universal small-alphabet hypothesis into a solved premise.

Coordination: #277 comment5708026047. The moment catalogue belongs to the agent
in #288 comment5707992008 and was not modified or resubmitted. Existing accepted
and pending packets, workflows, pins and secret isolation are unchanged.

## Separate supporting arithmetic

The exact test suite reconstructs6 small H models/34 vertices from178 square
systems, checks35 independent and35 dependent positive supports, and exercises
35 coefficient-kernel basis vectors. Six sharp examples reach support size
active cuts+1 in dimensions1,2,3,4,8,16. Five negative controls and inactive
slack margins down to2^-240 are retained. The corrected suite reproduces its
report byte-for-byte in a clean workspace. These tests are NOT Lean-extracted
proofs of the Python program or JSON parser.
