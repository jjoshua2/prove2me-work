# ACCEPTED: normalized tangent slices give genuine improving image edges

The trusted publisher reports ACCEPTED and authenticated live Proved for
`Hirsch.normalized_tangent_slice_lifts_to_image_edge`.

- Theorem `b531d260-eff2-475a-b25b-e7c941a21ec6`.
- Submission `cdeaac97-9b6c-4b7b-aba8-2ec80f32efef`.
- Frozen proof head `7d3c7cfcbbb4a3b7d4eda9aa728330592faf1770`.
- Run `34900402935`.
- Actual command: https://github.com/jjoshua2/prove2me-work/pull/248#issuecomment-5671219849
- Authenticated verdict: https://github.com/jjoshua2/prove2me-work/pull/248#issuecomment-5671267276
- Solution Git blob `afe5c9bb533b15e4bbf7df910be62e809df5a671`.
- Solution SHA256 `a1bf73c13e7fd2df2d852e183086a6d20a86c60591236ce6e5bd40ea0704c7dc`.

The original285-line proof passed its FIRST guarded compiler/axiom gate and
FIRST actual platform submission unchanged. Driver, solution and statement
exit codes are all zero. All five printed declarations have only propext,
Classical.choice and Quot.sound. Unused-variable warnings are preserved in
the raw solution-compile.log rather than silently removed after acceptance.
No proof repair or resubmission was needed.

The original verified ZIP (artifact10370796551) has SHA256
`0f374413c76e71aac0ce8bf17b75827b10c6599e05891a1502f61595826f6a0c`.
The original publication ZIP (artifact10370886309) has SHA256
`b22c810154f2b8948eb55b42833ff69b00187cc0cdbbc733f8bf2d2d9d9e0763`.
Both were downloaded and hash-checked; all five frozen packet hashes were
recomputed. The frozen proof and explanation equal the prepared local bytes;
problem JSON semantics also match. Raw audit, manifest, compile log and
publication-receipt.json are beside this file. artifact-readback.json is an
explicitly DERIVED summary, not an invented raw platform API response.

## Exact result, distinct from the producer

Finite strict slacks prove exact image tangent realizability. Positive active
row weights and an image-row factorization give positive height on every
nonzero image direction. A singleton support in the height-one tangent image,
together with maximal positive ray length over ALL source lifts, constructs
the entire original-image supporting segment and its actual IsExtreme property.
The objective improves strictly. No source adjacency, source vertexhood,
source compactness or original-image adjacency/exposing oracle is assumed.

Normalized-slice support and all-lift maximality remain explicit formal witness
interfaces. The software obtains them using accepted #247 fibre-dual geometry
and exact LP certificates; that producer/parser is NOT Lean-extracted. The
formal implication must not be misreported as kernel verification of all JSON
fixtures, formal LP termination, or a uniform polynomial route-length theorem.

## Software evidence and coordination

The two new source files were read back from GitHub and match the executed
local blobs. The unchanged historical exact LP engine is already on main.
A clean dependency replay reproduces all result fields (excluding timing) and
all seven generated fixture files byte-for-byte. The tests check297 routes,
428 original-image edges and20 rejected malformed/capped cases. Two genuinely
nonshortest pentagon routes are retained. No large full graph is enumerated.

Post-gate commits add software, exact evidence and frontier notes only; accepted
solution/problem/explanation are unchanged. #244 retains its independently
owned core-walk concatenation, and #238 its support-witness task. #241 is already
accepted/merged and is not reproved. No workflow, dependency pin, permission or
secret-separation change occurs. Do not resubmit this accepted packet.
