# Prove2Me late publication update — 2026-09-10

This is a delta to the earlier 2026-09-10 publication update and supersedes the
9/9 index wherever they disagree. The global Polynomial Hirsch frontier remains
unchanged: `Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) is **Open**.

## Compact simultaneous clipping — public / Proved

`Hirsch.simultaneous_clipping_diameter_of_compact_outer`

- theorem ID `75d26f37-e0bd-4d73-9128-688fe7d5a80c`
- submission ID `2c038ea7-ebc9-4f22-80c6-328fab2ea613`
- **ACCEPTED / Proved**
- source verification run `34485975796`
- publication run `34487272212`
- standalone SHA-256 `fe83809fcda2cc6b2714193964e8f8be6ad2a1705ac4e3383b8dc6621736564f`

For compact convex outer `Q`, finite simultaneous halfspace cuts, outer padded
diameter `D`, and intrinsic padded diameter budgets `B_i` on the corresponding
**final** exposed cut faces, the final intersection has padded diameter
`D + sum_i B_i`. No separate strict-centre assumption appears in the public
statement.

This closes the end-to-end bounded-clipping Lean assembly that the 9/9 index
still described as incomplete. It does not prove Polynomial Hirsch because the
face budgets remain hypotheses and arbitrary circuit/projective evolution is
not yet shown to supply them with polynomial total cost.

## Sharp row-circuit common-face localization — public / Proved

`Hirsch.row_circuit_common_face_dimension_bound`

- theorem ID `f0e79793-711b-4ada-b276-b4eab1fd0fe8`
- submission ID `b5028624-3b66-4e72-8f8d-5b269a429128`
- **ACCEPTED / Proved**
- frozen source commit `9f964b8617fbbcae3cf652c130cbdbacd32b0dea`
- source verification run `34495410594`
- standalone SHA-256 `6d3b6b7aecd9c483d30acdff94ff304afad8a8c45f6948b6c12aba1efc1ec009`

For extreme vertices `u,v` of an `n`-row H-polytope in ambient dimension `d`,
if `v-u` is a support-minimal row circuit, then

`2 * HirschCommonFace.commonFaceDim a b u v + d <= n + 1`.

No simplicity, irredundancy, strict-feasibility, or maximal-step assumption is
used.

## Balanced/estranged one-step obstruction — public / Proved

`Hirsch.balanced_row_circuit_vertices_share_tight_row`

- theorem ID `73ce6c5c-25d8-46ec-9d77-a9f2b5d7b454`
- submission ID `cf5a5faa-d4d2-419e-8802-62aded7c1e51`
- **ACCEPTED / Proved**
- source verification run `34495410594`
- standalone SHA-256 `e9b2a0be5fde78404b9b3456a8936d1ff3fea93be27c4cff0d318d02e27fe4ce`

If `n=2d`, `d>=2`, and two extreme vertices have row-circuit displacement,
they share a nonzero describing row tight at both endpoints. Thus an exactly
balanced estranged vertex pair cannot be a single row-circuit step.

## Publication gate and readback

The two circuit results were published by Actions run `34496281896` from an
immutable artifact produced by run `34495410594`. The publisher validated the
standalone proof hashes, public definition dependencies, Prove2Me version 0.9.9,
and the Open frontier before any write. It received `ACCEPTED` for both proofs,
read back both theorem statuses as `Proved`, and rechecked the frontier as
`Open` afterward.

Receipt artifact `10160146095`, digest
`sha256:9d2861066a81d8abf7f0c994372ca03f2acf4b9029f00c47b2c31818d29c1638`.
Mission discussion comment `ed23703f-6e2a-4199-ab42-bc43bd60e8cd` references
both new theorems and the unchanged Open frontier. The temporary push-triggered
publication workflow was deleted immediately after success.

A separate clean integration branch copied the exact verified Git blobs onto
the then-current `main` and independently rebuilt the source modules and the
same hash-locked standalone proofs in Actions run `34497418271`.

## What remains research-only

The broader circuit-localization research also studies intrinsic neutral-rank
defect after restricting to a common face. Circuit status can be lost when
intrinsically redundant restricted rows are removed. The ordinary research
proposes a monotone resource `B = facet excess + neutral-rank defect` and gives
optimal completion constructions showing equality can occur.

Those defect-transfer and optimal-completion statements are **not** yet Lean
or Prove2Me theorems. The next formal target is the neutral-row rank
characterization of `IsRowCircuit`, followed by face-restriction defect/excess
transfer. Neither should be registered as a new conjecture-level child unless a
strictly smaller non-cyclic parent reduction is first demonstrated.
