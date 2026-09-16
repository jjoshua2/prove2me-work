# ACCEPTED finite-coordinate route construction: next formal interface

PR #283. Target Hirsch.finite_coordinate_extreme_route_bound is ACCEPTED,
with authenticated publisher readback Proved. Theorem
1f61b140-7502-4508-a812-53fe712f2ad4, submission
119b7820-4131-4c99-ac87-46ec35dc7249. Run35163571909, frozen proof
74dbb5e144bc9ab4c822daff63dabe4f387d9d76. Do not resubmit.

Packet: research/publication_packets/coordinate_extreme_routes/.
Read accepted-evidence.md, publication-receipt.json and packet-audit.json.
The357-line standalone proof passed its first gate and first platform submission
unchanged. Five transitive reports contain only the standard logical axioms.
Proof,problem and explanation remain frozen; later additions are evidence only.

The public theorem has an ACTUAL constructed indexed walk, not a conditional
count on supplied paths. The finite rank_routes helper supports a different
bound K_j per coordinate and an arbitrary set of unfixed coordinates. The
real target constructs ranks from the actual finite coordinate images.
Local one-step improvement and coordinate-extreme closure remain assumptions.

The next geometric adapter must instantiate Fin n with the actual vertices of
a compact polytope, use ORIGINAL ordinary-edge adjacency, and derive admissible
face closure plus local coordinate improvement on every retained face. It must
not replace these with already-assumed short paths. The resulting geometric
corollary would remain a coordinate-inventory bound, not Polynomial Hirsch.
A global polynomial level budget for arbitrary carriers is refuted by accepted
#280's family; adaptive/route-local budgets require a genuinely separate proof.
The #277 common-face detour remains a restriction against shortestness claims.

A first useful restricted adapter may use a rigorously proved H-system class,
but do not claim it covers arbitrary carriers or silently transfer research
#277's cut-image proof into Lean. No such geometric adapter was compiled or
submitted in this turn. The local construction is classically attributed to
the Kleinschmidt--Onn coordinate-extreme argument, not a historical discovery.

The single-cut escape line in #277 comment5702735171 remains independently owned.
Coordination for this formal line is #277 comment5706119177. Accepted
#275/#279/#280/#281 were not retriggered, and all other active branches are
unchanged. No secret, workflow, protocol0.10.4 or Lean4.30/Mathlib pin changed.

Supporting test: python3 scripts/test_coordinate_extreme_routes.py.
It reconstructs finite face closure, checks local moves and exact public-type
matching, and builds2451 walks in32 finite graph models. Complete report hash
232957a0626afa53eaaa538427db3be14aeea32a196d1daaecbf820a02b914b1.
A fresh script/packet directory reproduces the report byte-for-byte. These are
not further formal theorems. Four negative inputs fail structural validation;
they do not independently establish necessity of every hypothesis. The frozen
public explanation's word "countermodels" has that narrower testing meaning,
as clarified in accepted-evidence.md. Source correctness is not Lean-extracted.

Local Lean/Lake was absent. Formal verification is the actual pinned hosted
run requested by the user's new top-level publication comment5706200622.
Raw frozen/request/audit/compile/publication files and independently checked
ZIP digests are preserved. No failed compiler attempt or target repair occurred.
