# Deferred clipping closes the maximum-support regime

Date: 2026-09-12. Integration: [PR #197](https://github.com/jjoshua2/prove2me-work/pull/197).
Frozen proof source: [`9f022ff39997a28e51a1ecc39155cb7d852ffd40`](https://github.com/jjoshua2/prove2me-work/commit/9f022ff39997a28e51a1ecc39155cb7d852ffd40).
Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## What is proved

For simultaneous clipping of a compact convex outer polyhedron, the new
`DeferredClipCertificate` fixes a shortest, chordless mixed-region path and its
actual parent-vertex portal pairs before any cut-route budget is supplied.
It retains the old-edge trace, extreme/closed region proofs, duplicate-free
labels and the geometric portal membership needed for #193.

The certificate's callback assembles any routes for just its selected cut
pairs, with cost `D + sum(actual cut costs)`. There is no whole-cut-face route
hypothesis in the certificate existence theorem. Endpoint lifting and radial
retraction are carried through the proof; endpoint singleton regions cost zero
and distinct old-edge regions charge at most `D`.

Let `e=n-d` and `r` count distinct selected cuts. For cuts drawn injectively
from the original rows and a common point strictly satisfying them, #193 gives
small minimum-presentation excess for every charged carrier when `r=e`.
The already-Proved small-excess input discharges each call at cost at most
three. This proves an actual parent-edge route of cost `D+3e` in that regime.

For a bounded H-polyhedron and arbitrary vertices `v,u`, deleting the rows
strict at `v` yields a target-tight compact star. The construction gives a
target-rooted certificate with `D=1` and `r<=e`. Thus:

| Selected geometry | Actual target-rooted route bound |
|---|---|
| Every used carrier has excess at most three | `1+3e` |
| Maximum used support `r=e` | `1+3e`, with all local calls discharged |
| Every used carrier has dimension at most five or excess at most three | `1+(4n+3)e` |

The low-dimensional bound applies to the intrinsic carrier dimension, even
when the parent dimension is high. Larman in the canonical affine chart gives
`n*2^(h-3)<=4n` for `h<=5`; affine diameter transport and extreme-face routing
turn that into ordinary parent edges. The budget `4n+3` safely covers both
classes, including natural-subtraction and zero-support boundary cases.

The theorem
`target_slack_quadratic_route_or_few_cut_high_dim_high_excess_carrier`
returns either the displayed quadratic route, or the same certificate with
`0<r<e` and an actual selected cut pair whose common carrier has both dimension
at least six and minimum-presentation excess at least four.

## Exact scope and remaining gap

These are local Lean theorems using two explicit classical inputs:

- `SmallExcessHpolyBound`, exactly the Proved
  [small-excess H-polyhedron theorem](https://prove2.me/theorems/12426807-9602-4014-bd5e-c69fb43f4cb6).
- `LarmanHpolyBound`, exactly the Proved
  [Larman theorem at this pin](https://prove2.me/theorems/68453b6b-bcef-4672-b877-d04e56527e3f).

Their live statements, environments and Proved status were checked and saved
in [public-inputs-and-frontier.json](verification/2026-09-12-deferred-clipping/public-inputs-and-frontier.json).
Keeping these inputs explicit avoids importing local theorem placeholders.
The new geometric assemblies have not been submitted as new platform theorems.

The high-carrier alternative is an unresolved obligation, not a lower bound
or an obstruction to the existence of a short route. It identifies the pairs
for which our estimates remain insufficient. Bounding one witness does not
bound all selected calls. The next task is a uniform polynomial bound on their
**total** cost, using their shared selected geometry. A recurrence with several
independent calls of excess `e-1` is insufficient by itself.

The live root remains Open, with
[common-face diameter in dimension at least six](https://prove2.me/theorems/87a8b4f4-8b58-4340-8cb9-5fd1b548d01e)
the sole reported open leaf. No root dependency has been changed by this work.

## Reproduction and preservation

Run `lake build Solutions.PolynomialTargetConeDeferredCosts` at the frozen
source commit. The successful targeted build checks the whole affected import
chain. All 13 new/adapter declarations are present in the axiom log; the audit
checked 373 reports in total and found only `propext`, `Classical.choice` and
`Quot.sound`. No new source contains an admission or unchecked axiom.

The [verification manifest](verification/2026-09-12-deferred-clipping/verification.json)
records exact source hashes and the complete
[build log](verification/2026-09-12-deferred-clipping/targeted-build.log).

The padded-route adapter is reused byte-for-byte from PR #197 source commit
`be8b34a4e37df36e8f2702938d83a9210f5e6338`. Its hosted
[verification run 34705245819](https://github.com/jjoshua2/prove2me-work/actions/runs/34705245819)
passed; its [axiom artifact](verification/2026-09-12-deferred-clipping/adapter-hosted-axioms.log)
is preserved. The completed one-shot workflow is removed from integration.
The four subsequent modules were verified locally; the original hosted run
is not claimed to cover them.
