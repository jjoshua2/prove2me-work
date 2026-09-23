# First radial-polygon gate: two new geometric lemmas clean; full packet failed

PR #339 is OPEN/DRAFT and unmerged. Target:
Hirsch.actual_planar_vertices_rank_attaining_original_routes.
Tested proof14f50c6a2ffb47fdce165753a889feb083800004; source940 lines/39495 bytes,
blob3ed33059e0c0611b61d2f809e796bc8094184503, SHA256
96b4c2fb43fc03b3143c8155e4bb1771e11675167e09557ba4602443e9576226.
No proof or metadata edit was made after this gate.

## Actual outcome

New top-level request5802759818, acknowledgement5802762849 and run35918994272
were read back. Gate107377791629 succeeded; verifier107377867035 failed driver
compilation with exit1. Standalone solution and exact target statement were not
reached. Publisher107378455630 and report-verify107378454193 were skipped.
One hosted attempt, zero registrations/proof submissions; no theorem/submission
ID, verified artifact, publisher receipt, ACCEPTED or Proved was produced.

The inherited exact_rank, new radial_mass_gt_one and new secant_edge reports
contain only propext, Classical.choice and Quot.sound. vertex_chain, ray_edge,
original_routes and public solution retain failed-elaboration sorryAx. No
admission was written. Clean helper reports do not verify the complete packet.

## Four localized repairs proposed, not applied or compiled

Five displayed errors arise at four root sites:

- 405: normalized_interpolation needs one_mul to remove leftover 1*inverse terms.
- 430: strict_chord uses a multiplicative-order lemma requiring an unavailable
  MulRightStrictMono real instance. Use (div_lt_iff₀ hx).2 and the existing
  positive denominator instead. The line431 no-goals diagnostic is a cascade.
- 687: ray_edge needs the local f and w definitions unfolded in its identity.
- 834: expose the natural-number value of Fin zero before proving 0<=i.val.

Exact patch: research/verification/radial-polygon-routes/first-attempt/
proposed-local-repair.patch. The complete proposed source is937 lines/39437 bytes,
computed blob303dc7e6d2239690dcebde0600acf537124a0363, SHA256
1a850ee30cfc49facfb0d9b82acd5659a692c5bd272c3d28a66ed56e320c88f2.
It is UNAPPLIED to the publication source and UNCOMPILED. Apply/check/reverse
passes. All declaration statements, public hypotheses/type, accepted dependency
bytes, metadata and explanation remain unchanged. Further errors may appear.
No second trigger was posted. Resume the same PR after fresh ownership/pending
checks, with local compilation when available and one prepared complete gate.

## Mathematical progress and limits

The complete written proof derives strict inverse-height convexity from original
extremality, not from an assumed favorable chain. The clean radial-mass lemma
shows that a nonnegative combination of other feasible radial vectors representing
an extreme point must have total coefficient greater than one. The clean secant
edge theorem turns a complete lower chart secant into a WHOLE original exposed
segment. The full proof still needs the four repairs before these can support a
verified assembled route theorem.

The candidate also constructs the target ray edges, both counted boundary walks,
and their shorter choice with L=min(k,n-k)+1 and2L<=n+2, composing with #338's
accepted exact-rank namespace. P is the original hull, not a refinement graph.
Full vertex-hull identity, actual extremality, chosen strict exposure, independent
coordinates and sorted complete order remain explicit inputs. The bound counts
original vertices, not original facets. No uniform high-dimensional result,
H-to-V/chart selection, arbitrary-walk shortestness or edge-exhaustion theorem is
asserted. The singleton chart is included formally but not in the executable tests.

## Tests and stored evidence

A new committed rational supporting test checks118 charts,19012 triples,750
exposed-segment occurrences and632 routes/1896 original-edge occurrences across
12 planar models, including shears/translations and a32-vertex/four-target case.
Ten malformed/premise controls fail. A clean three-script replay reproduces all
four complete output files. The two dependencies are unchanged #337 utilities;
no old blocked solver was run or uploaded. Python/JSON are not kernel-verified.

Only request artifact10776780823 exists:310 bytes, SHA256
bb6b43a56be40b9d9984edb39ee688d5009957c829ee0ebc0710d38992d4eeca.
The ZIP was downloaded/rehashed and its resolved.json preserved. Full decoded
verifier logs were read through cleanup. The saved displayed diagnostics and
all seven reports omit timestamps/setup/cleanup; they are not a complete raw
runner archive. Original failed inputs are preserved by exact blobs.

Local Lean/Lake/cache was unavailable and toolchain DNS failed. Source matching,
patch checks and rational execution are not compilation. Keep Lean4.30.0,
Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8, other owners and
all publisher/credential safeguards unchanged. Handoff:
research/RADIAL_POLYGON_ROUTES_HANDOFF.md.
