# ACCEPTED: constructed sliding-block original-edge routes

Public theorem: `Hirsch.moment_sliding_block_original_routes`.
Theorem ID: `e7f0c684-2c01-4076-b964-68ec03d676ad`.
Submission ID: `7ccdf32a-8620-48dd-880b-595615703cfb`.
Trusted publisher verdict: ACCEPTED; authenticated readback: Proved.
Accepted proof SHA: `3ff470b30ff3270461c1ea54298fb8ebe68f13f5`.
Run: `35268954077`; PR #296.
Corrected trigger: comment `5720540710`; verdict: comment `5720601557`.
Verdict time: `2026-09-17T20:12:32Z` (16:12:32 America/New_York).

## Exact formally verified result

For a strictly increasing real sequence a indexed by natural numbers, positive
k, and m original labels with2k<m, use the original mean-centered dimension-2k
moment inequalities. For any nonnegative s,L with s+L+2k<=m, the theorem proves
L<=m-2k and constructs an INJECTIVE sequence p of L+1 actual extreme points:

- Point p(t) is feasible and its EXACT tight original labels are
  s+t,...,s+t+2k-1.
- Every successive closed segment is an actual Mathlib IsExposed subset of the
  original feasible set. Injectivity makes each segment nondegenerate.
- Each original row's tight times form an interval; nonrevisiting is derived.

It constructs every vertex from coefficients of a paired consecutive-root
polynomial. Positivity of its full-label mean, original-row feasibility, exact
tight labels, extremality and consecutive exposedness are proved. No vertex
list, feasible path, rank, exchange sequence or adjacency oracle is assumed.
The entire supporting-slice result from accepted #295 supplies actual ORIGINAL
edges, not projected chords or merely equal endpoint objective values.

The size assumption on s,L only fits the windows into the finite original label
set. It does not assume their geometric feasibility. The theorem covers L=0;
k=0 is explicitly excluded. The premise is a globally strictly increasing
sequence on natural numbers, of which only the first m values are used. No
unordered-finite extension theorem or arbitrary-polytope representation is
silently assumed. The count parameter is the number of original inequalities;
a separate formal irredundant-facet interpretation is not asserted here.

This is a counted route CLASS through consecutive-block vertices, NOT all pairs
of moment vertices and not a Polynomial Hirsch solution. Other vertices may
have separated pairs of tight labels. The theorem does not route those into
this chain, prove a shortest path, or assert any general diameter bound. Classical
cyclic-polytope paired-root mathematics and the earlier #267 experiments are
credited. No historical-priority or best-known cyclic diameter claim is made.

## Actual correction, compilation and submission history

The initial871-line proof was checked in run35267809797. It had one displayed
error in the finite overlap membership proof at line763: automatic simplification
left a coerced constructed Fin label unidentified with its natural-number value.
The polynomial zero-set construction and actual extreme-point theorem compiled
with standard axioms; edge/route declarations inherited the failed elaboration
and were NOT verified. Publication was skipped, so no platform registration or
submission was made from that run.

The only proof correction replaces that four-line overlap subproof with explicit
Finset membership implications and congrArg Fin.val/Fin.ext. No hypothesis,
conclusion, public wrapper, other helper body, problem.json or explanation.md
changed. The accepted #295 namespace prefix is still byte-identical:22583 bytes,
544 lines, excluding its previous top-level solution/prints.

The corrected889-line proof, driver and target statement all compile with exit0
under Lean4.30.0 and the unchanged Mathlib pin. All FIVE transitive audit outputs
list only propext, Classical.choice and Quot.sound. No source proof admission
or target import occurs. Harmless inherited linter warnings remain in the raw
log. The corrected proof's FIRST actual platform submission was ACCEPTED; the
initial compile attempt is not described as successful.

The requested NEW top-level PR comments actually invoked the existing workflow:

    /prove2me publish research/publication_packets/moment_sliding_block_routes

No dispatch, workflow, pin, permissions, token, protocol or trusted publisher
secret split was changed. The local environment had no Lean/Lake executable;
formal compilation is the pinned hosted gate, not rational tests relabeled as
verification. No other owned branch or accepted/pending target was retriggered.

## Preserved original artifacts

The original ZIP archives were downloaded and independently hashed:

    first request: 9c5866371c88c9893117571b85650446e26748541c439edd1c3afccb8ebe1106
    corrected request: 0188cec2baeca1407cf382fab33054ed9c5c5c4c62ee5340b20c7b931ecf156a
    verified: cf44866ffce620e9c7d0e32ea2175b5cc54840dfa10e2df41b150ad5b9d13cf0
    publication: 14a98be3fa96d4fbdaf94a53bfd1f1688f85cb1d710ebe1c00a68af466e66f1c

All FIVE frozen source/driver/statement/metadata hashes were recomputed. Solution,
problem and explanation match the corrected prepared files byte-for-byte.
Accepted solution SHA256:
5be516fabb700f4f19f881536558c58ab959dec90e6193a8b957e275e40104be.

Raw packet audit, verified manifest, full driver log and aggregate publication
receipt are committed unchanged. Derived local readbacks are labeled. The
publication ZIP contains the aggregate receipt and generated PR comment, not
individual raw platform API responses. Proved is the trusted publisher's
authenticated readback; this chat did not make a separate direct platform poll.
No missing raw API responses or first-run full log are invented. The initial
failure note is explicitly a diagnostic excerpt. Post-verification files are
support/evidence only; the accepted proof and metadata remain unchanged.

## Supporting exact tests, including adverse examples

    python3 scripts/test_moment_sliding_block_routes.py

Nine independently reconstructed small original-H graphs use2014 square systems,
255 vertices and687 edges;1759 infeasible full-tight systems remain excluded.
The constructed full corridors have30 original edges, checked by1437 supporting-
objective evaluations on every reference vertex.85 corridor endpoint pairs
include SIX subpaths longer than independent BFS distance. In the2D/eight-row
case, the six-edge full corridor has endpoint distance two. This is not an
optimal-path method or a benchmark-improvement claim.

Sixteen assorted subcorridors include zero-length cases and nonuniform nodes.
Four explicit higher-dimensional tests d8/16/32/64 construct8/16/32/64 original
edges without enumerating full graphs. Twenty-one saved consumers replay with
polynomial/witness production disabled; eleven malformed inputs fail. Odd-degree
root polynomials can change sign between the two outside regions; that negative
control preserves the theorem's positive-even-dimension restriction.

The full13996-byte report and1240291-byte fixture reproduce byte-for-byte in a
clean directory with only the standalone test and proof/metadata inputs. The
repository summary is explicitly derived; the raw report and fixture are bundled
and regenerate. Python and JSON parsing are not Lean-extracted or formally
verified. These checks support interpretation but do not establish acceptance.

## Next interface

A concrete original-route construction now follows the accepted edge theorem,
rather than assuming a feasible exchange chain. Generalizing it would require
handling separated root pairs and proving enough legal moves with a controlled
count, or another genuine route construction. Merely supplying that sequence
as an assumption would not solve the remaining problem. Reuse this accepted
class theorem; do not resubmit it or misstate it as an all-pairs upper bound.
The older PREPARED/correction status in source-manifest is historical and is
superseded by the actual publication receipt and this note.
