# Defect-block refinement handoff

This is RESEARCH/CODE, not a Lean packet. Integration base is
73900455acaa956ba82d57ac5e54821fd0f13f39, preserving concurrent #259. Preserve #258's original-facet segment
and exact original-row intersection implementation unchanged. The initial
coordination was #258 comment5683887860. The final theorem is stronger than
that comment's preliminary within-one-block idea: EVERY minimal nonface need
only intersect at most TWO disjoint blocks.

## Main theorem and exact required input

K is the (d-1)-dimensional facet-intersection sphere of a SIMPLE bounded
full-dimensional polytope with m genuine original facets. Vertices of the new
complex are nonempty K-faces contained in one partition block. Refined faces
are within-block chains whose total carrier is a K-face. This is a genuine
joined barycentric subdivision, not a high-dimensional polyhedral extension.
It is flag iff each original minimal nonface meets <=2 blocks.

Let M be the number of those nonempty block faces. The classical
Adiprasito--Benedetti theorem supplies <=M-d refined dual edges. Adjacent full
refined facets share d-1 vertices; their carrier unions therefore share at
least d-1 ORIGINAL labels. Erase equal carriers and obtain ordinary original
edges, not projected chords. Every final edge is independently checked on the
actual original inequalities. Original facet reentries are permitted.

If max block size k, M<=m(2^k-1)/k. For size-two blocks, M=m+q where q counts
intersecting pairs, giving m-d+q. This is a genuine structural route bound,
not a theorem that arbitrary carriers have cheap blocks. Pair endpoints lift
with shared ORIGINAL labels first in each chain, keeping their common face.

## What the current code actually does

It finds ALL minimal nonfaces using exact original-H intersection witnesses
and strict dual exclusions, checking subsets through d+1. This can be
EXPONENTIAL and can enumerate all original vertex active sets. Do not claim
that absence of an input graph means absence of vertex-enumeration cost.
The raw classification cap fails before incomplete flagness can be claimed.
Even a supplied partition is completely checked. Default block merges are
heuristic, not an optimized minimal-cost partition.

The refined phase queries virtual link faces lazily; it does not enumerate
the whole refined dual graph. The consumer replays finite classification and
BFS on certified link graphs. It is free of LP/inverse discovery, NOT of all
graph computation. Original simplicity/irredundancy are the input class, not
inferred globally from visited bases. All old dependencies are unchanged.

## Positive family and explicit barrier

A product of r triangles, cut sequentially by u_i+u_(i+1)<=2-10^(-(i+1)), has
dimension2r,4r-1 genuine facets and a size-two partition giving M=5r-1 and
bound3r-1. The proof checks safe small codimension-two cuts and commuting edge
subdivisions. The genuine facet normals form a connected matroid, so the final
polytope is not an affine Cartesian product. No product chart or history is
passed to the producer. Tests cover r2/3/4, with global bounds5/8/11.

A d-simplex has one missing face of size m=d+1; ANY valid block partition has
at most two blocks. Its best blockwise count is
2^floor(m/2)+2^ceil(m/2)-2, despite diameter1. This disproves a universal cheap-
partition premise. It does NOT exclude other flag refinements: a hierarchical
edge-splitting construction gives the simplex boundary a2d-vertex flag refinement.
That last illustration is written, not a separately implemented optimizer.

## Actual comparisons

418 pairs on7 independent original graphs: new898 edges, raw#258863,
unchanged#253858, BFS854. New31 nonshortest versus raw9. Not a new default.
Refined983 edges include85 stationary carrier transitions; projected original
reentry debt24 remains. The latter is legitimate, not a failure of refined
flag nonrevisiting. Other boundary cases are not silently counted.
Three additional coupled-family routes have9 edges total. Abstract tests cover
114 labelled four-vertex complexes and1710 partitions;4506 pure carrier checks.
Fifteen distinct malformed/capped controls are rejected. Full packet replay
succeeds with LP, inverse and basis generation disabled.

## Local commands and delivery

    python3 -m py_compile scripts/defect_block_routes.py scripts/test_defect_block_routes.py
    python3 scripts/test_defect_block_routes.py

Stage options: --model NAME, --aux, --assemble. Names appear in models().
The no-argument call executes all stages. Full reports/pair tables/fixtures
regenerate; the compact committed summary labels itself as derived and binds
the full report by SHA256. The add-only patch must contain only the two new
scripts, note, handoff, summary and reproducibility records, not old dependencies.

No new Lean source, compiler result, hosted gate, Prove2Me acceptance, workflow,
secret or pinned-environment change is included. The next productive direction
is broader low-cost flag refinements or another global route measure, not a
reproof of the already accepted interfaces or the false universal raw segment
length bound. Read live ownership before modifying #244/#238/#250/#255.
