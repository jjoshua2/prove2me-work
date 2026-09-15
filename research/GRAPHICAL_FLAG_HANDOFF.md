# Continue from the graphical nested-refinement criterion

Read live STATUS and actual PR heads. This is written research/exact Python,
NOT a Lean-compiled or Prove2Me-accepted theorem. #264's further plateau work
is separately owned and untouched. The current contribution imports #261's
original-H classification and #258's route/edge machinery unchanged.

For an auxiliary graph G on the m ORIGINAL facet labels, let B be all nonempty
ORIGINAL faces whose induced G-subgraph is connected. The nested refinement
uses these tubes as vertices. A family is a face only if its union is an
original face AND pairs are nested or disjoint with no G-edge between them.
Do not omit the union condition or silently replace this by the clique complex.

The full face-poset building set has factors equal to induced G-components of
each face. Feichtner--Kozlov Theorem3.4 supplies the decreasing-inclusion stellar
subdivision. The exact flag criterion proved here is

    every original minimal nonface N has at most two components in G[N].

The proof is two-way: three components give a missing clique of tubes; conversely
a clique's maximal tubes are anticomplete, so a contained minimal nonface with
at most two components would lie in one/two tubes whose union is a face.
The private-label carrier argument maps refined adjacency to an original edge
or a stationary step. Compatible endpoint lifts preserve every common original
facet. The classical AB normal-flag theorem then gives original diameter<=M-d,
M the number of connected ORIGINAL faces. No auxiliary projection is used.

For a path or union of paths, M<=dm-d(d-1)/2. For maximum degree two, M<=md.
These give polynomial class bounds IF the exact graph criterion holds. There
is no theorem that every polytope has such a graph. Complete original minimal-
nonface discovery may be exponential and may identify every original vertex.
The graph optimizer is a capped finite branch-and-bound; complete search only
certifies optimal M within its degree class, not among all refinements.

The static certificate on #263's SAME 5D/10-facet plateau has graph edges
01,08,23,45,56,78. Its tube registry has10 singleton vertices and6 edges, M16,
all-pairs bound11. Connected triples are original nonfaces, so these subdivisions
commute. All720 orders give the same flag complex after canonical naming;
314 orders are strictly W-decreasing,420 step occurrences are neutral,none
increases W. Thus this is not a claim that a neutral step is unavoidable from
the original input. It removes dependence on a greedy schedule or macro search.
It matches #263's final M16 and improves on the BEST flat partition M18.

Other exact graphical-vs-best-flat counts: C(7,4) boundary11 vs12; C(8,4)16 vs20.
The flat comparisons enumerate all877/4140/115975 respective set partitions,
not a heuristic partition. However general stellar schedules already give M14
for C(8,4), so graphical certificates do NOT dominate arbitrary hierarchies.

Actual sparse-class obstruction: for boundary C(n,4), every cycle-stable triple
must contain a G-edge. Then complement(C_n union G) is triangle-free, forcing
|E(C_n union G)|>=binom(n,2)-floor(n^2/4). For maxdegree(G)<=2 this exceeds the
available2n edges for every n>=11. This is an all-size proof, not an extrapolation.
For n9 the test separately exhausts all20160 Hamiltonian cycles; none qualifies,
so no Hamiltonian path qualifies either. Do not turn that n9 result into a
statement about all disconnected degree-two graphs. Dense G may still have a
polynomial connected-face count on some classes; this is not a universal lower
bound on M or a Hirsch counterexample.

Reproduce:
    python3 scripts/test_graphical_flag_refinement.py --stage abstract
    python3 scripts/test_graphical_flag_refinement.py --stage geometry
    python3 scripts/test_graphical_flag_refinement.py --stage obstructions

Five unchanged inputs/dependencies: four scripts plus #263's integer plateau
fixture. The generic producer input is A,b,start,target and an auxiliary graph;
it supplies no vertex graph. The test reference does enumerate small graphs.
52 pairs give104 new edges,104 raw#258,104 BFS,with108 refined steps and4
stationary carriers. No aggregate benchmark advantage is claimed. The abstract
suite covers7296 complex/graph pairs and24714 pure carrier adjacencies. Ten
forged/capped cases fail; five complete audits disable geometric discovery.
BFS/recursion still replay. The checker and JSON parser are not Lean-extracted.

The complete three-stage clean replay uses only two new scripts, four old
scripts and the existing integer fixture. Every nontiming report field and
the226241-byte certificate fixture match exactly. Reports regenerate; repository
summary/replay records are derived local evidence, not platform receipts.

Next work must control connected original faces for a suitable graph on arbitrary
carriers, combine this representation with other controlled subdivisions, or use
another original-edge invariant. Do not insert existence of a sparse graph or
a polynomial tube registry as an unproved lemma and call that Polynomial Hirsch.
Keep pins, workflows, credentials, pending submissions and other branches intact.
