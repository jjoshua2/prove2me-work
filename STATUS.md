# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`; updated after merged research PR #268.
Keep Lean `v4.30.0` and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Read AGENTS.md, CLOUD_AGENT.md, SKILL.md, CONTINUE_HIRSCH.md and LIVE PR heads/
comments before choosing work. Do not duplicate accepted or pending submissions.

The preceding COMPLETE frontier, including every #267 proof and older archive,
is preserved verbatim in [pre-direct-route STATUS](https://github.com/jjoshua2/prove2me-work/blob/5e811793529ebacce9731c39cfe3d1b9d082e7c2/STATUS.md),
Git blob `6821eb73a17019283a8f25f01b20eea735924b06`. This update records research
software and a written fixed-budget equivalence, NOT a Lean/Prove2Me verdict.

## Objective and the refinement limitation that remains in force

The last preserved authenticated mission audit records root
`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` and remaining leaf
`Hirsch.common_face_diameter_of_dim_ge_six`,
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`, Open. This is NOT a fresh platform poll.
The target remains a uniform polynomial number of genuine ORIGINAL ordinary
edges for arbitrary high-dimensional carriers. Count original image facets,
not a smaller extension's rows, and do not label projected chords as edges.

Merged #267 proves in its note that every original minimal nonface has a distinct
minimal descendant under any forward stellar subdivision, with one new root
per step. At full flag completion, q+t<=binom(m+t,2). Its rational cyclic-polar
family has exponentially many certified minimal nonfaces and therefore requires
exponential TOTAL full-refinement size, even though selected original routes
are shortest with16/32/64 edges. The universal small complete forward-flagification
premise must not be reopened as merely an optimistic unproved lemma. This does
not refute Polynomial Hirsch, arbitrary non-stellar subdivisions, inverse moves,
or short paths inside a huge implicit refinement. Class-specific earlier flag
refinements remain correct. See research/STELLAR_NONFACE_PERSISTENCE.md.

## NEW merged #268: direct fixed-budget original-edge search

Research head `8f646809e265422691e848a2c53103d73bba9043`;
merge `c2c2e0156a26a683f8a14c451be76cc94a616d61`.
[Written equivalence](research/ORIGINAL_ROUTE_BMC.md),
[executed summary](research/ORIGINAL_ROUTE_BMC_SUMMARY.json),
[handoff](research/ORIGINAL_ROUTE_BMC_HANDOFF.md), source identities and clean
replay are on main. SEVEN additions. No older proof/selector is changed; no
Lean, axiom or Prove2Me gate was requested. The code is an experiment/certificate
engine, not a newly proved polynomial diameter theorem.

### Exact formula, not a restricted pivot rule

Input is only rational A,b,start,target and budget L. No graph, facet complex,
nonface catalogue, refinement, monotone objective, nonrevisiting premise or
suggested route is supplied. Nonsimple vertices, redundant inequalities and
lower-dimensional H presentations are supported. The positive certificate also
works for unbounded polyhedra with genuine vertex endpoints; do not conflate
that scope with the bounded conjecture or infer boundedness from a local basis.

At each layer choose d tight rows I with A_I R=I_d. For each step choose d-1
rows J tight at BOTH endpoints with A_J S=I_(d-1). Rational right inverses certify
full rank. Feasible full-rank points are vertices; distinct vertices in a common
rank(d-1) equality face are joined by an ordinary edge. Stationary padding is
allowed and removed before output. The proof gives an IFF for existence of a
route with at most the SPECIFIED L edges, not a theorem that a small L suffices.

Finite row selectors guard FIXED-COEFFICIENT inverse equalities. Thus the exact
default formula is linear arithmetic, not nonlinear products of unknowns:
O((L+1)md^2) scalar constraints, O((L+1)md^3) dense coefficient occurrences and
O((L+1)d^2) real variables. Polynomial size in EXPLICIT L is not polynomial in
log L and is not a polynomial solver-runtime statement. Endpoint bases can be
fixed soundly. Encoding-size caps return UNKNOWN before building huge formulas.

Optional lazy mode initially omits inverse variables, tests ranks and learns
exact original-row dependence exclusions globally across layers. Its uncapped
termination is finite, but the number of possible cuts may be exponential.
The exact inverse mode needs no such iterative rank oracle.

### Independent positive proof boundary

Every positive output carries only rational vertices, selected tight rows,
right inverses and a binding to the original input. Its consumer uses standard-
library fractions, NO solver, rank elimination, matrix inversion or graph search.
It checks the original geometry rather than trusting a SAT status. The exported
SMT-LIB text including check-sat is separately hash-bound.

UNSAT is currently ONLY a backend result, without a separately verified proof
trace. In the finite tests, independent original graphs establish shortestness;
do not generalize that to unseen negative solver outputs. UNKNOWN, actual timeouts,
encoding caps and refinement-round caps are not absence certificates. Neither
the Python code nor JSON parsing is Lean-extracted or formally verified.

### Actual new controls and observed limits

The genuine nonsimple4x4 Birkhoff polytope has dimension9,16 facets. A chosen
pair has8 common tight rows but rank7: their segment is a diagonal, not an edge.
The count-only one-step relaxation ACTUALLY returns SAT. Exact inverse mode
returns UNSAT at1; lazy mode learns one dependency and also returns UNSAT. Both
return certified2-edge routes, checked against the24-permutation reference graph.
A dimension16/25-row Birkhoff5 input also has a certified shortest2-edge route;
exact common rank14<15 rules out adjacency without enumerating its full graph.

The CLASSICAL UNBOUNDED Klee--Walkup4D/8-facet example has15 finite vertices,
24 finite edges and selected endpoint distance5. Independent enumeration of all70
bases and BFS confirm this. Both methods produce5-edge paths with one facet
reentry; every five-edge path there must reenter. The input comes from the cited
primary paper, not a new counterexample to bounded or Polynomial Hirsch. Its
nonzero recession direction is checked. A separate explicit cap sum(x)<=19 gives
a bounded9-facet control with27 vertices/54 edges and distance5; all126 bases
are checked. Both H presentations have exact facet-relative-interior witnesses.

Seven small reference models yield44 endpoint pairs and65 vertices/133 edges.
Each method finds44 shortest routes totalling68 edges and reports44 one-shorter
UNSATs. Those shortestness claims use independent reference graphs. Some rows
are deliberately redundant; overdetermined active sets are not all called
nonsimple geometry. Four affine/positive-row-scaling comparisons preserve the
minimum tested length, not necessarily the same solver-chosen path.

Cube5/8 inverse and cube12/16 lazy runs have5/8/12/16 edges without complete
graphs, shortest by source-facet drop. Stationary/interval/embedded-segment cases
pass in both modes. The #267 cyclic control succeeds in dimension6 but REALLY
times out at two seconds in dimensions8 and16 despite known short routes. These
adverse results are retained. No dimension64 direct-SMT or broad-distribution
performance claim is made.

110 positive certificates,94 negative solver queries andTWO actual timeouts
are saved. All110 positives replay with solver/elimination/inverse/search disabled.
Eleven malformed controls fail; four resource-bound controls remain UNKNOWN.
Backend Z3 4.13.3.0 is called through its installed C library, with SymPy1.14.0
only for test references. No package/native library is bundled or downloaded.
The positive verifier needs neither Z3 nor SymPy; no network/credentials are used.

### Reproduction and exact delivery

The full suite repeats in a clean TWO-script workspace and independently after
applying the seven-addition patch to an empty Git checkout. All source files
match byte-for-byte. Every solver/fixture/result field except the explicitly
excluded timing fields matches. Raw fixtures contain different timings, so raw
byte identity is NOT claimed. Canonical nontiming hashes, original/clean hashes
and source identities are recorded. The raw report/formulas/certificates are
bundled and regenerate; the committed summary labels itself derived.

    python3 scripts/test_original_route_bmc.py
    python3 scripts/original_route_bmc.py input.json --budget 8 --output result.json
    python3 scripts/original_route_bmc.py input.json --budget 8 --method lazy --output result.json

For --verify, pass only the result's nested certificate object. The solver can
still take exponential time and a small formula can be difficult. Historical
SAT/diameter work and the classical test models are credited in the note; this
is not a claim to have invented SMT or proved a new known-class diameter formula.

## Preserved accepted interfaces and earlier research

Accepted allocation/representation work through #236/#237/#241, Minkowski
edge/fibre #239--#245, original edge/face certificates #246/#247, valid-edge
selection #248 and face-locking #250 remain available under their exact hypotheses.
They are not an uncompiled backlog and are not resubmitted. #244 retains assembly.

#253--#259 supply tested original selectors, weighted tails, parameterized
exceptional-label bounds and reentry diagnostics. #260--#266 supply counted
block, hierarchical, budget, cactus and graphical class refinements. Their
positive class results and adverse examples are preserved in the previous
frontier. #267's full-size obstruction limits an unrestricted sufficient
strategy without invalidating those class results. #264's independently owned
energy work remains untouched; no cleanup/merge of its separate branch was attempted.

## Next conjecture-facing task

The new tool can test path-local hypotheses on unrestricted ORIGINAL routes,
including nonsimple and forced-reentry cases. The highest-value next step is a
concrete geometric invariant or construction that yields a uniform sufficient
polynomial L, or a checked counterexample to a proposed restriction. Merely
increasing the solver benchmark suite or naming bounded-budget satisfiability
as a new open child is not that proof. A polynomial-size formula for a supplied
budget does not establish a universal short path or polynomial solving time.
Independent negative-proof verification would strengthen experimental lower
bounds, but solver UNSAT alone must not be turned into a platform theorem.

#244 assembly, #238 support witnesses, #250 projected integration, #255 shortening
and #264 energy are separate. #208 needs its approved existing poll, not duplicate
submission; #210 is retired/reserved. Recheck live ownership before further work.
Written mathematics, exact software, Lean compilation, axiom audit, ACCEPTED
and authenticated Proved are distinct. Preserve pins, credentials and publisher
isolation. Research-only work requires no speculative hosted proof workflow.
