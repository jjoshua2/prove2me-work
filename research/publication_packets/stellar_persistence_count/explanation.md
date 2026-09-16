# Formal finite-sequence persistence count

## Exact target and relation to the Polynomial Hirsch work

The submitted theorem is `Hirsch.stellar_persistence_count`. It formalizes the
finite counting core of the written obstruction in PR #267. It is not a new
claim that the Polynomial Hirsch conjecture is solved, and it does not claim
that the entire cyclic-polytope example has now been formalized.

For a finite sequence of t forward stellar subdivisions, with m initial vertex
labels and any finite certified family A of initial inclusion-minimal nonfaces,
the conclusion is

    |A| + t <= choose(m + t, 2)

provided every final minimal nonface has cardinality two. No completeness of A
is assumed. Thus a known subfamily of initial incompatibilities is enough.

The source uses natural-number labels and finite sets, with downward-closed
families K(i) of faces supported on finite vertex-label sets V(i). Each step
subdivides an ACTUAL face E(i) with at least two labels and adds a label z(i)
that was not in V(i). The vertex set is updated by insertion. The new face
family is given by its actual membership rule, not by an assumed monotonicity,
injectivity, cardinality-growth, or persistence premise.

If z is absent from a candidate face T, the rule is

    T is an old face and E is not contained in T.

If z is present, the rule is

    (T without z) union E is an old face,
    and E is not contained in T without z.

All final minimal nonfaces having size two is the explicit terminal flag
condition used for counting. The statement does not assume normality,
polytopality, a carrier graph theorem, or any finite-dimensional geometric
result. Those are not needed for this combinatorial invariant.

## Derived single-step facts

For every old minimal nonface N, the source defines its canonical descendant

    N                                 if E is not contained in N,
    {z} union (N minus E)              if E is contained in N.

The theorem `minimal_descendant` proves this is a minimal nonface in the new
family using the definition of stellar membership. In the unchanged case,
every proper subset remains an old face avoiding E. In the changed case,
removing z or any other descendant label leads to a proper old subset of N.
The Lean proof handles arbitrary proper subsets, not just an unproved
single-deletion characterization.

A decoding identity proves that distinct old nonfaces have distinct descendants:
if z occurs in a descendant, remove z and restore E; otherwise keep it. Freshness
of z ensures that this returns exactly the original N.

The theorem `born_minimal` proves E itself becomes another minimal nonface.
Every proper subset of E is an old face and avoids E. The original E cannot
be the descendant of an old minimal nonface: decoding would say that E had
already been a nonface, contradicting its being the subdivided face.

Therefore the exact finite family

    insert E (image descendant A)

has |A|+1 distinct members, all minimal nonfaces supported on the enlarged
vertex-label set. `step_growth` proves this cardinality and support directly.
It does not count raw generated nonfaces before minimization and does not
assume that higher-defect weight increases. A formerly higher nonface may
become a missing pair while still contributing a distinct root to this count.

## Iteration and final pair bound

The proof inductively constructs a finite certified subfamily B(i) with exactly
|A|+i members. Its elements are genuine minimal nonfaces of the actual K(i)
and stay inside V(i). There is no supplied family-growth axiom in the public
statement; the induction invokes the proved single-step result.

A separate finite induction gives |V(i)|=|V(0)|+i, using the stipulated fresh
vertex insertion at each step. At completion, every element of B(t) has size
two by the terminal condition. Thus B(t) is contained in

    Finset.powersetCard 2 (V t).

Mathlib's finite-subset counting identity gives the desired binomial bound.
The proof is valid at t=0, for an empty certified initial family, for incomplete
initial subfamilies, and for face subdivisions larger than edges. Singleton
renamings are intentionally excluded by the face-size hypothesis.

## Scope of this formalization

The finite-sequence count is the obstruction used by #267: if a family has many
minimal incompatibilities, then a full forward stellar flagification needs room
for their distinct pair descendants. The current packet DOES NOT formalize the
moment-curve construction producing exponentially many initial nonfaces, its
polynomial-size rational coordinates, any direct original-edge routes, or a
uniform diameter theorem. Those remain separate arguments or future interfaces.

Inverse stellar moves, coarsening, and arbitrary subdivisions without a forward
stellar factorization are outside the theorem. The theorem does not lower-bound
original graph distance or the length of a selected path through an enormous
implicit refinement. Earlier positive class refinements are not contradicted.

The public `solution` has an import-only preamble and an inlined target signature.
All helper definitions occur only in the solution and unfold to the exact
public predicates. The public signature and `problem.json` were extracted from
the same bytes and compared exactly. No target theorem is imported; no proof
admissions or extra axioms occur in the solution. Five declarations request
transitive axiom output, including the final solution.

## Validation and publication boundary

The independent finite regression builds actual simplicial face sets and uses
literal maximal-simplex subdivision as the reference. It checks all 114
four-label complexes and 515 actual face subdivisions, including 77 subdivisions
at faces larger than edges. It also checks 80 four-step chains with incomplete
certified initial nonface subfamilies. This is a semantic regression and a
statement-binding check, NOT Lean verification.

The originating container has no Lean/Lake executable, and the public toolchain
host cannot be resolved there. The existing PR-comment workflow is used for one
prepared pinned compilation/axiom/publication attempt, as explicitly requested
by the user. No new workflow, pin, permission, token, or secret handling is
introduced. A source inspection or this explanation must not be read as a
compiler or platform verdict. Only the actual returned run and authenticated
publisher receipt establish those statuses.

Publication command on the open same-repository proof PR:

    /prove2me publish research/publication_packets/stellar_persistence_count

Do not repeat the command while its run or registration is pending. If the
compiler rejects the proof, preserve the diagnostic and distinguish that failure
from a mathematical disproof or from a completed Prove2Me submission.

## Sources

The project argument being formalized is PR #267,
`research/STELLAR_NONFACE_PERSISTENCE.md`. Standard stellar-subdivision background
is Lutz and Nevo, *Stellar theory for flag complexes*, arXiv:1302.5197. The proof
here derives the finite invariant directly and does not attribute it to an
unverified external theorem. No historical-priority claim is made.
