# The exact geometric objects of normalized circuit enumeration

## Result

For every real linear map A:R^n -> R^k, set

    K={x: x>=0, A x=0, sum_i x_i=1}.

The theorem proves that x is an extreme point of K if and only if x belongs to
K and its support is minimal among supports of ALL nonzero nonnegative null
vectors of A. Thus normalized positive circuits and vertices of this compact
section are exactly the same objects. Empty K, n=0, k=0, zero rows, duplicate
rows, and arbitrary rank are included. No feasibility, enumeration, circuit-
generation, full-rank or diameter premise is assumed.

The source proves extremality using Mathlib's actual open-segment definition,
not a predicate called 'vertex' defined to include the desired conclusion.
Normalization is also proved unique on every positive-circuit support.

This is classical convex geometry, not a new classical theorem or Polynomial
Hirsch. Related exposition: S. Mueller and G. Regensburger, *Elementary vectors
and conformal sums in polyhedral geometry and their relevance for metabolic
pathway analysis*, arXiv:1512.00267. The project contribution is the formal
interface connecting the recent positive-kernel tests to an independently
checkable affine-section catalogue and the accompanying exact lazy constructor.

## Forward proof: circuit implies extreme point

Let x be a positive circuit with total mass one, and suppose

    x=alpha*y+beta*z, alpha>0, beta>0, alpha+beta=1, y,z in K.

Outside support(x), nonnegativity and the strictly positive coefficients force
y and z to vanish. Thus support(y) is contained in support(x). The accepted
#218 ray-uniqueness argument makes x a positive multiple of y. Since both
vectors have mass one, the multiple is one. Therefore y=x, exactly the
extreme-point criterion. This also proves uniqueness of the normalized vector
on any circuit support.

## Reverse proof: extreme point implies circuit

Let x be an extreme point of K, and let y be any nonzero nonnegative null
vector with support contained in support(x). Set

    t=min_{i:y_i>0} x_i/y_i, r=x-t*y.

Then t>0, r>=0, A r=0, and r has strictly smaller support than x. If r=0,
x=t*y, so the supports are equal. Otherwise normalize both y and r to mass
one. Their positive masses give

    x=(t*mass(y))*normalize(y)+mass(r)*normalize(r),
    t*mass(y)+mass(r)=1.

This is a strictly positive convex combination of two points of K. Extremality
forces normalize(y)=x, again giving equality of supports. Crucially y was not
assumed normalized or already minimal. Hence minimality holds against ALL
nonzero nonnegative null vectors.

The pruning and same-support-ray proofs are reused unchanged from accepted
#218. No new Farkas or extremality axiom is introduced.

## Why the new packet is not another conformal-decomposition publication

During the pre-write historical audit, PR #25 was found to have already
published `HirschCircuit.elementary_conformal_decomposition_ambient_bound`,
theorem05726681-715c-408a-b44c-d73dac856b20, submission
9003da2a-48dd-4d30-9e64-a3f4eaf93235. That accepted theorem and its source prove
finite sign-compatible decomposition. The independently prepared duplicate
existence packet was therefore NOT pushed or resubmitted. Normalizing an old
existence result would not justify claiming a new decomposition theorem.

The present public statement instead identifies normalized circuits with
actual geometric vertices. The exact rational reconstruction implementation
is additional software evidence and application of the classical decomposition,
not a new publication of #25. #221 owns support optimality and #222 owns the
rank-plus-one cutoff; neither PR is modified or triggered here. #210 remains
reserved to the user's other agent.

## Catalogue-free exact reconstruction

Given an ALREADY SUPPLIED vector w>=0 with A w=0, the new Python constructor
never enumerates all circuit supports. At a nonzero current residual u, pin
one positive coordinate j. If the signed kernel on support(u) has dimension
more than one, choose a null direction v not proportional to u and form

    v-(v_j/u_j)*u.

Its j coordinate is zero. Choose its sign to have a positive coordinate, and
prune by the exact minimum ratio. The residual remains nonnegative and null,
its support shrinks, and its pinned coordinate remains positive. Repeat until
the restricted kernel is one-dimensional, normalize its positive generator,
and subtract a maximal multiple from the outer residual. Every outer step
also strictly decreases support.

For initial support size s this requires at most s outer removals, s(s-1)/2
inner support reductions, and s(s+1)/2 restricted-nullspace computations.
These are arithmetic-operation counts for the mathematical algorithm. No
strongly polynomial runtime or rational bit-growth bound is claimed here.
The RREF code has NOT been extracted from or verified in Lean.

The independent verifier uses exact SymPy DomainMatrix ranks rather than the
constructor's RREF. For every returned ray it checks positivity, normalization,
original-matrix nullness, and one-dimensional restricted kernel. Those facts
imply minimality: every supported null vector is proportional to the strictly
positive ray. It checks each signed pruning direction, preserved pin, residual,
retired coordinate, total reconstruction, positive coefficient and mass identity.
It never assumes a catalogue is complete. An omitted ray may prevent a
catalogue-based constructor succeeding, but cannot make a false decomposition
pass verification. A retired coordinate is positive in one ray and zero in
all later rays; this proves their linear independence. The numerical verifier
checks that stronger nullity term bound as well. It is NOT the new published
Lean theorem's conclusion.

If a supplied dual witness w has r.w<0, the exact reconstruction forces at
least one returned circuit to have negative r value. The helper returns it.
It does not discover the initial violating witness or prove there are none.
Thus it is a component for lazy separation, not a complete feasibility oracle.

## What remains

The new theorem identifies the correct finite objects, and #222 addresses
their support-size cutoff. A complete Lean refinement of the imperative
rational enumerator, row operations and finite list coverage is still separate.
The new theorem does not turn a partial catalogue into a complete one merely
because each returned vector is valid. Likewise it does not eliminate the
universal original-point tests in #219; #221 separately concerns exact support
budgets. No arbitrary residual edge route or Polynomial Hirsch bound is claimed.

## Reproduction

    python3 scripts/check_positive_circuit_catalogue.py
    python3 scripts/lazy_positive_circuit_decomposition.py --test

For a user-supplied exact rational system, pass JSON containing A,n,vector:

    python3 scripts/lazy_positive_circuit_decomposition.py --input input.json

The publication proof is standalone Mathlib at Lean4.30.0 / Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f. Its public statement preamble contains
only import/open commands, no custom definitions. Four axiom printouts remain
for the hosted final audit. No Lean/Lake executable is available in the originating
container; static checks and Python regressions are not compilation. Only the
actual recorded gate and authenticated verdict can establish acceptance.
