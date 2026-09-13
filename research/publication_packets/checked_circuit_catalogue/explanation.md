# A finite rational checker certifies every emitted AND omitted circuit support

## Mathematical target

For a rational matrix A with k rows and n columns, the source defines a finite
Boolean `check` and a rational output `catalogue`. It proves:

    check(A, table)=true
      => {real normalized positive circuits of A} = cast_to_real(catalogue(A, table)).

Normalization is sum(x)=1. Positive-circuit minimality is quantified against
ALL nonzero nonnegative real null vectors. It is not restricted to rational
vectors, preselected candidates, or already-normalized vectors.

The checker receives only finite rational matrix/vector data. It assumes no
RREF correctness, rank oracle, search completeness, feasibility or extremality
oracle. The algorithm may produce nonsense; an invalid arithmetic witness
must fail the Boolean check. It is the CHECKER whose generic correctness is
formalized, not every implementation detail or runtime of the producer.

The normalized-circuit/extreme-point theorem from #224 identifies these outputs
with the actual vertices of {x>=0:Ax=0,sum(x)=1}. They are multiplier-section
vertices, not vertices of the original Hirsch polytope. No new original-edge
diameter bound is asserted.

## Every support has a certificate

Enumerate U={S subset {0,...,n-1}: |S|<=k+1}, including the empty support.
The Lean definition forms `powersetCard` for each relevant cardinality and
unions the results; it does not generate the whole powerset and then count
only the retained supports. The count is sum_{j=0}^{min(n,k+1)} binomial(n,j).
This is polynomial in n for fixed k, not for unrestricted k.

For each support S, let D_S=[A_S; ones]. Exactly one of two certificate types
is used. Neither branch trusts an asserted rank or an elimination transcript.

1. **Dependent columns.** Supply nonzero z supported in S with A z=0 and
   sum(z)=0. These are finite rational zero checks. Such an S cannot be the
   full support of a normalized positive circuit: #222 makes every signed
   supported null vector proportional to that circuit, and the zero mass then
   forces the proportion and z to be zero, a contradiction.

2. **Independent columns.** Supply a left inverse L_S D_S=I_S. It is checked
   entry by entry using the ORIGINAL A. Let e be the last unit vector and
   c_S=L_S e, padded by zero outside S. Any supported normalized null vector
   must be c_S. Emit c_S precisely when it has positive entries on every index
   of S, A c_S=0, and total mass one. If these checks fail, no normalized
   positive circuit can have that exact support. A left inverse alone does
   not imply D_S theta=e is feasible; the original equations are checked again.

Full-column-rank D_S has a rational left inverse; otherwise it has a nonzero
rational null vector. The producer constructs these using exact elimination,
but the checker never calls elimination. For completeness of the output,
the only infinite-dimensional-looking issue is real x; rational identities
are cast into the reals and applied to arbitrary supported real vectors.

## Formal completeness and soundness

The source copies the two signed-ray/rank helper proofs from ACCEPTED #222
verbatim, not a sorry-based target import. Their original whole-source digest
is 5360f2a04a68b580552470ba42d1fa011eec5a73275c1c9b7766475fea028ddc.
The downloaded verified archive was checked against its published ZIP digest.

For any normalized real circuit x, #222 gives

    |support(x)| <= rank(A)+1 <= k+1.

Thus its support is actually visited by U; the cutoff is proved, not a claimed
property of the Python table. The dependent branch is impossible by the
zero-mass argument above. The finite left-inverse identities imply

    y_i = (L_S)_{i,last} * sum(y)

for EVERY supported real null vector y. Taking y=x reconstructs the exact
emitted rational vector. This proves nothing has been omitted.

Conversely an emitted c_S is nonnegative, null and normalized by direct tests.
For any nonzero nonnegative null y supported on c_S, the same identity makes
y=sum(y)*c_S. That scalar is nonzero, so the supports are equal. Thus each
emitted vector is genuinely a positive circuit, not merely a feasible point.

The generic theorem uses a Boolean computed from finite rational predicates.
It also includes three `by decide` examples that run in Lean's kernel: a
passing table with both kinds of cells; exact catalogue cardinality three;
and a rejected all-zero forged table. There is no native_decide or new axiom.
The small exported example is A=(1,1,-1,0), so its circuits are the zero-column
unit vector and the two positive half/half cancellations.

## Concrete certificate format and independent testing

The companion producer stores each support explicitly, a branch tag, and
only the relevant left matrix or null vector. The verifier recomputes the
ENTIRE expected bounded-support sequence before reading cells, rejects missing,
duplicate and reordered supports, and checks all coefficient identities.
Implicit zeros outside the stored support match the Lean table's padding.
The output list is re-derived by the exact positive/feasible/normalized filter;
missing or additional output vectors are rejected even if the table passes.

Small tests independently enumerate all supports of ALL sizes using SymPy's
augmented affine systems, without relying on the new cutoff or constructor.
They cover empty dimensions, zero/duplicate rows, positive-kernel emptiness,
dependent columns, rational near-resonance, and equivalent row transformations.
The test temporarily replaces the constructor's RREF/inverse functions with
raising stubs and confirms that audit still works. A noncanonical but valid
left inverse is accepted and produces the same catalogue, rather than requiring
an incidental pivot convention. Negative cases corrupt both certificate types,
support coverage, normalization, output, the original matrix, and numeric types.
The exact executed counts and source digests are in CHECKED_CIRCUIT_CATALOGUE_TESTS.json.

Python is NOT Lean-extracted; neither its JSON parser nor arbitrary future
versions are automatically trusted by the theorem. The supplied finite data
can be exported to Lean definitions and audited using the actual Lean checker.
The checked concrete example is generated from the Python table but is
independently recomputed by `decide` in the proof source. False exported data
would fail that check. General producer termination and rational bit complexity
are separate from checker soundness and output completeness.

## Scope and coordination

#221 support exactness and #222 rank cutoff are accepted; #227 owns their
allocation-budget composition. This work does not duplicate them. #224's
registration was safely resumed by the other agent and now reports ACCEPTED;
no duplicate publication was issued. Its geometric interpretation is useful
but is not imported as an axiom by this standalone rational checker proof.
No #210/225/226 source changes are needed. Existing compiler/secret separation,
Lean 4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f stay unchanged.

The remaining global mathematical gap is not disguised: certified circuit
catalogues and support budgets validate decompositions for supplied shapes;
they do not discover universally useful shapes or route arbitrary residual
carriers. Polynomial Hirsch is not proved by this checker.

## Reproduction

    python3 scripts/test_checked_circuit_catalogue.py
    python3 scripts/checked_circuit_catalogue.py input.json --output table.json
    lake env lean research/publication_packets/checked_circuit_catalogue/solution.lean

Input JSON has `A` and `n`; entries must be integers or rational strings.
The originating container has no Lean/Lake and its public toolchain probe failed
DNS. Do not label source checks or Python tests as Lean compilation. The new
packet's actual final compile/audit/publication result must be read separately.
