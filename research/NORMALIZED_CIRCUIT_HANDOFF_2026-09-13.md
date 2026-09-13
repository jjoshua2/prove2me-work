# Normalized circuit vertices and catalogue-free reconstruction

## Coordination and scope

Start from main including accepted #216/#218/#219 and receipts #220.
#221 is already the support-optimality proof; #222 is already the rank+1 proof.
Do not duplicate either. #210 remains untouched and untriggered.
A historical audit also found accepted conformal decomposition in #25; no new
copy of that theorem is submitted. The present candidate is instead
`Hirsch.normalized_positive_circuits_iff_extreme_points`.

It proves actual Mathlib geometric extremality in {x>=0:Ax=0,sum x=1} equivalent
to the exact positive-circuit support-minimality predicate. Normalized ray
uniqueness is included as an audited helper. All n,k are permitted, without a
full-rank, nonempty-section, Farkas, feasibility or enumerator assumption.
The proof reuses #218's minimum-ratio pruning and same-support-ray source.

The three rational scripts are test/construction tools, not Lean-extracted code.
They compare the rank-bounded catalogue to independent all-support affine-section
vertices on small instances. The lazy constructor needs NO catalogue, only an
actual nonnegative null input vector, and verifies every returned circuit by
independent signed rank, positivity and exact normalization. Its inner/outer
pruning traces strictly shrink supports and reconstruct the original vector.
Do not claim that validating a returned decomposition proves global catalogue
completeness, or that the tool discovers an initial infeasibility witness.

## Exact reproducibility

    python3 scripts/check_positive_circuit_catalogue.py --output /tmp/catalogue.json
    python3 scripts/lazy_positive_circuit_decomposition.py --test
    lake env lean research/publication_packets/normalized_circuit_vertices/solution.lean

The local container lacks Lean/Lake, so the prepared source has not been locally
compiled. Its signature and source hashes have been checked and both rational
suites actually executed. Use the existing final comment workflow, with no new
workflow or security changes. A failed compile must remain a failed compile;
do not weaken assumptions or keep submitting speculative revisions.

The duplicate rank/decomposition draft proofs were never pushed. The accepted
#25/#216/#218/#219 packets are not resubmitted. Source history and reference to
#222 are not a claim that its platform gate has accepted; read its own status.

## Next exact bridge

After this theorem, normalized-kernel vertex enumeration has an exact geometric
target rather than a separately assumed interpretation. The outstanding formal
algorithm task is to certify the matrix row operations/one-dimensional-nullspace
filter AND that every qualifying support is visited. #222's cutoff can limit
those supports once its own final status is verified. The accompanying lazy
constructor avoids complete support enumeration for a given witness; it does
not replace a complete negative decision for all possible witnesses.
