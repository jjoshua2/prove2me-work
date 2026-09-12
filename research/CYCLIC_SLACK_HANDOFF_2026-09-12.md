# Verification-agent handoff: fixed slack fails, adaptive mass conservation works

Continue PR #208; do not open another overlapping accounting PR. The previous
#208 code remains unchanged. The two new Python files reuse its exact optimizer
and verifier; the two new Lean files import only Mathlib or Def_Hirsch_model.
They do not need #206/#207 to compile. All NEW sources are uncompiled candidates.

## Result to preserve

For any fixed even d>=4 and fixed k,b, take n=2m with m>=k+d+3 and n-d>b.
On the explicit centered moment-curve polar, opposite consecutive-block
endpoints have exact minimum CHILD EXCESS2(n-d) in the k-slack first-edge/
available-facet repair family. Hence this cannot meet e+b. This is NOT an
edge-distance lower bound, NOT a failure of all radial certificates, and NOT
a refutation of bounded spill when detour slack is allowed to grow.

The proof's key fact is geometric: a free matching edge outside the common
signature permits a matching extension covering every original row, so the
actual carrier excess is exactly n-d. All sub-full-excess transitions move
active row supports by at most one around the n-cycle. A chain with at most
one full-excess jump cannot bridge supports farther apart than its length.

The positive route slides a block of d consecutive rows. Its actual length is
n/2 and child excess n/2-1<=n-d. It uses slack n/2-3, within d-1 of the proved
necessary slack for child mass<2e. Every step is an ordinary edge with shared
active rank d-1. Large certificates are constructed directly from supporting
polynomials, without all-vertex enumeration.

## Commands and scopes

```sh
python3 scripts/test_cyclic_slack_obstruction.py
python3 scripts/cyclic_slack_obstruction.py \
  --facets 40 --dimension 8 --slack 4 --allowance 2 \
  --output /tmp/cyclic-40d8.json
lake build Solutions.PolynomialTransportHeavyJumps \
  Solutions.PolynomialSupportingSlackCertificates
```

No Lean/Lake executable was present in the originating container. Inspect all
nine new axiom printouts after local compilation. API-sensitive points are
Finset.card_le_one and sum-subset lemmas, indexed chain induction, and vector
`module` calculations in the supporting-kernel proof. Preserve all retained-row,
metric, nonempty-signature, active-kernel and endpoint-slack assumptions.

The generic transport theorem is formalized as a candidate, but the complete
cyclic application and matching augmentation are in the mathematical note,
not silently counted as Lean-compiled. The numerical constructor consumes the
specific known moment-curve family; it is not a recognizer for arbitrary H-data.
The full original H-rows are checked on large returned routes. Matching-derived
large vertex-count formulas are mathematical counts, not enumerated data.

The test receipt gives actual arithmetic/graph counts and both reused source
hashes. Generated full fixtures are in the ZIP and reproducible from the script.
The PR needs only the new source, note, handoff and receipt. Do not overwrite
old #208 files or change old proof dependencies to absorb the new examples.
Publication, if appropriate after formalization, needs its own honest exact
interface and authenticated verdict. No platform mutation was made here.
