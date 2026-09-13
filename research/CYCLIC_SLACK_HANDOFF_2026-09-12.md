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


## Verification continuation (supersedes candidate-only status above)

The continued #208 source is frozen at b7a832e9ff98743d53c66d6e471fd0828891d22d. All six Lean modules compile locally; all 20 required declarations and 291 transitive axiom reports pass the standard-axiom audit. The exact portal-detour and cyclic-slack suites were rerun after the elaboration repairs and pass. See `verification/2026-09-12-additive-spill/` for logs and the compact source-hash audit. The final hosted gate is run 34725721217 at 418e7a4158b54212a43df0bec9b11e40506066da; its final verdict is recorded in the durable receipt and STATUS.md.

The public packet `publication_packets/additive_portal_repair/` isolates the conditional additive-spill route theorem with a named finite repair definition. It proves an actual route and cost at most C*e+(1+b*C)*h*(e-b), assuming the explicit repair tree, dimension drop, child monotonicity, sibling budget, and certified leaf routes. Numerical tags alone do not assert intrinsic geometric dimensions/excesses. The infinite cyclic obstruction and adaptive geometric construction remain mathematical-note results with exact finite regression checks; compiling their transport and supporting-kernel components does not formalize every step of that infinite argument.
