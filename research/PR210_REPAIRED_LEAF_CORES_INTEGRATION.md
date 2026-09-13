# Integrate the repaired source modules excluded by #231

This is an exact-blob integration of existing, successfully compiled #210 code.
No mathematical proof is edited or newly claimed here. It is unrelated to the
covering-allocation candidate whose commit was blocked in this continuation;
that candidate is NOT present in this tree or branch.

#231 integrated the three previously classified modules at merge
4e9772da71345462d37e65ca7e0b89f5f0474f90. Its original description excluded two
files because the classification run had failed on their older revisions.
Later repairs of both files passed their own module-only verification runs:

| Module | Exact checked source commit | Original source blob | Run |
|---|---|---|---|
| Solutions.PolynomialSeparatedFacetStars | d53b5bd8b3355cc7a752906df520d0a2afef14c0 | 17fcd7cc6759a33ff5cdd237b86a1106413863aa | 34786034557 |
| Solutions.PolynomialSimplexLiftObstructions | 11172b1165b31a81e8755bd9f88651a2a9ed4b8c | f5fe3019865087be6d4fcce3e8d7a3b38c58dc3b | 34786092344 |

The current read of both runs reports gate, verify, artifact upload and
report-verify SUCCESS, with publication SKIPPED. These are module compile
results, not new Prove2Me submissions or acceptance receipts. The source files
are copied by their original Git blob identifiers, not retyped or weakened.
Both import Mathlib only and retain the committed Lean/Mathlib pin.

PolynomialSeparatedFacetStars proves scalar source/target facet separation and
the exact diagonal-interval membership model of the spread box. It does not
formalize its entire face lattice or prove every routing obstruction claimed
in older prose notes. PolynomialSimplexLiftObstructions proves actual lifted
set-membership equivalence, erosion inclusion, finite scalar obstructions and
a negative-kernel infeasibility certificate; its own sufficiency/complete
catalogue interfaces remain separate from these finite cores.

Historical comments saying NEW UNCOMPILED in the files describe their creation
state. The source is deliberately unchanged; the later successful run IDs above
supersede that compilation status, not the stated mathematical scope.

A single fresh module-only gate on the clean integration checks both exact
blobs against current main. It does not execute candidate Python, publish a
packet, or alter workflows, credentials, permissions or theorem statements.
Keep any resulting run evidence distinct from platform acceptance.
