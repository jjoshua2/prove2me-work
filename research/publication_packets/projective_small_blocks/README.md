# Full finite-certificate projective hidden-product routing

Theorem [b6289eea-78b3-4bcf-a5d7-65fbab46a986](https://prove2.me/theorems/b6289eea-78b3-4bcf-a5d7-65fbab46a986).
Publication job `e712f0e4-55f3-4e80-8fdc-50fae180b13a` is PUBLISHED.
Proof submission `84cf11d7-d965-41c3-96b6-d0f108e8ce2e` is **ACCEPTED**;
`target-after.json` confirms **Proved**. Accepted source readback matches the
packet byte-for-byte. `decompositions.json` records the real row-block input.
Mission comment `940e9078-b248-4385-afa7-2f60bab07663` was read back with all
four intended artifact references. The root and open leaf remain Open.

The statement includes the complete source row partition and linear coordinate
equivalence, a nonempty bounded source, small factor excesses, and both finite
nonnegative denominator certificates. It concludes an ordinary-edge diameter
bound n-d for the sheared target, without a restriction on total excess.
It does not assume graph equivalence or universal projective factorization.
`problem.json` and `explanation.md` give the exact scope and classical attribution.

`manifest.json` freezes source commit 6cd06d52fa4bbd832d8eae1eddd85ded9f0bfec9,
source Git blobs and packet SHA-256 hashes. The proof copies the exact projective
geometry and finite-certificate wrapper from that source. Its only public theorem
input is the already-Proved independent-small-row-block theorem. The local
driver retains its complete proposition explicitly and passes a standard-axiom
audit. The separate public solution uses the platform declaration; its local
placeholder interface is typechecking evidence, not a local proof of that input.

Reproduce without modifying any receipt:

```
python3 scripts/prepare_projective_small_blocks.py --source 6cd06d52fa4bbd832d8eae1eddd85ded9f0bfec9 --out /tmp/reproduced-projective-blocks
lake env lean /tmp/reproduced-projective-blocks/driver.lean
lake build Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_independent_small_row_blocks
lake env lean /tmp/reproduced-projective-blocks/statement.lean
lake env lean /tmp/reproduced-projective-blocks/solution.lean
```

The builder reproduces all six prepared files byte-for-byte. The publisher
checks frozen hashes, driver/composition receipts, exact live dependency types,
Proved status, environment pin, and skill version before publication. It refuses
to duplicate an existing registration or proof request. Only authenticated
server receipts establish platform acceptance.
