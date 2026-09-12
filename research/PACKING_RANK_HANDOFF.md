# Packing / rank-local continuation handoff

Read `PACKING_UNIVERSALITY_AND_CUT_RANK_2026-09-12.md` first. This is independent
of #205's pending verification and does not modify that branch.

## What to verify and then connect

Three new Lean candidates (460 lines, twelve printed declarations):

```bash
lake build Solutions.PolynomialOrthantPackingNormalization \
  Solutions.PolynomialActiveCutRank Solutions.PolynomialPackingSupportRank
```

No new Lean or Prove2Me verdict exists yet. Repair elaboration locally and
audit the transitive axioms before a hosted gate. These modules import only
existing main interfaces or the new normalization module, not #205.

The full mathematical note additionally proves the simple-vertex preparation,
packing universality consequence, and rank-local route composition. Those
parts are not all new Lean declarations. Their exact remaining adapters are
listed in Section 7; do not replace the geometric premises by assumed routes.

## Run the exact code

Python 3.10+ and the standard library suffice. No package install, credentials,
network, approximate arithmetic, or external optimization tool is used.

```bash
python scripts/test_packing_rank.py --section all
```

The test writes deterministic input/certificate pairs into `research/` for
near-uniform noncubical and Todd models, a dense 32D feedback example, and a
64D rank-two packing example. Generated large JSON fixtures are in the chat
handoff archive and are reproducible from the committed test; only the compact
Todd input is stored separately in the PR. `PACKING_RANK_CHECK_all.json` is the
actual current execution receipt and hashes all eight new code files.

Individual commands after the suite creates the fixtures:

```bash
python scripts/packing_normalization.py research/near_uniform_todd_input.json
python scripts/rank_local_monotone_routes.py research/rank_two_dense_32d_input.json
python scripts/packing_support_routes.py research/rank_two_packing_64d_input.json
```

The programmatic `verify` / `verify_route` functions independently check
supplied certificates without invoking discovery, a linear optimizer, or
vertex enumeration. The routers enumerate only endpoint faces and expose caps;
they are not claimed strongly polynomial algorithms in growing rank.

## The key research correction

Unrestricted positive packing cuts, even with every upper coefficient within
10^-8 of one, can encode every simple-polytope graph. The normalization does
not prove a short route. Approximate rank-one structure is not an easy-case
certificate. Exact low rank is useful: rank-two feedback-box clips have
ordinary diameter <=d+q+4, and rank-two pure packing polytopes <=q+2,
independent of ambient dimension. The proof gives rank-sensitive exponential
bounds for larger rank, not universal Polynomial Hirsch.
