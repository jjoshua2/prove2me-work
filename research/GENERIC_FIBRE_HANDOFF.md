# Fibre path continuation: accepted genericity and compiled crossing geometry

## Completed in PR #242

Public theorem `Hirsch.generic_fibre_objectives_without_independent_ties`, theorem `d323320e-6843-4743-a2ea-e46b770cb3c8`, submission `4ac637cb-f9c4-47fe-9bc2-8d435e539177`, is ACCEPTED with authenticated publisher live Proved. Run `34798475975` froze proof `0e9c7ad7ea0e46623df0718564f0917ac50f027a`. See `publication_packets/generic_fibre_objectives/accepted-evidence.md` and the unchanged raw publication receipt. Do not resubmit.

The 165-line source retains the previous local proof commands and target exactly. Only the prose word that tripped the raw admission scanner was changed. The first run `34798001787` stopped before Lean; the first actual compile and first actual platform submission passed. All three compile exits are zero, and all five printed declarations use only standard logical axioms. Two artifact archive hashes and all five file hashes were independently checked. This is hosted pinned compilation; local Lean/Lake remains unavailable.

The new 199-line `Solutions/PolynomialEnvelopeCrossingEdges.lean` compiles at `ad42bf00ef2d5b79ae6211529cba4efedbc97066` in module-only run `34799074798`. Source blob `3c3695a01b2e7b0474c86111184c01c2dea53649`, SHA-256 `ecae31b8419bea9deb98ebd4fc4ba676c300cb6f5747dabd527095a92f455858`. Its first run exposed two elaboration sites, repaired directly without statement changes. The exact patch and failed diagnostic are retained. The successful module artifact records `built`; the trusted builder discards successful stdout, so the module does NOT have an independently observed printed-axiom audit or separate platform verdict. Do not transfer the genericity packet's audit to it.

## Actual mathematical connection

The genericity theorem constructs endpoint-preserving f,g for a finite list of nonzero differences. For every nonparallel pair d,e, f(d)g(e)-f(e)g(d) is nonzero. Thus no point of the entire affine objective line can tie two independent directions. Common strict core comparisons remain strict on the closed interval. Empty index types and arbitrary real vector spaces are covered.

`HirschEnvelopeCrossing.crossing_support_segments` derives the ENTIRE support segment in each finite hull from left/wall/right maximizing comparisons and a common tie line. `affine_crossing_exposed_edge` chooses a genuinely changed factor, orients its difference by the left/right objectives, proves every other change has a nonnegative parallel length, and proves the chosen factor has length one. Consequently the total segment is nondegenerate. It constructs both the global supporting-slice equality and actual `Hirsch.Adj`, rather than assuming either. It reuses the integrated Minkowski support assembler.

These results now supply genericity and per-event geometry for #239's accepted affine-envelope counting certificate. They do not yet instantiate the generic finite difference index, select/sort all crossing times, prove winners persist on each intervening interval, delete stationary repetitions and concatenate the resulting route. That finite assembly is the next exact formal target, not another genericity/bridge theorem.

## Reproducibility

Both original exact scripts are committed unchanged: `scripts/deterministic_fibre_path.py` blob `53acc03f022d6d9a8111a9d0ae411cecc7dbfddf` and `scripts/test_deterministic_fibre_path.py` blob `d21c26f4ac109b27168c9ca079cd2763819e3c5e`. The current raw regression is `verification/generic-fibre-current/exact-tests.json`. A clean-directory replay reproduced it and both 32D fixture files byte-for-byte; independent serialized verification passed.

Run:

    python3 scripts/test_deterministic_fibre_path.py --out /tmp/fibre-check.json --fixtures /tmp/fibre-fixtures
    python3 scripts/deterministic_fibre_path.py /tmp/fibre-fixtures/fibre-32d-input.json --certificate /tmp/fibre-fixtures/fibre-32d-certificate.json

Evidence: 85 paths/103 edges, 82 independent complete point-sum audits, 3465 edge/tuple checks, 3178 component-face checks, 8 valid parallel crossings and 17 rejected controls. The 32D simplex-core/24-triangle case has 24 fibre edges and budget 48, with no enumeration of its 9,320,174,703,873 raw point tuples. This is not a distinct-vertex count or shortest-path claim. Python/JSON is not Lean-extracted; the finite constructor takes a supplied decomposition and strictly exposed endpoints, not arbitrary original H-data.

## Live ownership and remaining conjecture gap

Read current main STATUS, live PR heads/comments and receipts before starting. Accepted #239 supplies the finite count; accepted #240 supplies exposed core-edge bridges. Neither needs another submission. #238 owns support-witness existence and #241 owns bounded-image representatives. #208's existing pending submission is not duplicated; retired/reserved #210 is untouched.

For an actual decomposition with core route L and factor budget K, the written full lift bound is L+(L+1)K. Proving a polynomial bound for arbitrary high-dimensional carriers still requires controlled decompositions or another geometric routing method. No universal decomposition, finite-catalogue-size bound, or Polynomial Hirsch proof is claimed. This update did not change pins, workflows, allowlists or secret separation. Root/leaf status is from the last preserved authenticated audit, not a fresh direct platform poll.
