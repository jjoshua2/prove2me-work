# Complete segment discovery from original inequalities

Read `research/ANTIPODAL_SEGMENT_DISCOVERY_2026-09-13.md` and its handoff.
Input to the end-to-end constructor is only `A`, `b`, `start`, and `end`:

```sh
python3 scripts/automatic_segment_routes.py input.json --output result.json
```

For complete factor discovery without requiring a recognized residual route:

```sh
python3 scripts/antipodal_segment_catalogue.py input.json --output catalogue.json
```

The output contains `certificate` and `verified`; the CLI `--certificate`
expects the inner certificate object. The catalogue uses a certified antipodal
ordinary-edge walk, checks every walk direction by the preceding capacity test,
and proves its residual is segment-free in every direction. It does not imply
that the residual has no higher-dimensional Minkowski summand.

No directions, generators, parent route or affine chart are supplied. Search
caps and potentially long simplex paths are explicit; no uniform polynomial
runtime is claimed. The integrated solver recognizes point, pyramid and a
sufficient feedback class, not every possible residual.

Run `python3 scripts/test_antipodal_catalogue.py` to regenerate the full exact
suite. The package includes unchanged dependencies for standalone execution;
they are not modifications in the incremental patch. The new Lean module is
an uncompiled candidate, not a platform-accepted theorem.
