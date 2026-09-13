# Implicit-base wall-refinement routes

Start with `research/IMPLICIT_WALL_REFINEMENT_2026-09-13.md` and its handoff.
Run `python3 scripts/test_implicit_minkowski_lift.py` to regenerate all stages,
large input/route fixtures, and the source-hashed receipt.

The standalone constructor accepts `A`, `b`, `base_route`, `summands`,
`source_weights`, and `target_weights`:

```
python3 scripts/implicit_minkowski_lift.py input.json --output result.json
```

The two weights arrays are nonnegative multipliers of original H-rows certifying
the endpoint objectives. The supplied parent route is checked; it is not found
by an unspecified oracle. The output contains `certificate` and `verified`.
The `--certificate` option expects the inner certificate object, not the wrapper.

A route with L parent edges and q added comparison directions lifts to at most
L+(L+1)q ordinary edges. This needs neither the full parent vertex graph nor its
edge-direction list, and tolerates genuinely thin final normal cones.
The separate B+5q analytic existence result is not the implemented sampler.

Two Lean files remain uncompiled candidates. No platform acceptance is claimed.
