# Recover a routable coarse core from final inequalities

Read `research/SEGMENT_PEELING_FROM_H_2026-09-13.md` and its adjacent handoff.
The input has only `A`, `b`, `start`, `end`, and `candidate_directions`:

```sh
python3 scripts/recognized_segment_routes.py input.json --output result.json
```

The algorithm discovers maximal removable segments with global Farkas certificates,
recognizes a sufficient affine positive-feedback core, and constructs edges of
the ORIGINAL H-polytope. Candidate directions are supplied; lengths, the parent
polytope, its coordinate chart and parent route are not.

`hpoly_segment_peeling.py` performs standalone extraction without demanding a
recognized core. The `--certificate` verifier expects the inner certificate
field of the constructor's output, not the entire result wrapper.

Run `python3 scripts/test_segment_peeling.py` to regenerate exact tests and
fixtures. The unchanged previous `implicit_minkowski_lift.py` is a dependency;
it is bundled for standalone use, not modified by the incremental patch.
The two new Lean files remain uncompiled candidates. Neither universal
recognition nor a polynomial pivot bound for exact simplex is claimed.
