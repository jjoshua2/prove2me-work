# Finite nonsegment summands from original inequalities

Start with `research/FINITE_SUMMAND_PACKING_2026-09-13.md` and its handoff.
Developed from 4b82eedf; integrated above concurrent simplex work at e6f5baa8.
The independent-generator simplex recognizer and local shape proposals remain
unchanged. The distinct extension here includes arbitrary finite point lists
and the complete joint packing region for multiple candidate shapes.

Single-candidate input has `A`, `b`, `candidate_vertices`, and optionally `start`:

```
python3 scripts/finite_summand_capacity.py problem.json --output capacity.json
```

For a route, also give `start` and `end`:

```
python3 scripts/recognized_finite_summand_routes.py problem.json --output route.json
```

Joint-region input has `A`, `b`, `candidate_shapes`, optional `start`, and optional
`scale_objective`:

```
python3 scripts/joint_summand_region.py candidates.json --output region.json
```

A candidate SHAPE is supplied; scale, exact erosion, core and route are discovered.
First-point translations are normalized away with the residual convention stated
in the proof. The `--certificate` options expect the inner certificate object.
The joint module also exports independent `verify_region` and `verify_scales`.

Run the staged `test_finite_summand_capacity.py` suite to regenerate fixtures and
hash-bound receipts. Old solver files in the download are unchanged dependencies,
not modifications in the incremental patch. New Lean modules are uncompiled
candidates. No universal shape discovery or polynomial simplex pivot bound is
claimed.
