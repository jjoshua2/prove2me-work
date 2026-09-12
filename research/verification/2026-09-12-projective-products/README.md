# Projective hidden-product verification

Source PR #203: original candidate `319a5fa5895939edead917ac307fbf4060d4b2db`;
verified source `6cd06d52fa4bbd832d8eae1eddd85ded9f0bfec9`.

The complete `local-build.log` comes from:

```
lake build Solutions.PolynomialProjectiveRowBlockRouting
```

This transitively builds the segment-chart and perspective modules. The three
source hashes and all 15 required declaration names are in
`local-verification.json`. `check_lean_axiom_log.audit` checks all 28 reports,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.

The single final hosted run
[34710879303](https://github.com/jjoshua2/prove2me-work/actions/runs/34710879303)
passes on that same source commit. `hosted-run.json`, `hosted-build.log` and
`hosted-audit.json` preserve its result and complete normalized build output.

`rational-check.json` is a fresh run of the original finite tests, with unchanged
counts and exact hashes for the three Lean modules, both Python programs, and
the directly imported row-block helper. It retains the 12-dimensional example:
ordinary affine detection finds one excess-12 block, while the certified
projective unshearing finds twelve intervals and an edge bound of 12.
`fixture-certificate.json` records the independently checked committed 4D input.
The regenerated fixture matches the original file byte-for-byte. Finite tests
are regression evidence, not universal geometry or Lean acceptance.

The original candidate receipt remains at
`research/PROJECTIVE_ROW_BLOCK_CHECK_2026-09-12.json`. The runner now accepts
`--receipt` and `--fixture` paths, so reproducing it need not overwrite history.
The existing helper remains unchanged at Git blob c402d2bb993a0e9147b942ff3d914ae0d3f6548b.

`row-blocks.json` and `small-excess.json` are authenticated Proved dependency
snapshots at the committed Mathlib pin. Only the row-block theorem is imported
by the standalone public proof. Publication source, manifest, local driver
audit, statement typecheck, exact submitted proof and server receipts live in
[projective_small_blocks](../../publication_packets/projective_small_blocks/).
