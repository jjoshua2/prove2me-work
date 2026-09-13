# Quantized gain-cycle continuation

Start with `research/GAIN_LATTICE_ROUTING_2026-09-12.md` and its adjacent handoff.
The new scripts reuse the unchanged `scripts/signed_basis_shadow.py` from PR #210.
The downloadable package includes that dependency for standalone execution; it
is not changed by the add-only patch or repository commit.

Input to `gain_shadow_extension.py` is an exact JSON object with `A`, `b`,
`start`, `end`, and optionally `gain_base`. A supplied base requests the global
gain-lattice certificate. Without it, the constructor may return an exact route
for arbitrary rational two-variable rows, but no uniform polynomial bound.

```sh
python3 scripts/test_gain_lattice_routing.py
python3 scripts/gain_shadow_extension.py problem.json --output result.json
```

The output contains `certificate` and `verified`. The `--certificate` option
expects the inner certificate object, not the wrapper. Test fixtures retain
both the original input and output for reproducibility.

The analytic diameter consequence is a derived application of a classical
normal-cone theorem. The sampler's runtime and the lengths it happens to return
are separate from that existence bound. New Lean sources are uncompiled
candidates, not accepted Prove2Me theorems.
