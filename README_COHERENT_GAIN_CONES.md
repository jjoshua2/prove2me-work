# Coherent gain-cone continuation

Read `research/COHERENT_GAIN_ROUTING_2026-09-12.md` and its verification handoff.
Run `python3 scripts/test_coherent_gain_cones.py` for exact regeneration.

The route constructor accepts original rational `A`, `b`, `start`, and `end`:

```sh
python3 scripts/coherent_gain_cones.py input.json --output result.json
```

Do not supply `gain_base`: this certificate requires no common gain lattice.
The `--certificate` verifier expects the inner `certificate` field of the output.
The bundled three older gain/shadow scripts are unchanged dependencies and are
not additions in the incremental Git patch.

The support graph may contain dense balanced blocks. Nonunit gain cycles must
be coherently directed isolated blocks. Their total multiplicative transport
controls cone width, but their minimum distance from gain one does not enter.
The ordinary-edge diameter consequence uses a cited classical analytic theorem.
The two new Lean files are uncompiled candidates, not platform-accepted theorems.
