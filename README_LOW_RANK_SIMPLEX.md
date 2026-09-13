# Higher-dimensional summands beyond a segment-free residual

Read `research/LOW_RANK_SIMPLEX_REMOVAL_2026-09-13.md` and its handoff.

`simplex_summand_certificate.py` takes original `A`, `b`, and
`simplex_generators` (independent vectors from an origin vertex), with an
optional feasible `start`. It certifies the exact maximal scalar for removal.

`local_simplex_routes.py` takes only original `A`, `b`, `start`, `end`.
It proposes local simplex shapes, tests each globally, recognizes a
point/pyramid/feedback core when possible, and returns original ordinary edges.
The proposals are not a complete higher-dimensional summand catalogue.

```sh
python3 scripts/local_simplex_routes.py input.json --output result.json
python3 scripts/simplex_summand_certificate.py candidate.json --output result.json
```

For either CLI, `--certificate` expects the inner `certificate` object, not
the full constructor output. Failed local proposals or core recognition
do not prove absence of other summands or large diameter. Exact LP and
enumeration caps are explicit.

The new Lean source is uncompiled. Full Farkas sufficiency and positive-circuit
generation remain stated classical/written dependencies rather than hidden
axioms. Only the reported original edges and certificates were executed here.
