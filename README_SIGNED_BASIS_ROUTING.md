# Signed two-variable carrier routing

Start with `research/SIGNED_BASIS_ROUTING_2026-09-12.md` and the adjacent handoff.
Run `python3 scripts/test_signed_basis_shadow.py` to regenerate all fixtures and
the executed source-hashed receipt. The constructor takes original rational
`A`, `b`, `start`, and `end` fields. For a route, run:

```
python3 scripts/signed_basis_shadow.py problem.json --output certificate.json
```

An output wrapper contains both `certificate` and `verified`. The independent
CLI `--certificate` input expects just the inner `certificate` object. The test
fixtures also retain the full original input and the output wrapper.

Two Lean modules are uncompiled candidates, not accepted platform theorems.
The stated ordinary-edge diameter follows mathematically from the explicit
signed inverse proof and the cited classical wide-normal-cone theorem. The
current exact sampler is not a certified implementation of that theorem's
expected-length distribution; successful routes are checked independently.
