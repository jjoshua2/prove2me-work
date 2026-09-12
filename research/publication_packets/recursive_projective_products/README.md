# Recursive projective product routing publication

Theorem [4afd7668-51a9-4a5e-a991-2a02c53b9e1c](https://prove2.me/theorems/4afd7668-51a9-4a5e-a991-2a02c53b9e1c) is **Proved**.
Submission `7f2bba60-85ad-42d5-8a1a-eed656add3f5` is **ACCEPTED**.
Definition `3c29c70d-337c-4d63-8f52-9c437f52e878` and accepted source readbacks
match the packet byte-for-byte. The authenticated decomposition records the
small-excess input and geometric definition. Mission comment
`34e388c1-afb6-412e-85c0-366096816186` was read back with all five intended
artifact references. The root and common-face open leaf remain Open.

Frozen source: `fcbb02425dececaa9a8f7abd90c341ae99dbafac`.
The standalone definition has geometric constructors only. The theorem derives
ordinary-edge diameter at most n-d by induction, using the already-Proved
excess-at-most-three theorem as its only imported diameter input. Distinct
nodes may use distinct positive projective charts.

The local explicit-premise driver passes its standard-axiom audit. The public
statement and solution typecheck, with the imported theorem interface treated
as a placeholder only for that local composition check. Acceptance is tracked
in the authenticated publication/verification receipts; do not infer it from
a local build. Full chart-search completeness and JSON proof-term generation
are outside this theorem.

Reproduce the seven prepared files and manifest byte-for-byte:

```
python3 scripts/prepare_recursive_projective_products.py --source fcbb02425dececaa9a8f7abd90c341ae99dbafac --out /tmp/recursive-projective-packet
lake build Definitions.Def_Hirsch_recursive_projective_products Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_rows_le_dim_add_three
lake env lean /tmp/recursive-projective-packet/driver.lean
lake env lean /tmp/recursive-projective-packet/statement.lean
lake env lean /tmp/recursive-projective-packet/solution.lean
```

The publisher verifies frozen hashes and local receipts and refuses duplicate
publication or verification requests. Poll existing jobs rather than resubmitting.
