# Current Prove2Me Hirsch frontier

Date: 2026-09-06. Repo: `jjoshua2/prove2me-work`.

Santos is **done on the public platform**. Do not keep proving
`spindle_one_step_axis` / wedge children as mission blockers.

## Proved (do not redo)

Linear Hirsch counterexample path, all Proved:

- `Hirsch.q28_*` certificate stack through `q28_polar_no_length_five_walk`
- `Hirsch.five_spindle_length_six`
- `Hirsch.spindle_normalize`, `spindle_one_step_axis`,
  `spindle_one_step_from_apex_facet`, `spindle_one_step`,
  `strong_dstep_spindle`
- `Hirsch.santos_counterexample`

Also Proved and used by the remaining polynomial reduction:

- `Hirsch.balanced_hpoly_transfer`
- `Hirsch.diameter_bound_of_target_face_access`
- `Hirsch.nonzero_supporting_row_of_distinct_extremes`
- `Hirsch.vertex_tight_rows_span`
- Kalai–Kleitman / Larman / Todd (quasi-polynomial or exponential; **not**
  a polynomial `(n+d)^k` bound)

Axis scratch in `Solutions/Axis*.lean` is leftover geometry from before
Santos closed. Keep it if useful; it is not an open mission leaf.

## Open (4 theorems, 1 leaf)

```
polynomial_hirsch_conjecture          SKETCH → balanced_hpoly_transfer (Proved)
                                           + balanced_polynomial_bound (Open)
balanced_polynomial_bound             SKETCH → polynomial_target_face_access (Open)
                                           + diameter_bound_of_target_face_access (Proved)
polynomial_target_face_access         SKETCH → nonzero_supporting_row (Proved)
                                           + polynomial_access_to_given_supporting_face (Open)
polynomial_access_to_given_supporting_face   OPEN LEAF
```

The only theorem that still needs a real proof is

**`Hirsch.polynomial_access_to_given_supporting_face`**
(`33fc334e-e05b-4090-ac49-f83fd94d9305`).

That is Kalai’s polynomial Hirsch conjecture, restated as: from vertex `u`,
reach *some* vertex `z` on a *specified* supporting hyperplane of the target
`v`, in at most `C(n+d)^k` edge steps, with `C,k` independent of `d,n`.

Do **not** fake-prove it from Kalai–Kleitman (`n^{log d}`) or Larman
(`n 2^{d-3}`). Those are the wrong growth. `graph_connected_general` gives
*some* walk, not a polynomial budget.

Env: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Credentials stay in gitignored `credentials.json`.
