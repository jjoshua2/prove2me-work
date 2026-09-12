# Simultaneous clipping used-label verification — 2026-09-12

Frozen head `c5bb370f625d91af93da6510854eb944dfabaac7` passed the focused pinned Lean gate in Actions run `34690671378`, job `103545243900`, under Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The build completed successfully. Audited declarations:

- `HirschRadial.clipUsedRegionCost` — no axioms;
- `HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes_used_labels` — only `propext`, `Classical.choice`, `Quot.sound`.

## Formal result

For one specified outer edge/stay route of padded length `D`, radial simultaneous-clipping repair now returns the actual simple list of repair-region labels selected by the connected-region proof. The list is `Nodup`, and the output parent-edge route has exactly the sum of local costs on those labels.

The label type distinguishes:

- final cut faces, charged by the supplied `B i`;
- old-route edge regions indexed by `Fin D`, charged one;
- endpoint singleton regions, charged zero.

This is path-sensitive infrastructure. It does not yet project to cut labels only and therefore does not itself state `D + sum_{used cuts} B i`. The next checked layer performs that combinatorial projection.

No Prove2Me mutation or credential use occurred. No global polynomial bound is claimed.
