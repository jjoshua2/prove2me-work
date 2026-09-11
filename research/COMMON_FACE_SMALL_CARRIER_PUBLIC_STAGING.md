# Common-face small-carrier publication staging

The compact public driver passed the pinned Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` gate in run `34630858124`, job `103367056989`. Its only public theorem depends on `propext`, `Classical.choice`, and `Quot.sound`.

The one-shot publication gate rechecks those exact proof bytes, generates a root-level `theorem solution`, authenticates Prove2Me, verifies the exact already-Proved small-excess and common-face-transport theorem records, and only then attempts publication. No Open theorem, sketch, or conjectural child is imported.

This update changes no Lean proof bytes; it triggers the main-branch publication workflow after PR #109 was retargeted to `main`.
