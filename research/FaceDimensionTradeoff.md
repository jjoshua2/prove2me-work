# Verified common-face dimension tradeoff

This branch preserves the Lean-verified result from commit `5de07bab34fb6549b9b3b4ee2ff3583a28038c5d`.

For separated extreme endpoints `u,v` and any intermediate extreme vertex `x`, the overlap of the common-direction spaces is controlled by the neutral rows, giving

`dim F(u,x) + dim F(v,x) <= d + (n - 2*d)`.

At exact balance `n=2*d`, this becomes the complementary bound

`dim F(u,x) + dim F(v,x) <= d`.

The same file proves a boundary-access splitter: to reach a point whose target-common face has dimension at most `d + (n - 2*d) - R`, it is enough to control graph diameter only in dimensions at most `R-1`.

GitHub Actions run `34287012631` completed successfully in Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. The audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appears.

This is a structural lemma, not a proof of Polynomial Hirsch.
