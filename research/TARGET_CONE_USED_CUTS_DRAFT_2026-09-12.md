# Target-cone used-cut reinsertion — verification target

This branch specializes the kernel-verified path-sensitive simultaneous-clipping theorem to the target-tight compact star outer model.

For target-slack batch `J`, the candidate theorem returns a separate `Nodup List J` for each repaired route:

- arbitrary final vertex pair: budget `2 + sum_{i in usedCuts} B i`;
- target root to a final vertex: budget `1 + sum_{i in usedCuts} B i`.

The theorem does not claim a polynomial bound on the selected face budgets and does not globally de-duplicate row usage across multiple repaired routes. It is intended as the path-sensitive accounting interface for the current batch-reinsertion frontier.

This file is documentation only and triggers the focused Lean/axiom gate. Treat the target-cone specialization as unverified until that gate succeeds. No Prove2Me mutation is part of this gate.
