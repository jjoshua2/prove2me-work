# Proof idea

For the forward implication, fix a certified group `I` and an edge `e`. Because all scales and edge lengths are nonnegative, restricting the full sum to `I` can only decrease it. The global capacity inequality therefore implies the group inequality.

For the reverse implication, the cover hypothesis gives a group `I` containing every index with nonzero edge contribution. Hence the full weighted edge sum is exactly the sum over `I`; the corresponding group inequality is therefore the global inequality for that edge.

This theorem is only the finite budget identity. The geometric fact used elsewhere in PR #210—that all nonzero Minkowski candidate contributions on one parent edge belong to a common direction group—is intentionally not hidden inside this standalone statement.
