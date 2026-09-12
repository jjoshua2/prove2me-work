# Simultaneous clipping: used-label verification target

This branch isolates a path-sensitive refinement of the already-verified simultaneous-clipping repair.

The new theorem returns the actual simple `Nodup` list of repair-region labels chosen by the intersection-graph route. Its exact route length is the sum of the corresponding local costs. Region labels distinguish:

- final cut faces, cost `B i`;
- old-walk edge regions, unit cost;
- endpoint singleton regions, zero cost.

The first used-label theorem is kernel-verified and integrated. The current child theorem projects only the cut labels. Since the complete label list is `Nodup`, the old-edge labels are distinct elements of `Fin D`, so their total unit charge is at most `D`. Its target route budget is

```text
D + sum_{i in usedCuts} B i
```

for a `Nodup` list `usedCuts`, rather than charging every available cut face.

This edit is documentation-only and triggers the focused child verification gate. Treat the cut-only theorem as unverified until that Lean/axiom gate succeeds. No Prove2Me mutation is part of this branch yet.
