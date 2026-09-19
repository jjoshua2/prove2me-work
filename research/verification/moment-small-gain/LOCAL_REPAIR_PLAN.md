# Required local repair work — not a verified patch

The first hosted gate reached actual pinned Lean and failed. The complete
solution remains exactly the gated source; no second command is requested.
The excerpt and first-gate.json identify the actual failing groups. None of the
five printed new declarations passed the transitive audit. In particular the
failed nodes_injective name in the output is NOT permission to add an axiom.

The following are implementation directions, not a claim of a ready repair.

1. At nodes_injective and slack_spec, split the finite-case simplification into
   stages rather than visiting an explicit goal location after simplification
   has already discharged it. Prove finite-index equalities/inequalities with
   exact index-value reductions and handle the reflexive cases explicitly.
2. Normalize every fixed nodes/pt/roots application BEFORE invoking field/ring
   tactics. Small typed evaluation lemmas proved by rfl can isolate kernel
   reduction from algebra; their types must keep the same original expressions.
   The displayed failures leave nodes at indices2,3,5 and nested pt components.
3. The target slack denominator is known positive as2-7*e^2 but is displayed
   as2-e^2*7 after normalization. Carry the exact equivalent nonzero hypothesis
   or avoid reordering it before field_simp. The three displayed rational
   identities are the unchanged true identities from the written slack table.
4. Concrete card/intersection facts should be closed with explicit finite
   computation (decide) or fully typed equality proofs, not left as unresolved
   numeral equalities by norm_num. The source root sets are tiny, computable
   Finsets; no extra assumption or classical geometric oracle is necessary.
5. In the three-edge route, unfold the local vector definition and explicitly
   supply point indices0,1,4,3 rather than leaving an underscore for inference.

Compile on the committed Lean4.30.0/Mathlib pin, starting with the smallest
changed helper file, then the complete standalone packet and all five transitive
axiom checks. Do not infer the remaining dependent proofs pass just because
these first errors are fixed. No theorem statement, delta/e interval, original
row, exhaustive-neighbor quantifier or three-edge conclusion should be weakened.
Only after local validation and a fresh ownership/duplicate check is another
existing-PR final gate appropriate. Do not use repeated Actions attempts as the
repair compiler. No claim that these directions have been Lean-tested.
