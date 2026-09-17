# First compile failed in the overlap lemma; publication skipped

This is a derived diagnostic excerpt/readback, not a full raw runner log or
platform receipt. Run35267809797, verify job105359311045, checked exact proof
e987a6ee0b67b143fd8ed3f71a80b5c6089833e1 with pinned Lean4.30.0/Mathlib.
The gate and environment restoration succeeded. Driver compilation failed;
verified-packet upload and publication were skipped. No platform theorem or
submission was created by that run.

The sole displayed Lean error is driver.lean:763:4:

```text
error: omega could not prove the goal
...
where
 a := ↑k
 b := ↑m
 c := ↑s
 d := ↑↑⟨s, ⋯⟩
```

The preceding simp list's Fin.ext_iff argument was reported unused. The finite
membership equivalence for the overlap still contained a coerced constructed
Fin label that the automated arithmetic did not identify with s. This is an
elaboration/tactic failure, not a counterexample to the interval identity.

The correction replaces only the four-line automatic proof of that equivalence
with explicit Finset.ext/membership reasoning in each direction. The constructed
label's value is made explicit using congrArg Fin.val, and conversely equality
of values is converted by Fin.ext. The set/cardinality statement is unchanged.
No other helper body, accepted dependency, public signature, problem.json or
explanation.md changed. Exact public-signature and rational tests pass again;
they are not local Lean verification.

Initial source SHA256:
5a9eca4f81e0c3c7714b602b5870d676cf390701be1ea89e08735b5946ea4baf.
Corrected source SHA256:
5be516fabb700f4f19f881536558c58ab959dec90e6193a8b957e275e40104be.
The corrected source has889 lines; the initial source had871.

The first run's roots_zero_iff and point_extreme audits listed only propext,
Classical.choice and Quot.sound. Later edge/route/root audits contained sorryAx
from the failed elaboration recovery and are NOT successful verification.
No source proof admission was present. The corrected final gate must compile
and audit the entire packet independently before any publication.

The first request artifact10517336191 was downloaded and its ZIP digest checked:
9c5866371c88c9893117571b85650446e26748541c439edd1c3afccb8ebe1106.
It resolves the exact first proof SHA above. The original ZIP, initial proof
and exact correction diff are preserved in the conversation bundle.
No workflow, pin, permission, secret split or other branch was changed.
