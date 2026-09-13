# Tight path forces target tightness

Compare the two paths prefix by prefix. At each step, `u` gains exactly the edge cost while `v` gains at most that cost, so induction gives `v k - v 0 ≤ u k - u 0` for every prefix `k ≤ n`. At the final vertex, `v` reaches the target bound `C`, hence `C ≤ u n - u 0`. The assumed target feasibility of `u` gives the reverse inequality. Therefore `u n - u 0 = C`.

This is the finite scalar core behind the network-potential target-insertion argument; it uses no graph-diameter or nondegeneracy premise.
