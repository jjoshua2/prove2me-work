# Moment small-face witness publication resumption

Read live STATUS and open PR comments. This is the previously local-only
210-line packet, now uploaded unchanged as proof PR #285. The newer accepted
#284 and prior accepted #281 are distinct and must not be resubmitted.

Target: Hirsch.moment_curve_exact_small_face_witnesses.
Packet: research/publication_packets/moment_small_face_witnesses.
Prepared proof SHA:612c7278ef785e649b3b9eb137b15e2c3e861e2d.
Source SHA256:7f721731a92f63e9299fd5b63ebcb991e8a992f6089c0d3a40298543c8ac2bee.
Base:fcc7f68febc372ccce3c8a8c4649638758c25374.
Actual NEW top-level command5706535074; bot acknowledgement5706536794.
Run35166526941 resolved the exact prepared SHA. Do not post another command
while it is active or registering a theorem. Keep draft until actual result.

The theorem constructs h>0 and x in R^(2k), for any finite distinct real
moment parameters and a proper selected set S with |S|<=k, such that the
original mean-centered rows have EXACT slack product_(s in S)(a_i-a_s)^2/h.
Thus all inequalities hold and precisely S is tight. No support or optimizer
is assumed. It supplies the proper-subset feasibility side of #267, not whole
(k+1)-set incompatibility, full-dimensionality/boundedness for arbitrary small
parameter sets, or Polynomial Hirsch. The mean-centering and exact constant
coefficient cancellation are proved, not hidden in an affine-map premise.

The proof and problem.json are unchanged from the preceding local bundle.
Explanation/status are refreshed for the actual upload. Five axiom printouts
and import/open-only preamble. No own target import or proof admissions.
Local Lean/Lake remains absent; fresh toolchain/GitHub DNS fails. This is the
user-requested final hosted attempt, not locally green compilation or a
speculative repeated proof-editing loop. A failure must be preserved distinctly
from a mathematical counterexample or Prove2Me rejection.

Exact arithmetic/signature tests reran, with 3,671 small witnesses,60,104
original inequalities,47,106 strict rows,86,426 coefficient probes and three
large samples in dimensions16/32/64. Ten negative controls and26 producer-
disabled audits pass. An isolated one-script replay reproduces the complete
report and38,922-byte fixture byte-for-byte. None of this proves Lean validity.

    python3 scripts/test_moment_small_faces.py

The original fixture regenerates and is in the conversation bundle. Reports
and source code are committed. These supporting-file additions do not alter
the proof SHA already resolved by the gate. No workflow, permission, secret,
toolchain or old proof changes. Other owned work remains untouched.

Next substantive geometric interface: establish the incompatible (k+1)-sets
using the explicit alternating affine dependence and derive minimality with
this witness theorem. The accepted finite stellar count #281 can then be
applied, but no whole exponential-family formalization is claimed here.
