# Continue from mixed-defect absorption, not an unproved universal descent

Read the live STATUS and actual open PRs before choosing work. This contribution
is written research and exact code, not a Lean/Prove2Me theorem. It extends #261's
exact stellar recurrence and original-edge carrier maps; all four old source
dependencies remain byte-identical. The attempted informational comment on #261
was blocked before posting and was not retried through another route. Source
work is a separate research contribution, not a publication trigger.

NEW EXACT OPERATION: choose a face edge E contained in at least one higher
minimal nonface. For every mixed high N meeting E in one label, provide a blocker
B that is either shared (E contained in B) or an old missing pair meeting E,
with B-E contained in N-E. This absorbs every mixed offspring. Old high defects
not containing E remain; shared defects replace E by the new label. Shared
triples become pairs. Therefore W=sum_high(|N|-2) drops EXACTLY by the number
of shared defects. Identical incidence is sufficient but no longer necessary.
The update is proved and independently tested; arbitrary subdivisions are not
assumed decreasing.

The bounded macro rule tries one arbitrary bridge followed by absorbed moves.
A macro of at most ell subdivisions is accepted ONLY after W strictly decreases.
Thus total committed subdivisions are at most ell*(W0-Wres). If residual high
nonfaces remain, #261's exact residual-block cost still applies. Neither a small
W0 nor successful ell3 macros on every polytope is asserted. Trial search can
be expensive; all caps and residual costs are explicit.

Actual cyclic-polar4D examples with7/8/9 facets previously needed M70/96/126;
the new greedy absorbed schedules give M11/14/18. The independent rational5D,
10-facet plateau has36 vertices. Its three absorbed prefix moves give
W9->7->5->3, and no single face-edge move lowers that last W. A3-step macro
crosses3->3->2->0. Total M16 instead of266, bound11. The input points and exact
all-square-system reconstruction are retained; no exploratory floating hull
is used by the certificate. This is a real plateau, not a tie-breaking failure.

The explicit cyclic boundary schedule first processes distance-two cyclic
chords, then pairs within two contiguous halves. Its absorbed moves finish
within T_n=binom(floor(n/2),2)+binom(ceil(n/2),2)-n+6 for all n>=6. Repeated
ordinary primal wedges expand each label to a group. Safe clone compression
plus the cyclic schedule gives original-edge bound m-4+T_n, with dimension
4+m-n. The geometric wedge/nonface proof, endpoint carriers and n>=7 nonproduct
qualification are in the note. This is a cheap FLAG REFINEMENT class, not a
new best diameter class: each ordinary wedge already increases graph diameter
by at most one, and the base has fixed dimension four.

REPRODUCE in separate calls if an execution timeout is short:
  python3 scripts/test_mixed_defect_absorption.py --stage abstract
  python3 scripts/test_mixed_defect_absorption.py --stage geometry
  python3 scripts/test_mixed_defect_absorption.py --stage family

Abstract:324 complexes,3189 exact stellar updates,1013 absorbed updates,
546 genuinely unequal-incidence updates,10550 pure-carrier adjacencies.
Geometry:58 pairs,123 delivered edges vs129 previous#261 and122 BFS; one
nonshortest route and one original reentry remain. All502 reference square
systems are exact. Thirteen malformed/capped controls fail; six stored audits
pass with geometric discovery AND planner selection disabled. Finite BFS and
classification are still replayed. No claimed formal verification of Python.

Family:11 cycle sizes n6..16 and9 wedge instances up to dimension20. Larger
models have construction-proved nonfaces and exact original-edge certificates;
only one10D/12-facet wedge additionally gets a full final-H graph/nonface check.
Base4D graphs choose test endpoints; no full large graph is supplied to the
producer. Distinguish greedy M11/M14 from explicit-schedule M12/M16 at n7/n8.
The complete three-stage suite replays in a clean directory with two new
scripts, the integer input fixture and four unchanged dependencies. Every
nontiming result/source field and both full fixture bytes agree. Detailed reports
and fixtures regenerate and are bundled; compact summaries are derived records.

LITERATURE GUARD: arXiv1303.5885 still advertises a missing-face-size bound in its
abstract but is withdrawn with an explicit mistake in the main proof. Do NOT
import its claimed 2^(r-2)n theorem. Adiprasito--Benedetti's normal-flag result is
the classical imported short-route theorem. No broad monotonicity assertion
from a stellar-theory summary replaces the exact verified recurrence here.

Next research must control a successful mixed-move schedule or residual size
for arbitrary dual boundaries. The current macros cross one explicit plateau,
not every possible plateau. The original conjecture is not reduced to a proved
small-weight condition. Existing #244/#238/#250/#255 ownership and all accepted
or pending platform submissions remain untouched.
