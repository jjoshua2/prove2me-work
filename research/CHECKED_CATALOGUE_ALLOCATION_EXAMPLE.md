# A checked catalogue reproduces a complete competing-shape budget

This is an exact executable application of the new audit, not a second claimed
Lean-verified instance or a new joint-capacity theorem. It checks a known
example from the earlier finite-summand work through the new independently
auditable complete catalogue, including every excluded support.

Let R be the hexagon |x|<=1, |y|<=1, |x+y|<=1. Take the triangle
T=conv(0,e1,e2) and square Q=conv(0,e1,e2,e1+e2). Their joint allocation system
has five coefficient variables and thirteen inequalities: six original-row
allocation constraints, five nonnegativity rows, and two block-total rows.

Applying the new producer/checker to its transpose checks exactly 4096 supports
through cardinality six. Of these, 768 have nonzero zero-mass null witnesses;
3328 have verified left inverses. The filter rejects 1295 inconsistent and
2015 nonpositive normalized candidates, leaving exactly 18 circuits. The
finite audit checks 87183 exact identities and uses no rank or LP routine.

The original six vertices are independently reconstructed by intersecting
pairs of original inequalities. For every audited circuit, optimizing its
original objective over those six vertices yields a joint linear budget.
Every such budget follows from s>=0, t>=0, s+t<=1. One circuit gives the
sharp reverse constraint (s+t)/5<=1/5, with thirteen weights

    (0,0,1/5,0,0,1/5,1/5,0,1/5,0,1/5,0,0).

Therefore the recovered complete scale region is exactly

    s>=0, t>=0, s+t<=1.

The full finite table, every derived budget, the independent vertices and the
sharp witness are in fixtures/checked_hexagon_triangle_square.json in the
conversation bundle. That fixture and the reproduction script are additional
local evidence, not a claim that a five-variable/13-row example was evaluated
inside Lean. The accepted proof's actual kernel example is A=(1,1,-1,0).

This demonstrates the intended connection: the extraction code no longer has
to trust a claim that an enumerator happened to return every positive circuit.
The remaining integration obligation is to apply the formal checked-output
statement directly to the formal allocation/support-budget theorems, rather
than treat the Python test itself as that complete formal composition.
