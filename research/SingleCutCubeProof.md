For every natural number $d$, every $a\in\mathbb R^d$, and every $\beta\in\mathbb R$, let

$$P=\{x\in[0,1]^d:a\cdot x\le\beta\}.$$

Then every two vertices of $P$ are joined by a padded edge walk of length $d+2$:

$$\operatorname{diam}(P)\le d+2.$$

No sign, integrality, simplicity, general-position, full-dimensionality, or nonemptiness assumption is needed. The result concerns the continuous polytope, not the convex hull of feasible integer points. The constant is an upper bound; optimality is not asserted.

The proof attaches each vertex to a retained cube corner, and joins the two corners without changing any coordinate twice. The attachment costs at most one edge at each end.

### Retained corners

Given feasible binary corners $p,q$, form the binary corner $z$ by taking the coordinatewise minimum when $a_i\ge0$ and the maximum when $a_i<0$. Thus

$$a_i z_i\le a_i p_i,\qquad a_i z_i\le a_i q_i$$

for each coordinate. Change the coordinates of $p$ to those of $z$ one at a time, and do the same from $q$ to $z$. Every change decreases or preserves the cutting functional. Therefore every intermediate corner is feasible. Reverse the second path and concatenate. Because $z_i$ equals either $p_i$ or $q_i$, the two sets of changed coordinates are disjoint. The total length is exactly their Hamming distance, at most $d$.

A feasible segment between two binary corners differing in coordinate $i$ is an extreme subset of $P$. Indeed, any open-segment decomposition of a point on that segment has the same fixed binary values in all other coordinates. Its endpoints therefore lie on the same coordinate segment. This verifies that the constructed moves are genuine polytope edges, not merely feasible displacements. In degenerate cuts, new edges can make graph distances shorter than Hamming distance; no shortest-path assertion is required here.

### New cut vertices

First establish a local perturbation criterion. Suppose a direction $h$ vanishes in every coordinate where $x$ is at a box bound, and also satisfies $a\cdot h=0$ when the cut is active. Finitely many strict slacks provide a positive $\delta$ such that both $x+\delta h$ and $x-\delta h$ belong to $P$. If $x$ is extreme, its midpoint decomposition implies $h=0$.

Now suppose an extreme point $x$ is not binary, and choose a fractional coordinate $i$. The direction $e_i$ shows both that $a_i\ne0$ and that $a\cdot x=\beta$; otherwise the perturbation criterion would force $e_i=0$. If another coordinate $j$ were fractional, the nonzero direction

$$h=a_j e_i-a_i e_j$$

would preserve every active box bound and the cutting equality, again contradicting the criterion. Thus $x$ has exactly one fractional coordinate.

Round that coordinate toward the cost-minimizing endpoint: set it to $0$ when $a_i\ge0$, and to $1$ otherwise. The resulting binary corner $p$ is feasible. The segment $[p,x]$ is an extreme subset of $P$: all coordinates other than $i$ are fixed at binary bounds, and the cut inequality restricts coordinate $i$ exactly to the interval between $p_i$ and $x_i$. Hence $p$ and $x$ are adjacent.

### Concatenation

For arbitrary extreme points $x,y$, select attached retained corners $p,q$. The stationary-or-edge steps at either endpoint, together with the corner path, yield

$$x\longrightarrow p\longrightarrow\cdots\longrightarrow q\longrightarrow y$$

of at most $1+d+1=d+2$ steps. Padding with stationary steps gives the exact budget in `Hirsch.DiamLE`. Empty and zero-dimensional cases are handled by the same quantified statement.

### Boundary of the argument

This is a concrete restricted full-diameter theorem, not a general polynomial Hirsch proof. It does not assume a small rank, product decomposition, or another numerical diameter theorem. It does not claim a best bound or literature priority.

The invariant fails for two cuts. The square intersected with $x-y\le1/3$ and $y-x\le1/3$ is a hexagon with retained corners $(0,0)$ and $(1,1)$ at distance three, although their Hamming distance is two. Thus one cannot iterate the proof while assuming retained-corner Hamming routes survive.

The vertex classification is also discussed in Black and Steiner, *Finding Short Paths On Simple Polytopes*, arXiv:2603.05482v1 (March 5, 2026), Lemma 2.2. Their shortest-path hardness results for fractional knapsack polytopes concern optimizing the exact path length, not finding the bounded-length paths constructed here. Source: https://arxiv.org/html/2603.05482v1
