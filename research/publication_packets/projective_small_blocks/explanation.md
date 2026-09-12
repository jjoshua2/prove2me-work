The proof first uses the already-Proved independent-row-block
theorem to route the source polyhedron $P$ in at most $n-d$ ordinary edges.
That theorem derives boundedness of the factors from the nonempty bounded
source and sums their small-excess bounds. The complete row partition and
invertible coordinate map make the sum of factor excesses equal to $n-d$.

The supplied weights certify both denominators. Multiplying the source rows
by $\mu_i\ge0$ gives $-c\cdot x\le\sum_i\mu_i b_i<1$ on $P$.
Similarly the target weights give $c\cdot y\le\sum_i\nu_i b_i<1$ on $Q$.
Thus $1+c\cdot x$ and $1-c\cdot y$ are strictly positive on their respective sets.

Define $f(x)=x/(1+c\cdot x)$ and $g(y)=y/(1-c\cdot y)$.
Their inverse identities are proved by direct algebra. The exact slack identity

$$b_i-a'_i\cdot f(x)=\frac{b_i-a_i\cdot x}{1+c\cdot x}$$

proves $f(P)=Q$ using positivity in both directions. No additional halfspace
is silently discarded. The total functions outside these positive domains
are never used in the geometric argument.

For $z=\alpha x+\beta y$, where $\alpha,\beta\ge0$ and
$\alpha+\beta=1$, write $D(t)=1+c\cdot t$. The proof establishes

$$f(z)=\frac{\alpha D(x)}{D(z)}f(x)+\frac{\beta D(y)}{D(z)}f(y).$$

The new coefficients are nonnegative and sum to one; strict positivity is
preserved for interior segment parameters. Applying the same identity to $g$
establishes exact image equalities for closed and open segments. Injectivity
on the convex positive domain then preserves and reflects extreme subsets.
Singletons give vertex preservation, and extreme closed segments give ordinary
edge preservation. Mapping each point of the source walk preserves its length
without any extra steps.

All inverse, segment, extreme-set, edge, slack, and multiplier proofs are
contained in the submitted file. Its only imported theorem is the already-Proved
independent-small-row-block bound. The audit driver keeps that exact input as
an explicit proposition; the platform verifies the unconditional composition.
Projective graph invariance is classical. This contribution formalizes the
specific positive chart and a finite sufficient routing criterion; it does not
prove a uniform polynomial bound for arbitrary carriers or a chart-discovery theorem.
