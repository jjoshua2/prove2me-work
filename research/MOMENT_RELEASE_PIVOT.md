# Arbitrary moment-vertex release pivots

## Constructive local progress

For d<m and distinct real node values a_i, let A_i(x)=sum_(j=1..d)(a_i^j-average_l a_l^j)x_j. The source is ANY actual extreme point u of all original inequalities A_i(x)<=1. Choose ANY tight original row p. The accepted active-evaluation theorem produces a direction w with A_p(w)=-1 and A_i(w)=0 for every other tight row.

The existence of a finite blocking row is proved, not supplied. The centered row slopes sum to zero. Since A_p(w)=-1, some slope must be positive. No already-tight row has positive slope, so every positive-slope row has positive source slack. Minimize (1-A_i(u))/A_i(w) over that finite nonempty set. The minimum t is positive, all original rows remain feasible up to t, and a minimizing q becomes tight. Its inequality fails past t, proving the entire nonnegative ray interval exactly [0,t].

At v=u+t*w, p is strictly slack and all other old active rows remain tight. The endpoint also has new q tight. These give d tight rows. The accepted polynomial root bound allows at most d, so the active set is EXACTLY (I minus p) union {q}; no extra blocker enters simultaneously. The accepted vertex criterion makes v extreme. The accepted whole common-slice theorem identifies [u,v] as an exposed nondegenerate original edge. No projected auxiliary edge, feasible direction, neighbor, inverse, rank or step oracle is assumed.

This is a local version of classical simplex geometry instantiated on the actual moment H system, not a new historical diameter theorem. It handles arbitrary moment vertices, including those with nonconsecutive active sets. The separate #296 consecutive-block route construction is not duplicated. The public statement includes the exact direction, ratio, next active set, whole exposed slice and feasible ray interval; it does not claim a policy reaches a target in a polynomial number of steps.

## Assumptions and limits

The parameters are injective and d<m. The chosen source must be an actual extreme point, and p must be tight. No compactness, ordered nodes, supplied vertex list or basis is a premise. The proof covers odd and even dimensions. At d=0 no tight row exists, so the implication is vacuous; dimension one gives the actual interval edge. The m original inequalities are not asserted irredundant facets in every boundary case.

The statement is existential over the direction and blocker. Source active-evaluation bijectivity additionally implies normalized-direction uniqueness mathematically, but a separate uniqueness/neighbor-enumeration theorem is not part of the public type. Selection among possible leaving rows, global monotonicity, cycle prevention and a useful uniform route-length bound remain separate. A valid one-edge construction cannot be counted as a solution of Polynomial Hirsch.

## Exact supporting tests

Six independent SymPy original-H enumerations examine 194 square systems and yield 69 feasible vertices. All 272 choices of a tight leaving row produce checked original edges; 4,934 source-inverse identities and 4,630 full-reference supporting-objective comparisons pass. The 125 infeasible full-tight systems are not included as vertices. Every common-row objective maximizes at exactly the two delivered endpoints among all reference vertices.

Nine additional pivots in dimensions 8,16,32 check the full original inequalities without enumerating the large graphs. Fifteen saved records replay with selection and inverse constructors disabled. Nine malformed controls are rejected. The final committed script reproduces both the 3,390-byte report and 263,614-byte fixture exactly in a clean script-only workspace. The full fixture is supplied in the export and regenerates with:

    python3 scripts/test_moment_release_pivots.py --out /tmp/moment-release

The explicit polynomial seed in the large tests is only an instance generator, not a duplicate Lean block-route theorem. Code uses exact rationals; the independent graph reference uses SymPy. These tests are not Lean-extracted and do not certify arbitrary JSON against the Lean kernel.

## Verification and ownership

The full 544-line accepted #295 namespace prefix is reused byte-for-byte, omitting only its former root/axiom-print suffix. Its original artifact and all five frozen hashes were checked. The new packet is research/publication_packets/moment_vertex_release_pivot. Consult its actual receipt/audit if present for verification status; a prepared source or issued comment is not acceptance.

Coordination was posted on #295 as comment5720564095. #296 block routes, #297 catalogues, older owned work, #270 blocked integration and reserved #210 remain untouched. No existing pin, workflow, protocol, allowlist or trusted credential isolation is altered. No fresh root/leaf mission poll is claimed.
