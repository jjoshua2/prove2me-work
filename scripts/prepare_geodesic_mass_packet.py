#!/usr/bin/env python3
"""Freeze the graph-theoretic joint budget; geometric adapters remain separate."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME = 'Hirsch.geodesic_joint_budget_of_all_available_contacts'
PREAMBLE = 'import Mathlib\nopen scoped BigOperators\nopen Set'
BINDERS = '''{V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (available : Finset V) (labels : List V) (hnd : labels.Nodup)
    (hsub : ∀ i ∈ labels, i ∈ p.support) (delta : V → ℕ) (e : ℕ)
    (hbudget : ∀ i ∈ labels, delta i + available.card ≤ e +
      (available.filter (fun j => j = i ∨ G.Adj j i)).card) :
    (labels.map delta).sum + labels.length * available.card ≤
      labels.length * e + 3 * available.card'''
NATURAL = '''Let p be a metric-shortest path in an undirected simple graph. Let A be
any finite set of available vertices, including vertices off the path, and let
L be a duplicate-free list of vertices on p. Suppose each selected vertex i
has a nonnegative integer budget delta_i satisfying
delta_i + |A| <= e + #{j in A : j=i or j is adjacent to i}.
Then sum_i delta_i + |L|*|A| <= |L|*e + 3|A|.
In particular when |A|=e the total budget is at most 3e.

Each available vertex contacts a window of at most three path positions:
otherwise it supplies a two-edge shortcut. Double-count those contacts and
sum the pointwise inequalities. True metric shortestness is essential.
This theorem is a graph and integer-budget statement. The separate repository
adapter proves its applicability to actual clipping carrier excesses; the
statement itself neither identifies delta with edge distance nor resolves
the Polynomial Hirsch conjecture.'''
EXPLANATION = '''Construct a competing path using take, append, and drop. Minimality
shows that any walk between two indexed path vertices is at least their index
gap. Closed-neighborhood contacts through one available vertex give a walk
of length at most two. Choose the first contact index to contain all contacts
in a three-element set, including an available vertex not on the path.
Double-count selected/available incidences, then sum the supplied pointwise
budgets without truncated subtraction. All proofs are in the submitted source;
there are no imported theorem dependencies or unproved cost assumptions beyond
the pointwise inequality explicitly present in the statement.'''

def prepare(source, out):
    source = subprocess.check_output(['git', 'rev-parse', source], text=True).strip()
    blobs = {}
    def blob(path):
        blobs[path] = subprocess.check_output(['git', 'rev-parse', source + ':' + path], text=True).strip()
        return subprocess.check_output(['git', 'show', source + ':' + path], text=True)
    region = blob('Solutions/PolynomialRegionRouting.lean')
    start = region.index('lemma nodup_cost_le')
    end = region.index('/--', start)
    prefix = PREAMBLE + '\nnamespace HirschRegionRoute\n' + region[start:end] + '\nend HirschRegionRoute\n'
    body = blob('Solutions/PolynomialGeodesicRowIncidence.lean')
    prefix += '\n'.join(line for line in body.splitlines() if not line.startswith(('import ', '#print axioms'))) + '\nend\n'
    solution = prefix + '\ntheorem solution ' + BINDERS + ''' := by
  classical
  have hpoint : ∀ i ∈ labels, delta i + available.card ≤
      e + HirschRegionRoute.availableContactLoad G available i := by
    intro i hi
    simpa only [HirschRegionRoute.availableContactLoad, HirschRegionRoute.ClosedNear] using hbudget i hi
  have hs := HirschRegionRoute.list_sum_available_budget labels delta
    (HirschRegionRoute.availableContactLoad G available) available.card e hpoint
  have hc := HirschRegionRoute.geodesic_list_available_load p hp available labels hnd hsub
  omega
'''
    problem = {'theorem_name': NAME, 'theorem_title': 'All available vertices give a joint budget along a graph geodesic',
               'formal_statement': 'theorem ' + NAME + ' ' + BINDERS + ' := by sorry',
               'natural_language_statement': NATURAL, 'preamble': PREAMBLE,
               'source': 'Geodesic shortcut and double-counting formalization, https://github.com/jjoshua2/prove2me-work/tree/' + source,
               'tags': ['graph-theory', 'polyhedra', 'formalization'], 'env': PIN}
    files = {'solution.lean': solution, 'driver.lean': solution + '\n#print axioms solution\n',
             'statement.lean': PREAMBLE + '\ntheorem ' + NAME + ' ' + BINDERS + ' := by sorry\n',
             'problem.json': json.dumps(problem, indent=2) + '\n', 'explanation.md': EXPLANATION + '\n'}
    out.mkdir(parents=True, exist_ok=True)
    for name, body in files.items():
        (out / name).write_text(body)
    (out / 'manifest.json').write_text(json.dumps({'source_commit': source, 'mathlib_rev': PIN,
        'source_blobs': blobs, 'public_dependencies': {}, 'sha256': {
            name: hashlib.sha256(body.encode()).hexdigest() for name, body in files.items()}}, indent=2) + '\n')
    print(json.dumps({'source': source, 'proof_lines': len(solution.splitlines())}))

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    prepare(args.source, args.out)
