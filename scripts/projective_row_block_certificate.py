#!/usr/bin/env python3
"""Certify ordinary-edge bounds for products hidden by a positive row shear.

Input A,b describes the TARGET polytope. Supply chart_normal c, a SOURCE
feasible_point/positive_balance for rows A_i-b_i*c, and nonnegative
source_denominator_weights / target_denominator_weights. The weights must
represent -c / +c using source / target rows and have weighted RHS < 1.

Reuses the repository's exact rational row_block_certificate helper. A chart
is supplied, not discovered or assumed to exist. No floats, omitted inequalities,
unchecked denominator signs, Lean verdicts, or global Hirsch claims are allowed.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any

from row_block_certificate import (
    Q, certificate as row_certificate, dot, jsonable, rational, require,
    verify_certificate as verify_rows,
)


def problem(data: dict[str, Any]) -> tuple[list[list[Q]], list[Q], list[Q], dict[str, Any]]:
    require(isinstance(data, dict), 'input must be an object')
    require('keep' not in data and 'redundancy' not in data,
            'this adapter does not drop rows; normalize them in a separate certified step')
    target = [[rational(x) for x in r] for r in data['A']]
    rhs = [rational(x) for x in data['b']]
    normal = [rational(x) for x in data['chart_normal']]
    require(bool(target) and bool(normal), 'positive ambient dimension is required')
    require(len(rhs) == len(target) and all(len(r) == len(normal) for r in target),
            'A/b/chart shape mismatch')
    source = [[x - bound*c for x, c in zip(row, normal)]
              for row, bound in zip(target, rhs)]
    source_data = {
        'A': source, 'b': rhs,
        'feasible_point': data['source_feasible_point'],
        'positive_balance': data['source_positive_balance'],
    }
    return target, rhs, normal, source_data


def positivity_margin(rows: list[list[Q]], rhs: list[Q],
                      desired: list[Q], raw_weights: list[Any]) -> Q:
    weights = [rational(x) for x in raw_weights]
    require(len(weights) == len(rows) and all(x >= 0 for x in weights),
            'denominator weights must be nonnegative and match the rows')
    for j, wanted in enumerate(desired):
        require(sum((weights[i]*rows[i][j] for i in range(len(rows))), Q(0)) == wanted,
                'denominator normal identity fails')
    margin = 1 - dot(weights, rhs)
    require(margin > 0, 'denominator is not certified strictly positive')
    return margin


def verify_projective_certificate(data: dict[str, Any], cert: dict[str, Any]) -> dict[str, Any]:
    """Independent identity checking; discovery output is never trusted."""
    target, rhs, normal, source = problem(data)
    alleged = [[rational(x) for x in r] for r in cert['unsheared_rows']]
    require(alleged == source['A'], 'rank-one unshearing identity fails')
    source_margin = positivity_margin(source['A'], rhs, [-x for x in normal],
                                      data['source_denominator_weights'])
    target_margin = positivity_margin(target, rhs, normal,
                                      data['target_denominator_weights'])
    verified = verify_rows(source, cert['row_block_certificate'])
    budget = verified['ordinary_edge_bound_using_existing_small_excess_theorem']
    return {
        'positive_chart_certified': True,
        'source_denominator_lower_bound': source_margin,
        'target_denominator_lower_bound': target_margin,
        'target_bounded_nonempty_by_chart': True,
        'source_factors': verified['factors'],
        'total_excess': verified['total_excess'],
        'ordinary_edge_bound_conditional_on_transport_and_small_excess': budget,
        'unresolved_source_factors': verified['unresolved_factor_indices'],
        'scope': 'Exact rational certificate; not a Lean or Prove2Me acceptance verdict.',
    }


def certificate(data: dict[str, Any]) -> dict[str, Any]:
    _, _, _, source = problem(data)
    rows = row_certificate(source)
    cert = {'unsheared_rows': source['A'], 'row_block_certificate': rows['certificate']}
    return {'certificate': cert, 'verified': verify_projective_certificate(data, cert)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        result = certificate(json.loads(args.input.read_text(encoding='utf-8')))
        text = json.dumps(jsonable(result), indent=2, sort_keys=True) + '\n'
        if args.output:
            args.output.write_text(text, encoding='utf-8')
        else:
            print(text, end='')
    except (ValueError, KeyError, TypeError, ZeroDivisionError, OSError) as exc:
        parser.exit(2, f'Certificate rejected: {exc}\n')


if __name__ == '__main__':
    main()
