#!/usr/bin/env python3
"""Exact minimality audit for the seven-mode Boolean seed.

The search domain is the 13 unoriented nonzero modes in the coordinate unit
cube.  For every subset of at most six modes, the script either bounds the
rank strictly below ``4M-2`` by summing the exact ranks of its individual
triad-support blocks, or computes the combined rank exactly over Q.  It then
checks that the seven Boolean representatives attain both the Hermitian rank
``4M-2`` and the unrestricted complex rank ``8M-2``.

This proves minimality inside the stated unit-cube domain.  It makes no claim
about six-mode configurations using wavevectors outside that cube.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import gcd
from typing import DefaultDict, Dict, List, Sequence, Tuple

from verify_full_multiplier_rigidity import (
    BOOLEAN_SEED_REPRESENTATIVES,
    boolean_seed_vectors,
    exact_rank,
    nonzero_vectors,
    triad_rows,
)
from verify_general_multiplier_rigidity import (
    exact_rank as general_exact_rank,
    triad_rows as general_triad_rows,
)
from verify_laplacian_rigidity import Vec, add, cross, neg, unoriented


TriadSupport = Tuple[Vec, Vec, Vec]


def canonical_support(p: Vec, q: Vec, r: Vec) -> TriadSupport:
    """Canonicalize a signed triad up to permutation and total sign."""
    forward = tuple(sorted((p, q, r)))
    backward = tuple(sorted((neg(p), neg(q), neg(r))))
    return min(forward, backward)  # type: ignore[return-value]


def restrict_blocks(
    row: Sequence[Fraction],
    subset: Sequence[Vec],
    full_representatives: Sequence[Vec],
    block_width: int,
) -> List[Fraction]:
    """Restrict a full-cube row to the mode blocks in ``subset``."""
    full_index = {mode: index for index, mode in enumerate(full_representatives)}
    result: List[Fraction] = []
    for mode in subset:
        start = block_width * full_index[mode]
        result.extend(row[start : start + block_width])
    return result


def hermitian_support_rows() -> tuple[
    List[Vec], Dict[TriadSupport, List[List[Fraction]]]
]:
    """Generate full-cube Hermitian rows grouped by unsigned triad support."""
    vectors = sorted(nonzero_vectors(1))
    representatives = sorted({unoriented(k) for k in vectors})
    grouped: DefaultDict[TriadSupport, List[List[Fraction]]] = defaultdict(list)
    vector_set = set(vectors)
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if (
                r not in vector_set
                or not (p <= q <= r)
                or cross(p, q) == (0, 0, 0)
            ):
                continue
            grouped[canonical_support(p, q, r)].extend(
                triad_rows(p, q, r, representatives)
            )
    return representatives, dict(grouped)


def support_modes(support: TriadSupport) -> frozenset[Vec]:
    return frozenset(unoriented(mode) for mode in support)


def audit_smaller_subsets(
    representatives: Sequence[Vec],
    grouped: Dict[TriadSupport, List[List[Fraction]]],
) -> tuple[int, int, Dict[int, int]]:
    """Rule out all unit-cube subsets of cardinality at most six exactly."""
    support_ranks = {support: exact_rank(rows) for support, rows in grouped.items()}
    assert set(support_ranks.values()) <= {6, 7}

    exact_checks = 0
    subsets_checked = 0
    rank_ceiling: Dict[int, int] = {}
    for size in range(1, 7):
        target_rank = 4 * size - 2
        best_rank = 0
        for subset_tuple in combinations(representatives, size):
            subsets_checked += 1
            subset = frozenset(subset_tuple)
            active = [
                support
                for support in grouped
                if support_modes(support) <= subset
            ]
            upper_bound = sum(support_ranks[support] for support in active)
            if upper_bound < target_rank:
                best_rank = max(best_rank, upper_bound)
                continue

            rows: List[List[Fraction]] = []
            for support in active:
                rows.extend(
                    restrict_blocks(
                        row, subset_tuple, representatives, block_width=4
                    )
                    for row in grouped[support]
                )
            rank = exact_rank(rows)
            exact_checks += 1
            best_rank = max(best_rank, rank)
            assert rank < target_rank, (subset_tuple, rank, target_rank)
        rank_ceiling[size] = best_rank
    return subsets_checked, exact_checks, rank_ceiling


def integer_rank(rows: Iterable[Sequence[int]]) -> int:
    """Exact rank with primitive integer cross-multiplication elimination."""
    basis: Dict[int, List[int]] = {}
    for source in rows:
        row = list(source)
        for pivot in sorted(basis):
            if not row[pivot]:
                continue
            factor = row[pivot]
            pivot_factor = basis[pivot][pivot]
            row = [
                pivot_factor * x - factor * y
                for x, y in zip(row, basis[pivot])
            ]
            content = 0
            for value in row:
                content = gcd(content, abs(value))
            if content > 1:
                row = [value // content for value in row]
        pivot = next((j for j, value in enumerate(row) if value), None)
        if pivot is None:
            continue
        content = 0
        for value in row:
            content = gcd(content, abs(value))
        if content > 1:
            row = [value // content for value in row]
        if row[pivot] < 0:
            row = [-value for value in row]
        basis[pivot] = row
    return len(basis)


def primitive_rows_by_support_mask(
    representatives: Sequence[Vec],
    grouped: Dict[TriadSupport, List[List[Fraction]]],
) -> Dict[int, List[Tuple[int, ...]]]:
    """Clear the common denominator and deduplicate row directions."""
    index = {mode: position for position, mode in enumerate(representatives)}
    result: Dict[int, List[Tuple[int, ...]]] = {}
    for support, rows in grouped.items():
        mask = sum(1 << index[mode] for mode in support_modes(support))
        primitive: set[Tuple[int, ...]] = set()
        for row in rows:
            assert all(6 % value.denominator == 0 for value in row)
            scaled = [int(6 * value) for value in row]
            content = 0
            for value in scaled:
                content = gcd(content, abs(value))
            assert content
            scaled = [value // content for value in scaled]
            first = next(value for value in scaled if value)
            if first < 0:
                scaled = [-value for value in scaled]
            primitive.add(tuple(scaled))
        result[mask] = sorted(primitive)
    return result


def expected_orthant_seeds() -> set[Tuple[Vec, ...]]:
    """The four Boolean subset-sum seeds modulo simultaneous sign."""
    coordinate_vectors: Tuple[Vec, Vec, Vec] = (
        (1, 0, 0),
        (0, 1, 0),
        (0, 0, 1),
    )
    result: set[Tuple[Vec, ...]] = set()
    for second_sign, third_sign in product((-1, 1), repeat=2):
        signs = (1, second_sign, third_sign)
        generators = [
            tuple(signs[j] * coordinate_vectors[j][i] for i in range(3))
            for j in range(3)
        ]
        modes = set()
        for coefficients in product((0, 1), repeat=3):
            if coefficients == (0, 0, 0):
                continue
            mode = tuple(
                sum(coefficients[j] * generators[j][i] for j in range(3))
                for i in range(3)
            )
            modes.add(unoriented(mode))  # type: ignore[arg-type]
        result.add(tuple(sorted(modes)))
    return result


def audit_seven_mode_minimizers(
    representatives: Sequence[Vec],
    grouped: Dict[TriadSupport, List[List[Fraction]]],
) -> List[Tuple[Vec, ...]]:
    """Exactly identify every rank-26 seven-mode subset in the unit cube."""
    by_mask = primitive_rows_by_support_mask(representatives, grouped)
    winners: List[Tuple[Vec, ...]] = []
    for indices in combinations(range(len(representatives)), 7):
        mask = sum(1 << index for index in indices)
        columns = [4 * index + offset for index in indices for offset in range(4)]
        local_rows = (
            [row[column] for column in columns]
            for support_mask, rows in by_mask.items()
            if not support_mask & ~mask
            for row in rows
        )
        if integer_rank(local_rows) == 26:
            winners.append(tuple(representatives[index] for index in indices))
    assert set(winners) == expected_orthant_seeds()
    return winners


def audit_boolean_seed() -> tuple[int, int, int, int]:
    """Check the Hermitian and unrestricted ranks on the seven-mode seed."""
    representatives = list(BOOLEAN_SEED_REPRESENTATIVES)
    vectors = boolean_seed_vectors()
    vector_set = set(vectors)
    hermitian_rows: List[List[Fraction]] = []
    general_rows: List[List[Fraction]] = []
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if (
                r not in vector_set
                or not (p <= q <= r)
                or cross(p, q) == (0, 0, 0)
            ):
                continue
            hermitian_rows.extend(triad_rows(p, q, r, representatives))
            general_rows.extend(general_triad_rows(p, q, r, representatives))
    hermitian_rank = exact_rank(hermitian_rows)
    general_rank = general_exact_rank(general_rows)
    assert hermitian_rank == 4 * len(representatives) - 2 == 26
    assert general_rank == 8 * len(representatives) - 2 == 54
    return len(hermitian_rows), hermitian_rank, len(general_rows), general_rank


def main() -> None:
    representatives, grouped = hermitian_support_rows()
    subsets, exact_checks, rank_ceilings = audit_smaller_subsets(
        representatives, grouped
    )
    print(
        "Unit-cube lower bound: PASS "
        f"({subsets} subsets of one through six modes; "
        f"{exact_checks} potentially competitive cases reduced exactly over Q)"
    )
    print(f"certified rank ceilings by size: {rank_ceilings}")

    winners = audit_seven_mode_minimizers(representatives, grouped)
    print(
        "Seven-mode minimizer classification: PASS "
        f"({len(winners)} winners, exactly the four coordinate-sign orthants)"
    )

    hermitian_rows, hermitian_rank, general_rows, general_rank = audit_boolean_seed()
    print(
        "Seven-mode Boolean seed: PASS "
        f"({hermitian_rows} Hermitian rows, rank {hermitian_rank}/28; "
        f"{general_rows} unrestricted rows, rank {general_rank}/56)"
    )
    print(
        "Minimality implication: PASS (an extra Hermitian kernel vector would "
        "also be an unrestricted-symbol kernel vector)"
    )


if __name__ == "__main__":
    main()
