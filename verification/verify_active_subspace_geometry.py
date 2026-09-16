#!/usr/bin/env python3
"""Exact checks for the active Fourier geometry of the Gram tensor M.

The checks use rational Gaussian Fourier coefficients.  They verify the
modewise strain weight, the Cauchy--Binet spectral-volume formulas in ranks
one through three, and invariance of a genuinely three-component planar
Fourier support under the Navier--Stokes vector field.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Iterable, Sequence, Tuple

from explore_full_multiplier import Gaussian, ONE, ZERO, gadd, gmul
from verify_adaptive_miller_metric import (
    VectorField,
    add_real_mode,
    gram_tensor,
    ns_velocity_derivative,
    real,
    strain_field,
)
from verify_laplacian_rigidity import Vec, neg

RMatrix = Tuple[Tuple[Fraction, Fraction, Fraction], ...]
WeightedMode = Tuple[Vec, Fraction]


def gaussian_norm_squared(value: Gaussian) -> Fraction:
    return value[0] * value[0] + value[1] * value[1]


def vector_norm_squared(value: Sequence[Gaussian]) -> Fraction:
    return sum(gaussian_norm_squared(component) for component in value)


def matrix_norm_squared_against_opposite(
    left: Sequence[Sequence[Gaussian]],
    right: Sequence[Sequence[Gaussian]],
) -> Fraction:
    total = ZERO
    for i in range(3):
        for j in range(3):
            total = gadd(total, gmul(left[i][j], right[i][j]))
    return real(total)


def weighted_gram(modes: Iterable[WeightedMode]) -> RMatrix:
    result = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for k, weight in modes:
        for a in range(3):
            for b in range(3):
                result[a][b] += weight * k[a] * k[b]
    return tuple(tuple(row) for row in result)


def determinant(matrix: RMatrix) -> Fraction:
    return (
        matrix[0][0]
        * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1]
        * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2]
        * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


def trace(matrix: RMatrix) -> Fraction:
    return sum(matrix[i][i] for i in range(3))


def second_elementary_symmetric(matrix: RMatrix) -> Fraction:
    return (
        matrix[0][0] * matrix[1][1]
        - matrix[0][1] * matrix[1][0]
        + matrix[0][0] * matrix[2][2]
        - matrix[0][2] * matrix[2][0]
        + matrix[1][1] * matrix[2][2]
        - matrix[1][2] * matrix[2][1]
    )


def cross(left: Vec, right: Vec) -> Vec:
    return (
        left[1] * right[2] - left[2] * right[1],
        left[2] * right[0] - left[0] * right[2],
        left[0] * right[1] - left[1] * right[0],
    )


def integer_norm_squared(value: Vec) -> int:
    return sum(component * component for component in value)


def scalar_triple(first: Vec, second: Vec, third: Vec) -> int:
    normal = cross(second, third)
    return sum(first[i] * normal[i] for i in range(3))


def rank(matrix: RMatrix) -> int:
    work = [list(row) for row in matrix]
    pivot_row = 0
    for column in range(3):
        pivot = next(
            (row for row in range(pivot_row, 3) if work[row][column]), None
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        scale = work[pivot_row][column]
        work[pivot_row] = [value / scale for value in work[pivot_row]]
        for row in range(3):
            if row == pivot_row or not work[row][column]:
                continue
            factor = work[row][column]
            work[row] = [
                work[row][j] - factor * work[pivot_row][j] for j in range(3)
            ]
        pivot_row += 1
    return pivot_row


def spectral_volume(modes: Sequence[WeightedMode], dimension: int) -> Fraction:
    if dimension == 1:
        return sum(weight * integer_norm_squared(k) for k, weight in modes)
    if dimension == 2:
        return sum(
            left_weight
            * right_weight
            * integer_norm_squared(cross(left, right))
            for (left, left_weight), (right, right_weight) in combinations(modes, 2)
        )
    if dimension == 3:
        return sum(
            first_weight
            * second_weight
            * third_weight
            * scalar_triple(first, second, third) ** 2
            for (
                (first, first_weight),
                (second, second_weight),
                (third, third_weight),
            ) in combinations(modes, 3)
        )
    raise ValueError("dimension must be 1, 2, or 3")


def check_abstract_cauchy_binet() -> None:
    examples = (
        (
            (((1, 0, 0), Fraction(2)), ((2, 0, 0), Fraction(3))),
            1,
        ),
        (
            (
                ((1, 0, 0), Fraction(2)),
                ((0, 1, 0), Fraction(3)),
                ((1, 1, 0), Fraction(5)),
            ),
            2,
        ),
        (
            (
                ((1, 0, 0), Fraction(2)),
                ((0, 1, 0), Fraction(3)),
                ((1, 1, 0), Fraction(5)),
                ((0, 0, 1), Fraction(7)),
                ((1, 1, 1), Fraction(11)),
            ),
            3,
        ),
    )
    for modes, expected_rank in examples:
        matrix = weighted_gram(modes)
        assert rank(matrix) == expected_rank
        if expected_rank == 1:
            pseudodeterminant = trace(matrix)
        elif expected_rank == 2:
            pseudodeterminant = second_elementary_symmetric(matrix)
        else:
            pseudodeterminant = determinant(matrix)
        assert pseudodeterminant == spectral_volume(modes, expected_rank)


def check_fourier_strain_weights() -> None:
    field: VectorField = {}
    data = (
        ((1, 0, 0), (0, 1, 2), ONE),
        ((0, 1, 0), (2, 0, -1), (Fraction(0), Fraction(1))),
        ((0, 0, 1), (1, -2, 0), (Fraction(1), Fraction(1))),
        ((1, 1, 0), (1, -1, 3), (Fraction(2), Fraction(-1))),
    )
    for k, polarization, phase in data:
        add_real_mode(field, k, polarization, phase)

    strains = strain_field(field)
    modes = []
    for k, _, _ in data:
        strain_weight = matrix_norm_squared_against_opposite(
            strains[k], strains[neg(k)]
        )
        expected = Fraction(integer_norm_squared(k), 2) * vector_norm_squared(
            field[k]
        )
        assert strain_weight == expected
        modes.append((k, 2 * strain_weight))

    matrix = gram_tensor(strains)
    assert matrix == weighted_gram(modes)
    assert rank(matrix) == 3
    assert determinant(matrix) == spectral_volume(modes, 3) > 0


def check_planar_support_invariance() -> None:
    field: VectorField = {}
    # All three velocity components occur, while every wavevector lies in z=0.
    add_real_mode(field, (1, 0, 0), (0, 2, 1), ONE)
    add_real_mode(field, (0, 1, 0), (3, 0, -1), (Fraction(0), Fraction(1)))
    add_real_mode(field, (1, 1, 0), (1, -1, 2), (Fraction(1), Fraction(1)))

    strains = strain_field(field)
    matrix = gram_tensor(strains)
    assert rank(matrix) == 2
    assert all(matrix[2][j] == matrix[j][2] == 0 for j in range(3))

    modes = []
    for k in ((1, 0, 0), (0, 1, 0), (1, 1, 0)):
        weight = 2 * matrix_norm_squared_against_opposite(
            strains[k], strains[neg(k)]
        )
        modes.append((k, weight))
    assert second_elementary_symmetric(matrix) == spectral_volume(modes, 2) > 0

    derivative = ns_velocity_derivative(field, Fraction(3, 5))
    assert derivative
    assert all(k[2] == 0 for k in derivative)


def main() -> None:
    check_abstract_cauchy_binet()
    print("Cauchy--Binet active-volume formulas: PASS (ranks 1, 2, and 3)")
    check_fourier_strain_weights()
    print("Fourier strain weights and full-rank Gram geometry: PASS")
    check_planar_support_invariance()
    print("Planar 2D3C support under the Navier--Stokes vector field: PASS")
    print("All exact active-subspace geometry checks passed.")


if __name__ == "__main__":
    main()
