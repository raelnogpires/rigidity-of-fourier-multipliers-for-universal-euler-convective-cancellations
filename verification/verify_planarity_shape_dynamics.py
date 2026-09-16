#!/usr/bin/env python3
"""Exact checks for the scale-free shape dynamics of the Gram tensor M.

The script verifies the compound Cauchy--Binet cofactor identity, the
dimensionless planarity factor and its shape gradient, the induced evolution
law along Navier--Stokes, and exact Fourier witnesses showing that neither
the nonlinear nor the viscous shape drift has a universal sign.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations
from typing import Sequence

from explore_full_multiplier import Gaussian, ONE
from verify_active_subspace_geometry import (
    RMatrix,
    WeightedMode,
    cross,
    determinant,
    second_elementary_symmetric,
    spectral_volume,
    trace,
    weighted_gram,
)
from verify_adaptive_miller_metric import (
    VectorField,
    add_real_mode,
    add_rmatrices,
    directional_tensor,
    energy_cross_term,
    gram_tensor,
    matrix_inner,
    matrix_inverse,
    matrix_scale,
    matrix_subtract,
    ns_velocity_derivative,
    production_tensor,
    strain_field,
    symmetric_coefficient_tensor,
)
from verify_tensorial_miller_identity import curl_field


def zero_matrix() -> RMatrix:
    return tuple(tuple(Fraction(0) for _ in range(3)) for _ in range(3))


def identity_matrix() -> RMatrix:
    return tuple(
        tuple(Fraction(i == j) for j in range(3)) for i in range(3)
    )


def diagonal(values: Sequence[int | Fraction]) -> RMatrix:
    return tuple(
        tuple(Fraction(values[i]) if i == j else Fraction(0) for j in range(3))
        for i in range(3)
    )


def cofactor(matrix: RMatrix) -> RMatrix:
    result = []
    for row in range(3):
        result_row = []
        other_rows = [index for index in range(3) if index != row]
        for column in range(3):
            other_columns = [index for index in range(3) if index != column]
            minor = (
                matrix[other_rows[0]][other_columns[0]]
                * matrix[other_rows[1]][other_columns[1]]
                - matrix[other_rows[0]][other_columns[1]]
                * matrix[other_rows[1]][other_columns[0]]
            )
            result_row.append((-1) ** (row + column) * minor)
        result.append(tuple(result_row))
    return tuple(result)


def cross_outer_sum(modes: Sequence[WeightedMode]) -> RMatrix:
    result = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for (left, left_weight), (right, right_weight) in combinations(modes, 2):
        normal = cross(left, right)
        for a in range(3):
            for b in range(3):
                result[a][b] += left_weight * right_weight * normal[a] * normal[b]
    return tuple(tuple(row) for row in result)


def shape_factor(matrix: RMatrix) -> Fraction:
    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    return 9 * determinant(matrix) / (mass * area)


def shape_gradient(matrix: RMatrix) -> RMatrix:
    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    radial = matrix_scale(identity_matrix(), Fraction(1, 1) / mass)
    area_gradient = matrix_scale(
        matrix_subtract(matrix_scale(identity_matrix(), mass), matrix),
        Fraction(1, 1) / area,
    )
    return matrix_subtract(
        matrix_subtract(matrix_inverse(matrix), radial), area_gradient
    )


def combined_production(field: VectorField) -> RMatrix:
    strains = strain_field(field)
    vorticity = curl_field(field)
    q_tensor = directional_tensor(strains, vorticity, vorticity)
    p_tensor = production_tensor(field, strains)
    return matrix_subtract(
        matrix_scale(p_tensor, Fraction(2)),
        matrix_scale(q_tensor, Fraction(1, 2)),
    )


def gram_derivative(field: VectorField, viscosity: Fraction) -> RMatrix:
    strains = strain_field(field)
    strains_dot = strain_field(ns_velocity_derivative(field, viscosity))
    return symmetric_coefficient_tensor(
        lambda test_matrix: 2
        * energy_cross_term(test_matrix, strains_dot, strains)
    )


def scaled_phase(scale: Fraction, phase: Gaussian) -> Gaussian:
    return scale * phase[0], scale * phase[1]


def nonlinear_shape_field(last_phase: Gaussian, scale: Fraction) -> VectorField:
    field: VectorField = {}
    data = (
        ((1, 0, 0), (0, 0, 1), ONE),
        ((0, 1, 0), (0, 0, -1), (Fraction(1), Fraction(1))),
        ((1, 1, 0), (1, -1, 0), last_phase),
        ((0, 0, 1), (0, 1, 0), ONE),
    )
    for wavevector, polarization, phase in data:
        add_real_mode(field, wavevector, polarization, scaled_phase(scale, phase))
    return field


def axial_shape_field(high_frequency_axis: int) -> VectorField:
    field: VectorField = {}
    if high_frequency_axis == 0:
        data = (
            ((3, 0, 0), (0, 1, 0), (Fraction(1, 9), Fraction(0))),
            ((0, 1, 0), (1, 0, 1), ONE),
            ((0, 0, 1), (2, 0, 0), ONE),
        )
    elif high_frequency_axis == 2:
        data = (
            ((1, 0, 0), (0, 1, 0), ONE),
            ((0, 1, 0), (1, 0, 1), ONE),
            ((0, 0, 3), (2, 0, 0), (Fraction(1, 9), Fraction(0))),
        )
    else:
        raise ValueError("the witness uses axis zero or two")
    for wavevector, polarization, phase in data:
        add_real_mode(field, wavevector, polarization, phase)
    return field


def check_compound_cauchy_binet() -> None:
    modes: tuple[WeightedMode, ...] = (
        ((1, 0, 0), Fraction(2)),
        ((0, 1, 0), Fraction(3)),
        ((1, 1, 0), Fraction(5)),
        ((0, 0, 1), Fraction(7)),
        ((1, 1, 1), Fraction(11)),
    )
    matrix = weighted_gram(modes)
    compound = cofactor(matrix)
    assert compound == cross_outer_sum(modes)
    assert trace(compound) == spectral_volume(modes, 2)
    assert determinant(matrix) == spectral_volume(modes, 3)


def check_shape_factor_and_gradient() -> None:
    for eigenvalues in ((1, 1, 1), (1, 2, 4), (1, 3, 20), (2, 5, 5)):
        matrix = diagonal(eigenvalues)
        beta = shape_factor(matrix)
        smallest_fraction = Fraction(min(eigenvalues), sum(eigenvalues))
        assert 0 < beta <= 1
        assert beta / 9 <= smallest_fraction <= beta / 3

        gradient = shape_gradient(matrix)
        assert matrix_inner(gradient, matrix) == 0
        mass = trace(matrix)
        area = second_elementary_symmetric(matrix)
        for index in range(3):
            others = [eigenvalues[j] for j in range(3) if j != index]
            expected = Fraction(
                (others[0] + others[1])
                * (others[0] * others[1] - eigenvalues[index] ** 2),
                eigenvalues[index] * mass * area,
            )
            assert gradient[index][index] == expected

    matrix = (
        (Fraction(5), Fraction(4), Fraction(0)),
        (Fraction(4), Fraction(6), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    direction = (
        (Fraction(2), Fraction(-1), Fraction(1, 3)),
        (Fraction(-1), Fraction(3), Fraction(2, 5)),
        (Fraction(1, 3), Fraction(2, 5), Fraction(-2)),
    )
    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    direct_derivative = (
        matrix_inner(cofactor(matrix), direction) / determinant(matrix)
        - trace(direction) / mass
        - matrix_inner(
            matrix_subtract(matrix_scale(identity_matrix(), mass), matrix),
            direction,
        )
        / area
    )
    assert direct_derivative == matrix_inner(shape_gradient(matrix), direction)


def check_navier_stokes_shape_law() -> None:
    viscosity = Fraction(1, 10)
    amplitude = Fraction(2)
    base_m = (
        (Fraction(5), Fraction(4), Fraction(0)),
        (Fraction(4), Fraction(6), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    base_n = (
        (Fraction(9), Fraction(8), Fraction(0)),
        (Fraction(8), Fraction(10), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    positive_c = diagonal((2, -2, 0))
    expected_rates = (Fraction(2, 525), Fraction(-26, 105))
    cases = (
        ((Fraction(0), Fraction(1)), positive_c),
        (ONE, matrix_scale(positive_c, Fraction(-1))),
    )
    observed_rates = []
    for (last_phase, base_c), expected_rate in zip(cases, expected_rates):
        field = nonlinear_shape_field(last_phase, amplitude)
        strains = strain_field(field)
        matrix = gram_tensor(strains)
        dissipation = gram_tensor(strains, extra_laplacian=True)
        production = combined_production(field)
        assert matrix == matrix_scale(base_m, amplitude**2)
        assert dissipation == matrix_scale(base_n, amplitude**2)
        assert production == matrix_scale(base_c, amplitude**3)

        gradient = shape_gradient(matrix)
        rate = matrix_inner(gradient, production) + 2 * viscosity * matrix_inner(
            gradient, dissipation
        )
        assert rate == expected_rate
        matrix_dot = gram_derivative(field, viscosity)
        assert add_rmatrices(
            matrix_dot,
            matrix_scale(dissipation, 2 * viscosity),
            production,
        ) == zero_matrix()
        assert matrix_inner(gradient, matrix_dot) == -rate
        observed_rates.append(rate)
    assert observed_rates[0] > 0 > observed_rates[1]


def check_viscous_sign_indefiniteness() -> None:
    expected_m = diagonal((1, 2, 4))
    expected_n = (diagonal((9, 2, 4)), diagonal((1, 2, 36)))
    expected_contractions = (Fraction(24, 7), Fraction(-24, 7))
    for axis, dissipation_expected, contraction_expected in zip(
        (0, 2), expected_n, expected_contractions
    ):
        field = axial_shape_field(axis)
        strains = strain_field(field)
        matrix = gram_tensor(strains)
        dissipation = gram_tensor(strains, extra_laplacian=True)
        production = combined_production(field)
        assert matrix == expected_m
        assert dissipation == dissipation_expected
        assert production == zero_matrix()
        assert (
            matrix_inner(shape_gradient(matrix), dissipation)
            == contraction_expected
        )


def main() -> None:
    check_compound_cauchy_binet()
    print("Compound Cauchy--Binet cofactor tensor: PASS")
    check_shape_factor_and_gradient()
    print("Scale-free planarity factor and exact shape gradient: PASS")
    check_navier_stokes_shape_law()
    print("Navier--Stokes shape law and opposite nonlinear drifts: PASS")
    check_viscous_sign_indefiniteness()
    print("Opposite viscous planarity drifts on exact Fourier states: PASS")
    print("All exact planarity-shape checks passed.")


if __name__ == "__main__":
    main()
