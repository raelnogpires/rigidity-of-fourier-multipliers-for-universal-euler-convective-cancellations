#!/usr/bin/env python3
"""Exact checks for the whitened Fourier frame and full Gram-shape flow.

The checks use rational matrices throughout.  They verify that whitening the
active Fourier Gram vectors gives a Parseval frame, identify the normalized
dissipation as its shell-weighted moment, audit the unit-determinant affine
shape equation, and check the sharp universal shape-rate constants.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Sequence

from verify_active_subspace_geometry import (
    RMatrix,
    WeightedMode,
    second_elementary_symmetric,
    trace,
    weighted_gram,
)
from verify_adaptive_miller_metric import (
    matrix_inner,
    matrix_inverse,
    matrix_multiply,
    matrix_scale,
    matrix_subtract,
)
from verify_planarity_shape_dynamics import shape_gradient


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


def add_matrices(left: RMatrix, right: RMatrix) -> RMatrix:
    return tuple(
        tuple(left[i][j] + right[i][j] for j in range(3)) for i in range(3)
    )


def negate(matrix: RMatrix) -> RMatrix:
    return matrix_scale(matrix, Fraction(-1))


def norm_squared_integer(vector: Sequence[int]) -> int:
    return sum(component * component for component in vector)


def matrix_vector(matrix: RMatrix, vector: Sequence[int]) -> tuple[Fraction, ...]:
    return tuple(
        sum(matrix[i][j] * vector[j] for j in range(3)) for i in range(3)
    )


def weighted_outer_sum(
    modes: Sequence[WeightedMode],
    inverse_square_root: RMatrix,
    shell_weighted: bool = False,
    centered_shell: Fraction | None = None,
) -> RMatrix:
    result = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for wavevector, weight in modes:
        whitened = matrix_vector(inverse_square_root, wavevector)
        shell = Fraction(norm_squared_integer(wavevector))
        if centered_shell is not None:
            shell -= centered_shell
        elif not shell_weighted:
            shell = Fraction(1)
        coefficient = weight * shell
        for i in range(3):
            for j in range(3):
                result[i][j] += coefficient * whitened[i] * whitened[j]
    return tuple(tuple(row) for row in result)


def deviatoric(matrix: RMatrix) -> RMatrix:
    return matrix_subtract(
        matrix,
        matrix_scale(identity_matrix(), trace(matrix) / 3),
    )


def affine_shape_cotangent(matrix: RMatrix) -> RMatrix:
    """B=M^(1/2) G(M) M^(1/2), written without a square root."""
    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    matrix_squared = matrix_multiply(matrix, matrix)
    area_term = matrix_scale(
        matrix_subtract(matrix_scale(matrix, mass), matrix_squared),
        Fraction(1, 1) / area,
    )
    return matrix_subtract(
        matrix_subtract(
            identity_matrix(), matrix_scale(matrix, Fraction(1, 1) / mass)
        ),
        area_term,
    )


def diagonal_spectral_diameter(matrix: RMatrix) -> Fraction:
    assert all(matrix[i][j] == 0 for i in range(3) for j in range(3) if i != j)
    eigenvalues = [matrix[i][i] for i in range(3)]
    return max(eigenvalues) - min(eigenvalues)


def check_whitened_tight_frame() -> None:
    modes: tuple[WeightedMode, ...] = (
        ((1, 0, 0), Fraction(5)),
        ((2, 0, 0), Fraction(1)),
        ((0, 1, 0), Fraction(7)),
        ((0, 3, 0), Fraction(1)),
        ((0, 0, 1), Fraction(5)),
        ((0, 0, 2), Fraction(1)),
    )
    matrix = weighted_gram(modes)
    inverse_square_root = diagonal((Fraction(1, 3), Fraction(1, 4), Fraction(1, 3)))
    assert matrix == diagonal((9, 16, 9))
    assert weighted_outer_sum(modes, inverse_square_root) == identity_matrix()

    dissipation_modes = tuple(
        (wavevector, weight * norm_squared_integer(wavevector))
        for wavevector, weight in modes
    )
    dissipation = weighted_gram(dissipation_modes)
    normalized = matrix_multiply(
        inverse_square_root,
        matrix_multiply(dissipation, inverse_square_root),
    )
    assert normalized == weighted_outer_sum(
        modes, inverse_square_root, shell_weighted=True
    )
    assert normalized == diagonal((Fraction(7, 3), Fraction(11, 2), Fraction(7, 3)))

    shell_mean = trace(normalized) / 3
    assert deviatoric(normalized) == weighted_outer_sum(
        modes, inverse_square_root, centered_shell=shell_mean
    )


def check_shell_band_and_single_shell() -> None:
    sharp_modes: tuple[WeightedMode, ...] = (
        ((1, 0, 0), Fraction(1)),
        ((0, 1, 0), Fraction(1)),
        ((0, 0, 3), Fraction(1)),
    )
    matrix = weighted_gram(sharp_modes)
    inverse_square_root = diagonal((1, 1, Fraction(1, 3)))
    normalized = weighted_outer_sum(
        sharp_modes, inverse_square_root, shell_weighted=True
    )
    assert matrix == diagonal((1, 1, 9))
    assert normalized == diagonal((1, 1, 9))
    assert diagonal_spectral_diameter(normalized) == 9 - 1

    single_shell_modes: tuple[WeightedMode, ...] = (
        ((1, 0, 0), Fraction(1)),
        ((0, 1, 0), Fraction(2)),
        ((0, 0, 1), Fraction(4)),
    )
    single_matrix = weighted_gram(single_shell_modes)
    single_dissipation = weighted_gram(single_shell_modes)
    assert single_matrix == diagonal((1, 2, 4))
    assert single_dissipation == single_matrix
    assert matrix_inner(shape_gradient(single_matrix), single_dissipation) == 0


def check_unit_determinant_shape_equation() -> None:
    square_root = (
        (Fraction(2), Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    inverse_square_root = matrix_inverse(square_root)
    matrix = matrix_multiply(square_root, square_root)
    driver = (
        (Fraction(2), Fraction(1), Fraction(-1)),
        (Fraction(1), Fraction(-1), Fraction(2)),
        (Fraction(-1), Fraction(2), Fraction(3)),
    )
    matrix_dot = negate(
        matrix_multiply(square_root, matrix_multiply(driver, square_root))
    )
    relative_velocity = matrix_multiply(
        inverse_square_root,
        matrix_multiply(matrix_dot, inverse_square_root),
    )
    assert relative_velocity == negate(driver)
    assert deviatoric(relative_velocity) == negate(deviatoric(driver))

    cotangent = affine_shape_cotangent(matrix)
    gradient = shape_gradient(matrix)
    assert cotangent == matrix_multiply(
        square_root, matrix_multiply(gradient, square_root)
    )
    assert trace(cotangent) == matrix_inner(gradient, matrix) == 0
    forcing = negate(matrix_dot)
    assert matrix_inner(gradient, forcing) == matrix_inner(cotangent, driver)


def check_condition_number_rate() -> None:
    matrix = diagonal((1, 4, 9))
    square_root = diagonal((1, 2, 3))
    inverse_square_root = diagonal((1, Fraction(1, 2), Fraction(1, 3)))
    for entries in product(range(-3, 4), repeat=3):
        driver = diagonal(entries)
        matrix_dot = negate(
            matrix_multiply(square_root, matrix_multiply(driver, square_root))
        )
        relative_velocity = matrix_multiply(
            inverse_square_root,
            matrix_multiply(matrix_dot, inverse_square_root),
        )
        assert relative_velocity == negate(driver)
        log_condition_rate = matrix_dot[2][2] / matrix[2][2] - matrix_dot[0][0]
        assert abs(log_condition_rate) <= diagonal_spectral_diameter(driver)


def check_sharp_shape_rate_bound() -> None:
    for eigenvalues in product(range(1, 13), repeat=3):
        matrix = diagonal(eigenvalues)
        cotangent = affine_shape_cotangent(matrix)
        assert trace(cotangent) == 0
        assert sum(abs(cotangent[i][i]) for i in range(3)) <= 2

        for driver_entries in ((-2, 1, 4), (3, -1, 0), (5, 5, -2)):
            driver = diagonal(driver_entries)
            rate = matrix_inner(cotangent, driver)
            assert abs(rate) <= diagonal_spectral_diameter(driver)

    deficits = []
    for denominator in (10, 100, 1000):
        matrix = diagonal((Fraction(1, denominator), 1, 1))
        cotangent = affine_shape_cotangent(matrix)
        nuclear_norm = sum(abs(cotangent[i][i]) for i in range(3))
        assert nuclear_norm < 2
        deficits.append(2 - nuclear_norm)
        unit_diameter_driver = diagonal((1, 0, 0))
        assert matrix_inner(cotangent, unit_diameter_driver) > 0
    assert deficits[0] > deficits[1] > deficits[2] > 0


def main() -> None:
    check_whitened_tight_frame()
    print("Whitened active wavevectors form an exact Parseval frame: PASS")
    check_shell_band_and_single_shell()
    print("Shell-band bound and single-shell viscous neutrality: PASS")
    check_unit_determinant_shape_equation()
    print("Unit-determinant affine Gram-shape equation: PASS")
    check_condition_number_rate()
    print("Spectral-diameter condition-number rate: PASS")
    check_sharp_shape_rate_bound()
    print("Sharp universal scalar shape-rate constant: PASS")
    print("All exact whitened Gram-shape checks passed.")


if __name__ == "__main__":
    main()
