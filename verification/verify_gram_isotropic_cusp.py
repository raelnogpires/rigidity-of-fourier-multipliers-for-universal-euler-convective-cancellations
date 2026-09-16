#!/usr/bin/env python3
"""Exact checks for the isotropic cusp of Gram spectral-shape space.

The verifier rewrites the two rational Gram coordinates as the quadratic and
cubic invariants of the normalized traceless Gram tensor.  Exact Taylor
arithmetic through order six then resolves the triple-eigenvalue point: the
two scalar rates emerge linearly, the signed branch coordinate emerges
cubically, and the realizability discriminant emerges at sixth order.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Sequence

from verify_active_subspace_geometry import (
    RMatrix,
    determinant,
    second_elementary_symmetric,
    trace,
)
from verify_adaptive_miller_metric import (
    matrix_inner,
    matrix_multiply,
    matrix_scale,
    matrix_subtract,
)
from verify_gram_shape_coordinates import (
    affine_eta_cotangent,
    realizability_polynomial,
    shape_coordinates,
)
from verify_whitened_gram_shape import affine_shape_cotangent

ORDER = 6
Series = tuple[Fraction, ...]
SeriesMatrix = tuple[tuple[Series, Series, Series], ...]


def identity_matrix() -> RMatrix:
    return tuple(
        tuple(Fraction(i == j) for j in range(3)) for i in range(3)
    )


def diagonal(values: Sequence[int | Fraction]) -> RMatrix:
    return tuple(
        tuple(Fraction(values[i]) if i == j else Fraction(0) for j in range(3))
        for i in range(3)
    )


def matrix_deviatoric(matrix: RMatrix) -> RMatrix:
    return matrix_subtract(
        matrix,
        matrix_scale(identity_matrix(), trace(matrix) / 3),
    )


def normalized_anisotropy(matrix: RMatrix) -> RMatrix:
    return matrix_subtract(
        matrix_scale(matrix, Fraction(1, 1) / trace(matrix)),
        matrix_scale(identity_matrix(), Fraction(1, 3)),
    )


def signed_branch_coordinate(eta: Fraction, chi: Fraction) -> Fraction:
    return eta * chi - 3 * eta + 2


def series_constant(value: int | Fraction) -> Series:
    return (Fraction(value),) + (Fraction(0),) * ORDER


def series_linear(value: int | Fraction, derivative: int | Fraction) -> Series:
    return (Fraction(value), Fraction(derivative)) + (Fraction(0),) * (ORDER - 1)


def series_add(left: Series, right: Series) -> Series:
    return tuple(left[index] + right[index] for index in range(ORDER + 1))


def series_scale(value: Series, scalar: int | Fraction) -> Series:
    return tuple(Fraction(scalar) * entry for entry in value)


def series_subtract(left: Series, right: Series) -> Series:
    return series_add(left, series_scale(right, -1))


def series_multiply(left: Series, right: Series) -> Series:
    return tuple(
        sum(left[index] * right[degree - index] for index in range(degree + 1))
        for degree in range(ORDER + 1)
    )


def series_inverse(value: Series) -> Series:
    result = [Fraction(0) for _ in range(ORDER + 1)]
    result[0] = 1 / value[0]
    for degree in range(1, ORDER + 1):
        result[degree] = -sum(
            value[index] * result[degree - index]
            for index in range(1, degree + 1)
        ) / value[0]
    return tuple(result)


def series_divide(numerator: Series, denominator: Series) -> Series:
    return series_multiply(numerator, series_inverse(denominator))


def series_sum(values: Sequence[Series]) -> Series:
    result = series_constant(0)
    for value in values:
        result = series_add(result, value)
    return result


def series_derivative(value: Series) -> Series:
    return tuple(
        Fraction(index + 1) * value[index + 1] if index < ORDER else Fraction(0)
        for index in range(ORDER + 1)
    )


def series_second_invariant(matrix: SeriesMatrix) -> Series:
    return series_sum(
        (
            series_subtract(
                series_multiply(matrix[0][0], matrix[1][1]),
                series_multiply(matrix[0][1], matrix[1][0]),
            ),
            series_subtract(
                series_multiply(matrix[0][0], matrix[2][2]),
                series_multiply(matrix[0][2], matrix[2][0]),
            ),
            series_subtract(
                series_multiply(matrix[1][1], matrix[2][2]),
                series_multiply(matrix[1][2], matrix[2][1]),
            ),
        )
    )


def series_determinant(matrix: SeriesMatrix) -> Series:
    return series_add(
        series_subtract(
            series_multiply(
                matrix[0][0],
                series_subtract(
                    series_multiply(matrix[1][1], matrix[2][2]),
                    series_multiply(matrix[1][2], matrix[2][1]),
                ),
            ),
            series_multiply(
                matrix[0][1],
                series_subtract(
                    series_multiply(matrix[1][0], matrix[2][2]),
                    series_multiply(matrix[1][2], matrix[2][0]),
                ),
            ),
        ),
        series_multiply(
            matrix[0][2],
            series_subtract(
                series_multiply(matrix[1][0], matrix[2][1]),
                series_multiply(matrix[1][1], matrix[2][0]),
            ),
        ),
    )


def series_shape_coordinates(matrix: SeriesMatrix) -> tuple[Series, Series]:
    mass = series_sum(tuple(matrix[index][index] for index in range(3)))
    area = series_second_invariant(matrix)
    determinant_series = series_determinant(matrix)
    eta = series_scale(series_divide(area, series_multiply(mass, mass)), 3)
    chi = series_scale(
        series_divide(determinant_series, series_multiply(mass, area)), 9
    )
    return eta, chi


def series_branch_coordinate(eta: Series, chi: Series) -> Series:
    return series_add(
        series_subtract(series_multiply(eta, chi), series_scale(eta, 3)),
        series_constant(2),
    )


def series_realizability(eta: Series, chi: Series) -> Series:
    bracket = series_add(
        series_add(
            series_subtract(series_constant(3), series_scale(eta, 4)),
            series_scale(chi, 6),
        ),
        series_scale(series_multiply(chi, chi), -1),
    )
    return series_subtract(series_multiply(eta, bracket), series_scale(chi, 4))


def check_exact_cusp_coordinates() -> None:
    matrices = [diagonal(values) for values in product(range(1, 8), repeat=3)]
    matrices.extend(
        (
            (
                (Fraction(5), Fraction(4), Fraction(0)),
                (Fraction(4), Fraction(5), Fraction(0)),
                (Fraction(0), Fraction(0), Fraction(1)),
            ),
            (
                (Fraction(10), Fraction(4), Fraction(2)),
                (Fraction(4), Fraction(9), Fraction(2)),
                (Fraction(2), Fraction(2), Fraction(5)),
            ),
        )
    )
    for matrix in matrices:
        eta, chi = shape_coordinates(matrix)
        anisotropy = normalized_anisotropy(matrix)
        quadratic = matrix_inner(anisotropy, anisotropy)
        cubic = determinant(anisotropy)
        beta = signed_branch_coordinate(eta, chi)
        boundary = realizability_polynomial(eta, chi)

        assert 1 - eta == Fraction(3, 2) * quadratic
        assert beta == 27 * cubic
        assert eta * boundary == 4 * (1 - eta) ** 3 - beta**2
        assert quadratic**3 / 2 - 27 * cubic**2 == eta * boundary / 27
        assert beta**2 <= 4 * (1 - eta) ** 3


def check_exact_branch_evolution() -> None:
    square_root: RMatrix = (
        (Fraction(2), Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    matrix = matrix_multiply(square_root, square_root)
    driver: RMatrix = (
        (Fraction(2), Fraction(1), Fraction(-1)),
        (Fraction(1), Fraction(-1), Fraction(2)),
        (Fraction(-1), Fraction(2), Fraction(3)),
    )
    forcing = matrix_multiply(square_root, matrix_multiply(driver, square_root))
    matrix_series: SeriesMatrix = tuple(
        tuple(series_linear(matrix[i][j], -forcing[i][j]) for j in range(3))
        for i in range(3)
    )
    eta_series, chi_series = series_shape_coordinates(matrix_series)
    beta_series = series_branch_coordinate(eta_series, chi_series)
    eta, chi = shape_coordinates(matrix)
    chi_rate = matrix_inner(affine_shape_cotangent(matrix), driver)
    eta_rate = matrix_inner(affine_eta_cotangent(matrix), driver)

    assert eta_series[1] == -eta * eta_rate
    assert chi_series[1] == -chi * chi_rate
    assert beta_series[1] == eta * (
        (3 - chi) * eta_rate - chi * chi_rate
    )


def check_isotropic_high_order_opening() -> None:
    drivers: tuple[RMatrix, ...] = (
        (
            (Fraction(2), Fraction(3), Fraction(-1)),
            (Fraction(3), Fraction(-2), Fraction(4)),
            (Fraction(-1), Fraction(4), Fraction(5)),
        ),
        diagonal((1, 2, 4)),
        diagonal((1, 1, 4)),
        (
            (Fraction(3), Fraction(1), Fraction(2)),
            (Fraction(1), Fraction(0), Fraction(-1)),
            (Fraction(2), Fraction(-1), Fraction(-2)),
        ),
    )
    for scale in (Fraction(1), Fraction(5), Fraction(11, 3)):
        for driver in drivers:
            matrix_series: SeriesMatrix = tuple(
                tuple(
                    series_linear(
                        scale if i == j else Fraction(0),
                        -scale * driver[i][j],
                    )
                    for j in range(3)
                )
                for i in range(3)
            )
            eta, chi = series_shape_coordinates(matrix_series)
            beta = series_branch_coordinate(eta, chi)
            boundary = series_realizability(eta, chi)
            trace_free_driver = matrix_deviatoric(driver)
            quadratic = matrix_inner(trace_free_driver, trace_free_driver)
            cubic = determinant(trace_free_driver)
            driver_discriminant = quadratic**3 / 2 - 27 * cubic**2

            assert eta[:2] == (Fraction(1), Fraction(0))
            assert chi[:2] == (Fraction(1), Fraction(0))
            assert eta[2] == -quadratic / 6
            assert chi[2] == -quadratic / 3
            assert beta[:3] == (Fraction(0),) * 3
            assert beta[3] == -cubic
            assert boundary[:6] == (Fraction(0),) * 6
            assert boundary[6] == driver_discriminant / 27
            assert driver_discriminant >= 0
            if quadratic:
                assert 54 * cubic**2 <= quadratic**3
                assert (54 * cubic**2 == quadratic**3) == (
                    driver_discriminant == 0
                )

            eta_rate = series_scale(
                series_divide(series_derivative(eta), eta), -1
            )
            chi_rate = series_scale(
                series_divide(series_derivative(chi), chi), -1
            )
            assert eta_rate[0] == chi_rate[0] == 0
            assert eta_rate[1] == quadratic / 3
            assert chi_rate[1] == 2 * quadratic / 3


def main() -> None:
    check_exact_cusp_coordinates()
    print("Exact quadratic--cubic Gram cusp coordinates: PASS")
    check_exact_branch_evolution()
    print("Exact signed branch-coordinate evolution: PASS")
    check_isotropic_high_order_opening()
    print("Isotropic second/third/sixth-order opening laws: PASS")
    print("All exact isotropic Gram-cusp checks passed.")


if __name__ == "__main__":
    main()
