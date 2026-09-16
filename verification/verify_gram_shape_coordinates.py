#!/usr/bin/env python3
"""Exact checks for complete scale-free spectral coordinates of the Gram tensor.

For a positive definite 3 by 3 Gram tensor M, the two coordinates

    eta = 3 tr(cof M) / (tr M)^2,
    chi = 9 det M / (tr M tr(cof M))

determine the unordered eigenvalues of M/tr M.  The checks below verify the
normalized characteristic polynomial, its discriminant/realizability region,
the exact eta evolution law, its sharp affine speed bound, and tangency of the
flow at the repeated-eigenvalue boundary.  They also verify the exact
differential conditioning determinant, reconstruct the simple-spectrum
log-eigenvalue velocity, and resolve boundary departure to second order.
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
from verify_planarity_shape_dynamics import shape_factor, shape_gradient
from verify_whitened_gram_shape import (
    affine_shape_cotangent,
    diagonal_spectral_diameter,
)

Jet2 = tuple[Fraction, Fraction, Fraction]


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


def shape_coordinates(matrix: RMatrix) -> tuple[Fraction, Fraction]:
    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    eta = 3 * area / mass**2
    chi = 9 * determinant(matrix) / (mass * area)
    return eta, chi


def normalized_characteristic(
    value: Fraction, eta: Fraction, chi: Fraction
) -> Fraction:
    return value**3 - value**2 + eta * value / 3 - chi * eta / 27


def realizability_polynomial(eta: Fraction, chi: Fraction) -> Fraction:
    return eta * (3 - 4 * eta + 6 * chi - chi**2) - 4 * chi


def jet_constant(value: int | Fraction) -> Jet2:
    return Fraction(value), Fraction(0), Fraction(0)


def jet_add(left: Jet2, right: Jet2) -> Jet2:
    return tuple(left[i] + right[i] for i in range(3))  # type: ignore[return-value]


def jet_scale(value: Jet2, scalar: int | Fraction) -> Jet2:
    return tuple(Fraction(scalar) * entry for entry in value)  # type: ignore[return-value]


def jet_subtract(left: Jet2, right: Jet2) -> Jet2:
    return jet_add(left, jet_scale(right, -1))


def jet_multiply(left: Jet2, right: Jet2) -> Jet2:
    return (
        left[0] * right[0],
        left[1] * right[0] + left[0] * right[1],
        left[2] * right[0] + 2 * left[1] * right[1] + left[0] * right[2],
    )


def jet_inverse(value: Jet2) -> Jet2:
    return (
        1 / value[0],
        -value[1] / value[0] ** 2,
        2 * value[1] ** 2 / value[0] ** 3 - value[2] / value[0] ** 2,
    )


def jet_divide(numerator: Jet2, denominator: Jet2) -> Jet2:
    return jet_multiply(numerator, jet_inverse(denominator))


def jet_sum(values: Sequence[Jet2]) -> Jet2:
    result = jet_constant(0)
    for value in values:
        result = jet_add(result, value)
    return result


def jet_shape_coordinates(
    matrix: tuple[tuple[Jet2, Jet2, Jet2], ...],
) -> tuple[Jet2, Jet2]:
    mass = jet_sum(tuple(matrix[i][i] for i in range(3)))
    area = jet_sum(
        (
            jet_subtract(
                jet_multiply(matrix[0][0], matrix[1][1]),
                jet_multiply(matrix[0][1], matrix[1][0]),
            ),
            jet_subtract(
                jet_multiply(matrix[0][0], matrix[2][2]),
                jet_multiply(matrix[0][2], matrix[2][0]),
            ),
            jet_subtract(
                jet_multiply(matrix[1][1], matrix[2][2]),
                jet_multiply(matrix[1][2], matrix[2][1]),
            ),
        )
    )
    determinant_jet = jet_add(
        jet_subtract(
            jet_multiply(
                matrix[0][0],
                jet_subtract(
                    jet_multiply(matrix[1][1], matrix[2][2]),
                    jet_multiply(matrix[1][2], matrix[2][1]),
                ),
            ),
            jet_multiply(
                matrix[0][1],
                jet_subtract(
                    jet_multiply(matrix[1][0], matrix[2][2]),
                    jet_multiply(matrix[1][2], matrix[2][0]),
                ),
            ),
        ),
        jet_multiply(
            matrix[0][2],
            jet_subtract(
                jet_multiply(matrix[1][0], matrix[2][1]),
                jet_multiply(matrix[1][1], matrix[2][0]),
            ),
        ),
    )
    eta = jet_scale(jet_divide(area, jet_multiply(mass, mass)), 3)
    chi = jet_scale(
        jet_divide(determinant_jet, jet_multiply(mass, area)), 9
    )
    return eta, chi


def jet_realizability(eta: Jet2, chi: Jet2) -> Jet2:
    bracket = jet_add(
        jet_add(
            jet_subtract(jet_constant(3), jet_scale(eta, 4)),
            jet_scale(chi, 6),
        ),
        jet_scale(jet_multiply(chi, chi), -1),
    )
    return jet_subtract(jet_multiply(eta, bracket), jet_scale(chi, 4))


def eta_gradient(matrix: RMatrix) -> RMatrix:
    """Gradient of log eta in the Frobenius pairing."""
    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    area_gradient = matrix_scale(
        matrix_subtract(matrix_scale(identity_matrix(), mass), matrix),
        Fraction(1, 1) / area,
    )
    return matrix_subtract(
        area_gradient,
        matrix_scale(identity_matrix(), Fraction(2, 1) / mass),
    )


def affine_eta_cotangent(matrix: RMatrix) -> RMatrix:
    """M^(1/2) grad(log eta) M^(1/2), without taking a square root."""
    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    matrix_squared = matrix_multiply(matrix, matrix)
    return matrix_subtract(
        matrix_scale(
            matrix_subtract(matrix_scale(matrix, mass), matrix_squared),
            Fraction(1, 1) / area,
        ),
        matrix_scale(matrix, Fraction(2, 1) / mass),
    )


def check_complete_spectral_coordinates() -> None:
    for eigenvalues in product(range(1, 10), repeat=3):
        matrix = diagonal(eigenvalues)
        mass = trace(matrix)
        eta, chi = shape_coordinates(matrix)
        normalized = tuple(Fraction(value, mass) for value in eigenvalues)

        assert 0 < eta <= 1
        assert 0 < chi <= 1
        for eigenvalue in normalized:
            assert normalized_characteristic(eigenvalue, eta, chi) == 0

        discriminant = Fraction(1)
        for left, right in ((0, 1), (0, 2), (1, 2)):
            discriminant *= (normalized[left] - normalized[right]) ** 2
        boundary = realizability_polynomial(eta, chi)
        assert discriminant == eta * boundary / 27
        assert boundary >= 0
        assert (boundary == 0) == (len(set(eigenvalues)) < 3)

    # chi alone does not determine spectral shape: these have equal chi but
    # lie on the two different axisymmetric branches.
    eta_one_large, chi_one_large = shape_coordinates(diagonal((1, 1, 2)))
    eta_two_large, chi_two_large = shape_coordinates(diagonal((1, 2, 2)))
    assert chi_one_large == chi_two_large == Fraction(9, 10)
    assert eta_one_large == Fraction(15, 16)
    assert eta_two_large == Fraction(24, 25)


def check_rank_two_boundary() -> None:
    for left, right in product(range(1, 20), repeat=2):
        mass = Fraction(left + right)
        eta = Fraction(3 * left * right, mass**2)
        chi = Fraction(0)
        assert 0 < eta <= Fraction(3, 4)
        assert realizability_polynomial(eta, chi) == eta * (3 - 4 * eta) >= 0
        assert (eta == Fraction(3, 4)) == (left == right)


def check_eta_gradient_and_affine_flow() -> None:
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
    matrix_dot = matrix_scale(forcing, Fraction(-1))

    gradient = eta_gradient(matrix)
    cotangent = affine_eta_cotangent(matrix)
    assert matrix_inner(gradient, matrix) == 0
    assert trace(cotangent) == 0
    assert cotangent == matrix_multiply(
        square_root, matrix_multiply(gradient, square_root)
    )

    mass = trace(matrix)
    area = second_elementary_symmetric(matrix)
    mass_dot = trace(matrix_dot)
    area_dot = mass * mass_dot - matrix_inner(matrix, matrix_dot)
    direct_log_eta_dot = area_dot / area - 2 * mass_dot / mass
    affine_rate = matrix_inner(cotangent, driver)
    assert direct_log_eta_dot == matrix_inner(gradient, matrix_dot)
    assert direct_log_eta_dot == -affine_rate


def check_sharp_eta_speed_bound() -> None:
    drivers = ((-2, 1, 4), (3, -1, 0), (5, 5, -2))
    for eigenvalues in product(range(1, 16), repeat=3):
        matrix = diagonal(eigenvalues)
        cotangent = affine_eta_cotangent(matrix)
        entries = tuple(cotangent[i][i] for i in range(3))
        assert sum(entries) == 0
        assert all(Fraction(-1) <= entry <= Fraction(1) for entry in entries)
        assert sum(abs(entry) for entry in entries) <= 2

        for driver_entries in drivers:
            driver = diagonal(driver_entries)
            rate = matrix_inner(cotangent, driver)
            assert abs(rate) <= diagonal_spectral_diameter(driver)

    rate_deficits = []
    nuclear_deficits = []
    for denominator in (10, 100, 1000):
        matrix = diagonal((1, Fraction(1, denominator), Fraction(1, denominator)))
        cotangent = affine_eta_cotangent(matrix)
        unit_diameter_driver = diagonal((1, 0, 0))
        rate = abs(matrix_inner(cotangent, unit_diameter_driver))
        nuclear_norm = sum(abs(cotangent[i][i]) for i in range(3))
        assert rate < 1
        assert nuclear_norm < 2
        rate_deficits.append(1 - rate)
        nuclear_deficits.append(2 - nuclear_norm)
    assert rate_deficits[0] > rate_deficits[1] > rate_deficits[2] > 0
    assert nuclear_deficits[0] > nuclear_deficits[1] > nuclear_deficits[2] > 0


def check_differential_coordinate_conditioning() -> None:
    for eigenvalues in product(range(1, 10), repeat=3):
        if len(set(eigenvalues)) < 3:
            continue
        matrix = diagonal(eigenvalues)
        mass = trace(matrix)
        eta, chi = shape_coordinates(matrix)
        normalized = tuple(Fraction(value, mass) for value in eigenvalues)
        chi_cotangent = affine_shape_cotangent(matrix)
        eta_cotangent = affine_eta_cotangent(matrix)
        chi_entries = tuple(chi_cotangent[i][i] for i in range(3))
        eta_entries = tuple(eta_cotangent[i][i] for i in range(3))

        # The sum is the cotangent of log(27 det(M)/(tr M)^3).
        for index in range(3):
            assert chi_entries[index] + eta_entries[index] == (
                1 - 3 * normalized[index]
            )

        cross = (
            chi_entries[1] * eta_entries[2]
            - chi_entries[2] * eta_entries[1],
            chi_entries[2] * eta_entries[0]
            - chi_entries[0] * eta_entries[2],
            chi_entries[0] * eta_entries[1]
            - chi_entries[1] * eta_entries[0],
        )
        vandermonde = (
            (normalized[0] - normalized[1])
            * (normalized[1] - normalized[2])
            * (normalized[2] - normalized[0])
        )
        assert cross == (vandermonde / (eta / 3),) * 3

        chi_norm_squared = sum(entry**2 for entry in chi_entries)
        eta_norm_squared = sum(entry**2 for entry in eta_entries)
        cotangent_inner = sum(
            chi_entries[i] * eta_entries[i] for i in range(3)
        )
        expected_chi_norm = (
            2 * (3 * eta - eta**2 - (eta + 1) * chi) / (3 * eta)
        )
        expected_eta_norm = (
            2 * (3 * eta - 4 * eta**2 + 2 * eta * chi - chi)
            / (3 * eta)
        )
        expected_inner = (
            3 * eta - 4 * eta**2 - eta * chi + 2 * chi
        ) / (3 * eta)
        assert chi_norm_squared == expected_chi_norm
        assert eta_norm_squared == expected_eta_norm
        assert cotangent_inner == expected_inner
        assert sum(
            (chi_entries[i] + eta_entries[i]) ** 2 for i in range(3)
        ) == 6 * (1 - eta)

        gram_determinant = (
            chi_norm_squared * eta_norm_squared - cotangent_inner**2
        )
        assert gram_determinant == realizability_polynomial(eta, chi) / eta


def check_simple_spectrum_rate_reconstruction() -> None:
    drivers = ((-2, 1, 4), (3, -1, 0), (5, 5, -2))
    for eigenvalues in product(range(1, 9), repeat=3):
        if len(set(eigenvalues)) < 3:
            continue
        matrix = diagonal(eigenvalues)
        eta, chi = shape_coordinates(matrix)
        chi_entries = tuple(
            affine_shape_cotangent(matrix)[i][i] for i in range(3)
        )
        eta_entries = tuple(
            affine_eta_cotangent(matrix)[i][i] for i in range(3)
        )
        chi_norm_squared = sum(entry**2 for entry in chi_entries)
        eta_norm_squared = sum(entry**2 for entry in eta_entries)
        cotangent_inner = sum(
            chi_entries[i] * eta_entries[i] for i in range(3)
        )
        gram_determinant = realizability_polynomial(eta, chi) / eta
        assert gram_determinant > 0

        for driver_entries in drivers:
            driver = tuple(Fraction(value) for value in driver_entries)
            centered = tuple(value - sum(driver) / 3 for value in driver)
            chi_rate = sum(chi_entries[i] * driver[i] for i in range(3))
            eta_rate = sum(eta_entries[i] * driver[i] for i in range(3))

            chi_coefficient = (
                eta_norm_squared * chi_rate - cotangent_inner * eta_rate
            ) / gram_determinant
            eta_coefficient = (
                chi_norm_squared * eta_rate - cotangent_inner * chi_rate
            ) / gram_determinant
            reconstructed = tuple(
                chi_coefficient * chi_entries[i]
                + eta_coefficient * eta_entries[i]
                for i in range(3)
            )
            assert reconstructed == centered

            pairwise_log_speed = sum(
                (driver[left] - driver[right]) ** 2
                for left, right in ((0, 1), (0, 2), (1, 2))
            )
            invariant_speed = (
                3
                * (
                    eta_norm_squared * chi_rate**2
                    - 2 * cotangent_inner * chi_rate * eta_rate
                    + chi_norm_squared * eta_rate**2
                )
                / gram_determinant
            )
            assert pairwise_log_speed == invariant_speed


def check_second_order_axisymmetric_departure() -> None:
    square_roots = {4: Fraction(2), 9: Fraction(3), 25: Fraction(5)}
    base_spectra = ((4, 4, 9), (9, 9, 4), (4, 4, 25), (25, 25, 4))
    driver_data = (
        (2, -2, 5, 3, -1, 4),
        (1, 1, -3, 2, 5, -4),
        (-2, 4, 0, -1, 3, 2),
    )
    for spectrum in base_spectra:
        roots = tuple(Fraction(value) for value in spectrum)
        square_root = tuple(square_roots[value] for value in spectrum)
        mass = sum(roots)
        repeated_root = roots[0] / mass
        simple_root = roots[2] / mass

        for entries in driver_data:
            driver: RMatrix = (
                (Fraction(entries[0]), Fraction(entries[3]), Fraction(entries[4])),
                (Fraction(entries[3]), Fraction(entries[1]), Fraction(entries[5])),
                (Fraction(entries[4]), Fraction(entries[5]), Fraction(entries[2])),
            )
            matrix_jet = tuple(
                tuple(
                    (
                        roots[i] if i == j else Fraction(0),
                        -square_root[i] * driver[i][j] * square_root[j],
                        Fraction(0),
                    )
                    for j in range(3)
                )
                for i in range(3)
            )
            eta_jet, chi_jet = jet_shape_coordinates(matrix_jet)
            boundary_jet = jet_realizability(eta_jet, chi_jet)
            plane_gap_squared = (
                (driver[0][0] - driver[1][1]) ** 2 + 4 * driver[0][1] ** 2
            )
            expected_second_derivative = (
                54
                * repeated_root**2
                * (repeated_root - simple_root) ** 4
                * plane_gap_squared
                / eta_jet[0]
            )
            assert boundary_jet[0] == 0
            assert boundary_jet[1] == 0
            assert boundary_jet[2] == expected_second_derivative


def check_axisymmetric_boundary_tangency() -> None:
    matrices = (diagonal((2, 2, 5)), diagonal((2, 5, 5)))
    for matrix in matrices:
        eta, chi = shape_coordinates(matrix)
        assert realizability_polynomial(eta, chi) == 0
        eta_cotangent = affine_eta_cotangent(matrix)
        chi_cotangent = affine_shape_cotangent(matrix)

        for entries in product(range(-2, 3), repeat=6):
            driver: RMatrix = (
                (Fraction(entries[0]), Fraction(entries[3]), Fraction(entries[4])),
                (Fraction(entries[3]), Fraction(entries[1]), Fraction(entries[5])),
                (Fraction(entries[4]), Fraction(entries[5]), Fraction(entries[2])),
            )
            eta_rate = matrix_inner(eta_cotangent, driver)
            chi_rate = matrix_inner(chi_cotangent, driver)
            eta_dot = -eta * eta_rate
            chi_dot = -chi * chi_rate

            boundary_eta = 3 - 8 * eta + 6 * chi - chi**2
            boundary_chi = eta * (6 - 2 * chi) - 4
            boundary_dot = boundary_eta * eta_dot + boundary_chi * chi_dot
            assert boundary_dot == 0


def check_consistency_with_planarity_coordinate() -> None:
    for eigenvalues in ((1, 2, 3), (2, 2, 5), (1, 7, 11)):
        matrix = diagonal(eigenvalues)
        _, chi = shape_coordinates(matrix)
        assert chi == shape_factor(matrix)

        square_root = diagonal(tuple(Fraction(value) for value in eigenvalues))
        squared_matrix = matrix_multiply(square_root, square_root)
        assert affine_shape_cotangent(squared_matrix) == matrix_multiply(
            square_root,
            matrix_multiply(shape_gradient(squared_matrix), square_root),
        )


def main() -> None:
    check_complete_spectral_coordinates()
    print("Two coordinates reconstruct the normalized Gram spectrum: PASS")
    check_rank_two_boundary()
    print("Rank-two closure of the realizability region: PASS")
    check_eta_gradient_and_affine_flow()
    print("Exact complementary-coordinate affine evolution: PASS")
    check_sharp_eta_speed_bound()
    print("Sharp universal complementary shape-rate bound: PASS")
    check_differential_coordinate_conditioning()
    print("Exact invariant-coordinate conditioning determinant: PASS")
    check_simple_spectrum_rate_reconstruction()
    print("Simple-spectrum log-eigenvalue rate reconstruction: PASS")
    check_axisymmetric_boundary_tangency()
    print("Axisymmetric realizability-boundary tangency: PASS")
    check_second_order_axisymmetric_departure()
    print("Second-order axisymmetric departure law: PASS")
    check_consistency_with_planarity_coordinate()
    print("Consistency with the existing planarity coordinate: PASS")
    print("All exact Gram spectral-coordinate checks passed.")


if __name__ == "__main__":
    main()
