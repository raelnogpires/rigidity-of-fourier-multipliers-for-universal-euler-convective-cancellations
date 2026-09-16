#!/usr/bin/env python3
"""Exact checks for the spectral--orbital completion of Gram-shape flow.

On the simple-spectrum stratum, the two scalar Gram-shape rates reconstruct
the diagonal (spectral) part of the normalized driver.  This script checks the
orthogonal complementary orbital part, its eigenframe equation, its
commutator characterization, and an exact Fourier witness in which nonlinear
production is purely orbital.  It also identifies the independent orbital
component of shell-dependent viscous flow.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Sequence

from explore_full_multiplier import ONE
from verify_adaptive_miller_metric import (
    VectorField,
    add_real_mode,
    add_rmatrices,
    gram_tensor,
    matrix_inner,
    matrix_multiply,
    matrix_scale,
    matrix_subtract,
    strain_field,
)
from verify_gram_shape_coordinates import (
    affine_eta_cotangent,
    eta_gradient,
    realizability_polynomial,
    shape_coordinates,
)
from verify_planarity_shape_dynamics import (
    combined_production,
    shape_gradient,
)
from verify_whitened_gram_shape import affine_shape_cotangent

RMatrix = tuple[tuple[Fraction, Fraction, Fraction], ...]


def identity_matrix() -> RMatrix:
    return tuple(
        tuple(Fraction(i == j) for j in range(3)) for i in range(3)
    )


def diagonal(values: Sequence[int | Fraction]) -> RMatrix:
    return tuple(
        tuple(Fraction(values[i]) if i == j else Fraction(0) for j in range(3))
        for i in range(3)
    )


def transpose(matrix: RMatrix) -> RMatrix:
    return tuple(tuple(matrix[j][i] for j in range(3)) for i in range(3))


def conjugate(orthogonal: RMatrix, matrix: RMatrix) -> RMatrix:
    return matrix_multiply(
        orthogonal, matrix_multiply(matrix, transpose(orthogonal))
    )


def commutator(left: RMatrix, right: RMatrix) -> RMatrix:
    return matrix_subtract(
        matrix_multiply(left, right), matrix_multiply(right, left)
    )


def frobenius_norm_squared(matrix: RMatrix) -> Fraction:
    return matrix_inner(matrix, matrix)


def deviatoric(matrix: RMatrix) -> RMatrix:
    trace = sum(matrix[i][i] for i in range(3))
    return matrix_subtract(matrix, matrix_scale(identity_matrix(), trace / 3))


def spectral_coefficients(
    eta: Fraction, chi: Fraction
) -> tuple[Fraction, Fraction, Fraction]:
    chi_norm_squared = 2 * (3 * eta - eta**2 - (eta + 1) * chi) / (3 * eta)
    eta_norm_squared = (
        2 * (3 * eta - 4 * eta**2 + 2 * eta * chi - chi) / (3 * eta)
    )
    cotangent_inner = (
        3 * eta - 4 * eta**2 - eta * chi + 2 * chi
    ) / (3 * eta)
    return chi_norm_squared, eta_norm_squared, cotangent_inner


def check_simple_spectral_orbit_decomposition() -> None:
    eigenvalues = (1, 4, 9)
    square_root = diagonal((1, 2, 3))
    matrix = diagonal(eigenvalues)
    eta, chi = shape_coordinates(matrix)
    discriminant = realizability_polynomial(eta, chi)
    chi_cotangent = affine_shape_cotangent(matrix)
    eta_cotangent = affine_eta_cotangent(matrix)
    chi_norm_squared, eta_norm_squared, cotangent_inner = spectral_coefficients(
        eta, chi
    )

    for entries in product(range(-1, 2), repeat=6):
        driver: RMatrix = (
            (Fraction(entries[0]), Fraction(entries[3]), Fraction(entries[4])),
            (Fraction(entries[3]), Fraction(entries[1]), Fraction(entries[5])),
            (Fraction(entries[4]), Fraction(entries[5]), Fraction(entries[2])),
        )
        chi_rate = matrix_inner(chi_cotangent, driver)
        eta_rate = matrix_inner(eta_cotangent, driver)
        spectral_speed = (
            eta
            * (
                eta_norm_squared * chi_rate**2
                - 2 * cotangent_inner * chi_rate * eta_rate
                + chi_norm_squared * eta_rate**2
            )
            / discriminant
        )
        centered_diagonal = tuple(
            driver[i][i] - sum(driver[j][j] for j in range(3)) / 3
            for i in range(3)
        )
        assert spectral_speed == sum(value**2 for value in centered_diagonal)

        orbital_speed = 2 * sum(
            driver[i][j] ** 2 for i, j in ((0, 1), (0, 2), (1, 2))
        )
        assert frobenius_norm_squared(deviatoric(driver)) == (
            spectral_speed + orbital_speed
        )

        matrix_dot = matrix_scale(
            matrix_multiply(square_root, matrix_multiply(driver, square_root)),
            -1,
        )
        angular_velocity = tuple(
            tuple(
                Fraction(0)
                if i == j
                else Fraction(square_root[i][i] * square_root[j][j], 1)
                * driver[i][j]
                / Fraction(eigenvalues[i] - eigenvalues[j], 1)
                for j in range(3)
            )
            for i in range(3)
        )
        spectral_matrix_dot = diagonal(
            tuple(-eigenvalues[i] * driver[i][i] for i in range(3))
        )
        assert matrix_dot == tuple(
            tuple(
                spectral_matrix_dot[i][j]
                + commutator(angular_velocity, matrix)[i][j]
                for j in range(3)
            )
            for i in range(3)
        )
        assert orbital_speed == 2 * sum(
            Fraction((eigenvalues[i] - eigenvalues[j]) ** 2, eigenvalues[i] * eigenvalues[j])
            * angular_velocity[i][j] ** 2
            for i, j in ((0, 1), (0, 2), (1, 2))
        )


def check_commutator_characterization() -> None:
    frame: RMatrix = (
        (Fraction(3, 5), Fraction(-4, 5), Fraction(0)),
        (Fraction(4, 5), Fraction(3, 5), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    diagonal_matrix = diagonal((1, 4, 9))
    diagonal_driver: RMatrix = (
        (Fraction(2), Fraction(-1), Fraction(3)),
        (Fraction(-1), Fraction(4), Fraction(5)),
        (Fraction(3), Fraction(5), Fraction(-2)),
    )
    matrix = conjugate(frame, diagonal_matrix)
    driver = conjugate(frame, diagonal_driver)
    bracket = commutator(matrix, driver)
    bracket_diagonal = matrix_multiply(
        transpose(frame), matrix_multiply(bracket, frame)
    )

    recovered_diagonal = tuple(
        tuple(
            Fraction(0)
            if i == j
            else bracket_diagonal[i][j]
            / (diagonal_matrix[i][i] - diagonal_matrix[j][j])
            for j in range(3)
        )
        for i in range(3)
    )
    recovered = conjugate(frame, recovered_diagonal)
    expected_diagonal = tuple(
        tuple(
            Fraction(0) if i == j else diagonal_driver[i][j]
            for j in range(3)
        )
        for i in range(3)
    )
    expected = conjugate(frame, expected_diagonal)
    assert recovered == expected
    assert commutator(matrix, recovered) == bracket
    assert frobenius_norm_squared(recovered) == 2 * sum(
        diagonal_driver[i][j] ** 2 for i, j in ((0, 1), (0, 2), (1, 2))
    )


def pure_orbit_fourier_field(sign: int) -> VectorField:
    field: VectorField = {}
    data = (
        ((1, 0, 0), (0, 0, 1), ONE),
        ((0, 1, 0), (0, 0, -1), ONE),
        ((1, 1, 0), (1, -1, 0), (Fraction(0), Fraction(sign))),
        ((0, 0, 1), (0, 1, 0), ONE),
    )
    for wavevector, polarization, phase in data:
        add_real_mode(field, wavevector, polarization, phase)
    return field


def check_actual_fourier_pure_orbit_witness() -> None:
    viscosity = Fraction(1, 10)
    expected_matrix = (
        (Fraction(5), Fraction(4), Fraction(0)),
        (Fraction(4), Fraction(5), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    expected_dissipation = (
        (Fraction(9), Fraction(8), Fraction(0)),
        (Fraction(8), Fraction(9), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    scalar_rates = []
    angular_velocities = []
    for sign in (1, -1):
        field = pure_orbit_fourier_field(sign)
        strains = strain_field(field)
        matrix = gram_tensor(strains)
        dissipation = gram_tensor(strains, extra_laplacian=True)
        production = combined_production(field)
        forcing = add_rmatrices(production, matrix_scale(dissipation, 2 * viscosity))
        assert matrix == expected_matrix
        assert dissipation == expected_dissipation
        assert production == matrix_scale(
            diagonal((2, -2, 0)), Fraction(sign)
        )

        # In the q_+=(1,1,0)/sqrt(2), q_-=(1,-1,0)/sqrt(2), e_3 frame,
        # M=diag(9,1,1), N=diag(17,1,1), and C is purely q_+--q_- off-block.
        plus_minus_forcing = (forcing[0][0] - forcing[1][1]) / 2
        assert plus_minus_forcing == 2 * sign
        assert matrix_inner(shape_gradient(matrix), production) == 0
        assert matrix_inner(eta_gradient(matrix), production) == 0

        orbital_speed = 2 * plus_minus_forcing**2 / (9 * 1)
        assert orbital_speed == Fraction(8, 9)
        angular_velocity = plus_minus_forcing / (9 - 1)
        assert angular_velocity == Fraction(sign, 4)
        angular_velocities.append(angular_velocity)

        scalar_rates.append(
            (
                matrix_inner(shape_gradient(matrix), forcing),
                matrix_inner(eta_gradient(matrix), forcing),
            )
        )
    assert scalar_rates[0] == scalar_rates[1]
    assert angular_velocities == [Fraction(1, 4), Fraction(-1, 4)]


def pure_viscous_orbit_fourier_field() -> VectorField:
    field: VectorField = {}
    data = (
        ((2, 0, 0), (0, 1, 0), 1),
        ((0, 1, 0), (1, 0, 0), 4),
        ((1, 1, 0), (1, -1, 0), 1),
        ((0, 0, 1), (1, 0, 0), 3),
    )
    for wavevector, polarization, amplitude in data:
        add_real_mode(
            field,
            wavevector,
            polarization,
            (Fraction(amplitude), Fraction(0)),
        )
    return field


def mixed_orbit_fourier_field(
    a: Fraction, b: Fraction, d: Fraction, c: Fraction
) -> VectorField:
    """Four-mode family with explicitly competing nonlinear/viscous orbits."""
    field: VectorField = {}
    data = (
        ((1, 0, 0), (0, 0, 1), (a, Fraction(0))),
        ((0, 1, 0), (0, 0, -1), (b, Fraction(0))),
        ((1, 1, 0), (1, -1, 0), (Fraction(0), d)),
        ((0, 0, 1), (0, 1, 0), (c, Fraction(0))),
    )
    for wavevector, polarization, phase in data:
        add_real_mode(field, wavevector, polarization, phase)
    return field


def _rank_one(vector: Sequence[int]) -> RMatrix:
    return tuple(
        tuple(Fraction(vector[i] * vector[j]) for j in range(3))
        for i in range(3)
    )


def _weighted_moment(
    vectors: Sequence[Sequence[int]],
    weights: Sequence[Fraction],
    *,
    shell_weighted: bool,
) -> RMatrix:
    result = diagonal((0, 0, 0))
    for vector, weight in zip(vectors, weights):
        shell = sum(value * value for value in vector)
        coefficient = weight * (shell if shell_weighted else 1)
        result = add_rmatrices(
            result, matrix_scale(_rank_one(vector), coefficient)
        )
    return result


def _shell_pair_commutator(
    vectors: Sequence[Sequence[int]], weights: Sequence[Fraction]
) -> RMatrix:
    result = diagonal((0, 0, 0))
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            left = vectors[i]
            right = vectors[j]
            left_shell = sum(value * value for value in left)
            right_shell = sum(value * value for value in right)
            inner = sum(left[r] * right[r] for r in range(3))
            coefficient = (
                weights[i]
                * weights[j]
                * (right_shell - left_shell)
                * inner
            )
            wedge = tuple(
                tuple(
                    Fraction(left[a] * right[b] - right[a] * left[b])
                    for b in range(3)
                )
                for a in range(3)
            )
            result = add_rmatrices(
                result, matrix_scale(wedge, coefficient)
            )
    return result


def minimal_viscous_orbit_fourier_field() -> VectorField:
    """Three-pair, full-rank, triad-free viscous-orbit witness."""
    field: VectorField = {}
    data = (
        ((1, 0, 0), (0, 0, 1), (Fraction(1), Fraction(0))),
        ((1, 1, 0), (1, -1, 0), (Fraction(1, 2), Fraction(0))),
        ((0, 0, 1), (1, 0, 0), (Fraction(1), Fraction(0))),
    )
    for wavevector, polarization, phase in data:
        add_real_mode(field, wavevector, polarization, phase)
    return field


def check_shell_pair_torque_and_minimal_witness() -> tuple[Fraction, Fraction]:
    """Check the pairwise shell torque and the optimal three-pair example."""
    cases = (
        (
            ((1, 0, 0), (1, 1, 0), (0, 0, 1)),
            (Fraction(1), Fraction(1), Fraction(1)),
        ),
        (
            ((1, 2, 0), (0, 1, 1), (1, 0, 2), (2, -1, 1)),
            (Fraction(2), Fraction(3, 2), Fraction(5), Fraction(4, 3)),
        ),
    )
    for vectors, weights in cases:
        matrix = _weighted_moment(vectors, weights, shell_weighted=False)
        dissipation = _weighted_moment(
            vectors, weights, shell_weighted=True
        )
        assert commutator(matrix, dissipation) == _shell_pair_commutator(
            vectors, weights
        )

    field = minimal_viscous_orbit_fourier_field()
    strains = strain_field(field)
    matrix = gram_tensor(strains)
    dissipation = gram_tensor(strains, extra_laplacian=True)
    production = combined_production(field)
    assert matrix == (
        (Fraction(2), Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    assert dissipation == (
        (Fraction(3), Fraction(2), Fraction(0)),
        (Fraction(2), Fraction(2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    assert production == diagonal((0, 0, 0))
    assert commutator(matrix, dissipation) == (
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(-1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    assert (
        matrix[0][0] * matrix[1][1] * matrix[2][2]
        - matrix[0][1] ** 2 * matrix[2][2]
    ) == 1

    viscosity = Fraction(1, 10)
    # The planar determinant is 1 and the squared eigenvalue gap is 5.
    orbital_speed = Fraction(8, 5) * viscosity**2
    angular_speed = Fraction(2, 5) * viscosity
    assert orbital_speed == Fraction(2, 125)
    assert angular_speed == Fraction(1, 25)
    return orbital_speed, angular_speed


def check_combined_orbital_viscosity_selector() -> Fraction:
    """Check exact cancellation and the positive-viscosity obstruction."""
    field = mixed_orbit_fourier_field(
        Fraction(2), Fraction(1), Fraction(1), Fraction(1)
    )
    strains = strain_field(field)
    matrix = gram_tensor(strains)
    dissipation = gram_tensor(strains, extra_laplacian=True)
    production = combined_production(field)
    assert matrix == (
        (Fraction(8), Fraction(4), Fraction(0)),
        (Fraction(4), Fraction(5), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    assert dissipation == (
        (Fraction(12), Fraction(8), Fraction(0)),
        (Fraction(8), Fraction(9), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    assert production == diagonal((4, -4, 0))
    nonlinear_bracket = commutator(matrix, production)
    viscous_bracket = commutator(matrix, dissipation)
    assert nonlinear_bracket[0][1] == Fraction(-32)
    assert viscous_bracket[0][1] == Fraction(12)
    planar_determinant = (
        matrix[0][0] * matrix[1][1] - matrix[0][1] ** 2
    )
    planar_gap_squared = (
        (matrix[0][0] - matrix[1][1]) ** 2 + 4 * matrix[0][1] ** 2
    )
    nonlinear_norm_squared = (
        2 * nonlinear_bracket[0][1] ** 2
        / (planar_determinant * planar_gap_squared)
    )
    viscous_norm_squared = (
        2 * viscous_bracket[0][1] ** 2
        / (planar_determinant * planar_gap_squared)
    )
    whitened_inner = (
        2 * nonlinear_bracket[0][1] * viscous_bracket[0][1]
        / (planar_determinant * planar_gap_squared)
    )
    assert nonlinear_norm_squared == Fraction(256, 219)
    assert viscous_norm_squared == Fraction(12, 73)
    assert whitened_inner == Fraction(-32, 73)
    viscosity = Fraction(4, 3)
    selected_viscosity = max(
        Fraction(0), -whitened_inner / (2 * viscous_norm_squared)
    )
    minimum_speed = (
        nonlinear_norm_squared
        - min(whitened_inner, Fraction(0)) ** 2 / viscous_norm_squared
    )
    assert selected_viscosity == viscosity
    assert minimum_speed == 0
    combined = add_rmatrices(
        production, matrix_scale(dissipation, 2 * viscosity)
    )
    assert commutator(matrix, combined) == diagonal((0, 0, 0))

    # Interchanging a and b makes the whitened nonlinear and viscous
    # off-orbit components positively correlated, so nu=0 is the constrained
    # least-rotation choice and no physical viscosity can cancel them.
    field = mixed_orbit_fourier_field(
        Fraction(1), Fraction(2), Fraction(1), Fraction(1)
    )
    strains = strain_field(field)
    matrix = gram_tensor(strains)
    dissipation = gram_tensor(strains, extra_laplacian=True)
    production = combined_production(field)
    nonlinear_bracket = commutator(matrix, production)
    viscous_bracket = commutator(matrix, dissipation)
    assert nonlinear_bracket[0][1] == Fraction(-32)
    assert viscous_bracket[0][1] == Fraction(-12)
    planar_determinant = (
        matrix[0][0] * matrix[1][1] - matrix[0][1] ** 2
    )
    planar_gap_squared = (
        (matrix[0][0] - matrix[1][1]) ** 2 + 4 * matrix[0][1] ** 2
    )
    whitened_inner = (
        2
        * nonlinear_bracket[0][1]
        * viscous_bracket[0][1]
        / (planar_determinant * planar_gap_squared)
    )
    assert whitened_inner == Fraction(32, 73)
    viscous_norm_squared = (
        2 * viscous_bracket[0][1] ** 2
        / (planar_determinant * planar_gap_squared)
    )
    assert max(
        Fraction(0), -whitened_inner / (2 * viscous_norm_squared)
    ) == 0
    return whitened_inner


def check_actual_fourier_pure_viscous_orbit_witness() -> None:
    viscosity = Fraction(1, 10)
    field = pure_viscous_orbit_fourier_field()
    strains = strain_field(field)
    matrix = gram_tensor(strains)
    dissipation = gram_tensor(strains, extra_laplacian=True)
    production = combined_production(field)
    forcing = add_rmatrices(production, matrix_scale(dissipation, 2 * viscosity))
    expected_matrix = (
        (Fraction(20), Fraction(4), Fraction(0)),
        (Fraction(4), Fraction(20), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(9)),
    )
    expected_dissipation = (
        (Fraction(72), Fraction(8), Fraction(0)),
        (Fraction(8), Fraction(24), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(9)),
    )
    assert matrix == expected_matrix
    assert dissipation == expected_dissipation
    assert production == diagonal((0, 0, 0))
    assert commutator(matrix, dissipation) != diagonal((0, 0, 0))

    # In the q_+=(1,1,0)/sqrt(2), q_-=(1,-1,0)/sqrt(2), e_3 frame,
    # M=diag(24,16,9), N has q_+--q_- entry 24, and C=0.
    plus_minus_forcing = (forcing[0][0] - forcing[1][1]) / 2
    assert plus_minus_forcing == 48 * viscosity
    orbital_speed = 2 * plus_minus_forcing**2 / (24 * 16)
    assert orbital_speed == 12 * viscosity**2
    assert orbital_speed == Fraction(3, 25)
    angular_velocity = plus_minus_forcing / (24 - 16)
    assert angular_velocity == 6 * viscosity == Fraction(3, 5)

    # The active shells are 1, 2, and 4.  The general shell-band estimate
    # O_M(2 nu D) <= (8/3) nu^2 (r_+-r_-)^2 holds strictly here.
    shell_band_bound = Fraction(8, 3) * viscosity**2 * (4 - 1) ** 2
    assert orbital_speed < shell_band_bound


def main() -> None:
    check_simple_spectral_orbit_decomposition()
    print("Spectral--orbital affine-speed decomposition: PASS")
    check_commutator_characterization()
    print("Basis-free commutator characterization of orbital speed: PASS")
    check_actual_fourier_pure_orbit_witness()
    print("Actual Fourier pure-orbit nonlinear witness: PASS")
    check_actual_fourier_pure_viscous_orbit_witness()
    print("Actual Fourier viscous orbital witness: PASS")
    obstruction_inner = check_combined_orbital_viscosity_selector()
    print(
        "Combined orbital viscosity selector: PASS "
        f"(exact cancellation at nu=4/3; obstruction inner product "
        f"{obstruction_inner})"
    )
    minimal_speed, minimal_angle = (
        check_shell_pair_torque_and_minimal_witness()
    )
    print(
        "Shell-pair torque/minimal viscous orbit: PASS "
        f"(nu=1/10 speed {minimal_speed}; angular rate {minimal_angle})"
    )
    print("All exact Gram spectral--orbital checks passed.")


if __name__ == "__main__":
    main()
