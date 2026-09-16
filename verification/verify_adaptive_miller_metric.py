#!/usr/bin/env python3
"""Exact checks for the adaptive anisotropic Miller-metric identity.

The script starts from the projected Fourier Navier--Stokes equation, computes
the instantaneous time derivative of the strain, and checks the moving
anisotropic H^2 energy law using rational Gaussian arithmetic.  It also checks
the work-free ODE for H and the sharp 1/3 transversality constant.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Dict, Iterable, Sequence, Tuple

from explore_full_multiplier import (
    Gaussian,
    GVec,
    IMAGINARY_UNIT,
    ONE,
    ZERO,
    gadd,
    gdot,
    gmul,
    gsub,
)
from verify_laplacian_rigidity import Vec, add, neg, transverse_basis
from verify_tensorial_miller_identity import (
    GMatrix,
    add_vector_mode,
    advective_field,
    curl_field,
    gneg,
    gscale,
    gvadd,
    gvscale,
    strain_matrix,
)

VectorField = Dict[Vec, GVec]
MatrixField = Dict[Vec, GMatrix]
RMatrix = Tuple[Tuple[Fraction, Fraction, Fraction], ...]


def conjugate(value: Gaussian) -> Gaussian:
    return value[0], -value[1]


def add_real_mode(
    field: VectorField,
    k: Vec,
    polarization: Sequence[int],
    phase: Gaussian,
) -> None:
    amplitude = tuple(
        gmul(phase, (Fraction(component), Fraction(0)))
        for component in polarization
    )
    field[k] = amplitude  # type: ignore[assignment]
    field[neg(k)] = tuple(conjugate(value) for value in amplitude)  # type: ignore[assignment]


def zero_vector() -> GVec:
    return ZERO, ZERO, ZERO


def prune_vector(field: VectorField) -> VectorField:
    return {
        k: value
        for k, value in field.items()
        if any(component != ZERO for component in value)
    }


def matrix_dot(left: GMatrix, right: GMatrix) -> Gaussian:
    value = ZERO
    for i in range(3):
        for j in range(3):
            value = gadd(value, gmul(left[i][j], right[i][j]))
    return value


def real(value: Gaussian) -> Fraction:
    assert value[1] == 0
    return value[0]


def strain_field(field: VectorField) -> MatrixField:
    return {k: strain_matrix(k, value) for k, value in field.items()}


def leray(k: Vec, value: Sequence[Gaussian]) -> GVec:
    length_squared = sum(component * component for component in k)
    assert length_squared > 0
    normal = gdot(value, k)
    return tuple(
        gsub(value[i], gscale(normal, Fraction(k[i], length_squared)))
        for i in range(3)
    )  # type: ignore[return-value]


def ns_velocity_derivative(
    u: VectorField, viscosity: Fraction
) -> VectorField:
    """Instantaneous u_t from u_t=-P(u.grad u)+nu Delta u."""
    nonlinear = advective_field(u)
    at_zero = nonlinear.get((0, 0, 0), zero_vector())
    assert at_zero == zero_vector()
    result: VectorField = {}
    for k in (set(u) | set(nonlinear)) - {(0, 0, 0)}:
        projected = leray(k, nonlinear.get(k, zero_vector()))
        length_squared = sum(component * component for component in k)
        viscous = gvscale(u.get(k, zero_vector()), -viscosity * length_squared)
        result[k] = gvadd(gvscale(projected, -1), viscous)
        assert gdot(result[k], k) == ZERO
    return prune_vector(result)


def gram_tensor(strains: MatrixField, extra_laplacian: bool = False) -> RMatrix:
    """M_ab=<partial_a S,partial_b S>, or N_ab with one extra |k|^2."""
    result = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for k, matrix in strains.items():
        opposite = strains.get(neg(k))
        if opposite is None:
            continue
        contraction = real(matrix_dot(matrix, opposite))
        laplacian = sum(component * component for component in k) if extra_laplacian else 1
        for a in range(3):
            for b in range(3):
                result[a][b] += k[a] * k[b] * laplacian * contraction
    return tuple(tuple(row) for row in result)


def directional_tensor(
    strains: MatrixField,
    left_vorticity: VectorField,
    right_vorticity: VectorField,
) -> RMatrix:
    """Integral of partial_ab S_ij times W_i Z_j."""
    result = [[ZERO for _ in range(3)] for _ in range(3)]
    for p, q, r in product(strains, left_vorticity, right_vorticity):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        contraction = ZERO
        for i in range(3):
            for j in range(3):
                contraction = gadd(
                    contraction,
                    gmul(
                        strains[p][i][j],
                        gmul(left_vorticity[q][i], right_vorticity[r][j]),
                    ),
                )
        for a in range(3):
            for b in range(3):
                result[a][b] = gadd(
                    result[a][b], gscale(contraction, -p[a] * p[b])
                )
    return tuple(tuple(real(value) for value in row) for row in result)


def add_rmatrices(*matrices: RMatrix) -> RMatrix:
    return tuple(
        tuple(sum(matrix[i][j] for matrix in matrices) for j in range(3))
        for i in range(3)
    )


def matrix_inner(left: RMatrix, right: RMatrix) -> Fraction:
    return sum(left[i][j] * right[i][j] for i in range(3) for j in range(3))


def matrix_scale(matrix: RMatrix, scalar: Fraction) -> RMatrix:
    return tuple(tuple(scalar * value for value in row) for row in matrix)


def matrix_subtract(left: RMatrix, right: RMatrix) -> RMatrix:
    return tuple(
        tuple(left[i][j] - right[i][j] for j in range(3))
        for i in range(3)
    )


def matrix_multiply(left: RMatrix, right: RMatrix) -> RMatrix:
    return tuple(
        tuple(sum(left[i][ell] * right[ell][j] for ell in range(3)) for j in range(3))
        for i in range(3)
    )


def commutator(left: RMatrix, right: RMatrix) -> RMatrix:
    return matrix_subtract(matrix_multiply(left, right), matrix_multiply(right, left))


def identity_matrix() -> RMatrix:
    return tuple(
        tuple(Fraction(int(i == j)) for j in range(3)) for i in range(3)
    )


def h_contraction(h: RMatrix, tensor: RMatrix) -> Fraction:
    return matrix_inner(h, tensor)


def energy_cross_term(h: RMatrix, left: MatrixField, right: MatrixField) -> Fraction:
    """Integral H_ab partial_a(left):partial_b(right)."""
    result = ZERO
    for k, left_matrix in left.items():
        opposite = right.get(neg(k))
        if opposite is None:
            continue
        weight = sum(h[a][b] * k[a] * k[b] for a in range(3) for b in range(3))
        result = gadd(result, gscale(matrix_dot(left_matrix, opposite), weight))
    return real(result)


def transport_term(h: RMatrix, u: VectorField, strains: MatrixField) -> Fraction:
    """H_ab int (partial_a u_l)(partial_b S_ij)(partial_l S_ij)."""
    result = ZERO
    for p, q, r in product(u, strains, strains):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        matrix_contraction = matrix_dot(strains[q], strains[r])
        derivative_factor = ZERO
        for a in range(3):
            for b in range(3):
                for ell in range(3):
                    coefficient = h[a][b] * p[a] * q[b] * r[ell]
                    derivative_factor = gadd(
                        derivative_factor, gscale(u[p][ell], coefficient)
                    )
        # Three Fourier derivatives contribute i^3=-i.
        contribution = gmul(
            gmul((Fraction(0), Fraction(-1)), derivative_factor),
            matrix_contraction,
        )
        result = gadd(result, contribution)
    return real(result)


def strain_square_term(h: RMatrix, strains: MatrixField) -> Fraction:
    """Integral (L_H S):S^2, evaluated directly in Fourier variables."""
    result = ZERO
    for p, q, r in product(strains, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        weight = sum(h[a][b] * p[a] * p[b] for a in range(3) for b in range(3))
        contraction = ZERO
        for i in range(3):
            for j in range(3):
                for ell in range(3):
                    contraction = gadd(
                        contraction,
                        gmul(strains[p][i][j], gmul(strains[q][i][ell], strains[r][ell][j])),
                    )
        result = gadd(result, gscale(contraction, weight))
    return real(result)


def transport_mixed(
    h: RMatrix,
    velocity: VectorField,
    left_strain: MatrixField,
    right_strain: MatrixField,
) -> Fraction:
    """Polarization of T_H in its velocity and two strain slots."""
    result = ZERO
    for p, q, r in product(velocity, left_strain, right_strain):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        matrix_contraction = matrix_dot(left_strain[q], right_strain[r])
        derivative_factor = ZERO
        for a in range(3):
            for b in range(3):
                for ell in range(3):
                    coefficient = h[a][b] * p[a] * q[b] * r[ell]
                    derivative_factor = gadd(
                        derivative_factor, gscale(velocity[p][ell], coefficient)
                    )
        contribution = gmul(
            gmul((Fraction(0), Fraction(-1)), derivative_factor),
            matrix_contraction,
        )
        result = gadd(result, contribution)
    return real(result)


def strain_square_mixed(
    h: RMatrix,
    left: MatrixField,
    middle: MatrixField,
    right: MatrixField,
) -> Fraction:
    """Polarization of <L_H S,S^2> in its three strain slots."""
    result = ZERO
    for p, q, r in product(left, middle, right):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        weight = sum(h[a][b] * p[a] * p[b] for a in range(3) for b in range(3))
        contraction = ZERO
        for i in range(3):
            for j in range(3):
                for ell in range(3):
                    contraction = gadd(
                        contraction,
                        gmul(left[p][i][j], gmul(middle[q][i][ell], right[r][ell][j])),
                    )
        result = gadd(result, gscale(contraction, weight))
    return real(result)


def symmetric_coefficient_tensor(function) -> RMatrix:
    """Recover P=P^T from a linear functional H -> H:P."""
    result = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for a in range(3):
        for b in range(a, 3):
            basis: RMatrix = tuple(
                tuple(
                    Fraction(
                        int((i == a and j == b) or (a != b and i == b and j == a))
                    )
                    for j in range(3)
                )
                for i in range(3)
            )
            value = function(basis)
            result[a][b] = result[b][a] = value if a == b else value / 2
    return tuple(tuple(row) for row in result)


def production_tensor(u: VectorField, strains: MatrixField) -> RMatrix:
    """P=P^T characterized by H:P=T_H+R_H."""
    return symmetric_coefficient_tensor(
        lambda h: transport_term(h, u, strains) + strain_square_term(h, strains)
    )


def production_tensor_derivative(
    u: VectorField,
    u_dot: VectorField,
    strains: MatrixField,
    strains_dot: MatrixField,
) -> RMatrix:
    """Exact time derivative of the cubic production tensor."""
    return symmetric_coefficient_tensor(
        lambda h: (
            transport_mixed(h, u_dot, strains, strains)
            + transport_mixed(h, u, strains_dot, strains)
            + transport_mixed(h, u, strains, strains_dot)
            + strain_square_mixed(h, strains_dot, strains, strains)
            + strain_square_mixed(h, strains, strains_dot, strains)
            + strain_square_mixed(h, strains, strains, strains_dot)
        )
    )


def solve_three_by_three(
    coefficients: Tuple[Tuple[Fraction, Fraction, Fraction], ...],
    right_hand_side: Tuple[Fraction, Fraction, Fraction],
) -> Tuple[Fraction, Fraction, Fraction]:
    """Exact Gaussian elimination for a nonsingular 3 by 3 system."""
    rows = [list(coefficients[i]) + [right_hand_side[i]] for i in range(3)]
    for column in range(3):
        pivot = next(row for row in range(column, 3) if rows[row][column] != 0)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [entry / scale for entry in rows[column]]
        for row in range(3):
            if row == column:
                continue
            scale = rows[row][column]
            rows[row] = [
                rows[row][j] - scale * rows[column][j] for j in range(4)
            ]
    return tuple(rows[i][3] for i in range(3))  # type: ignore[return-value]


def solve_square_system(
    coefficients: Sequence[Sequence[Fraction]],
    right_hand_side: Sequence[Fraction],
) -> Tuple[Fraction, ...]:
    """Exact Gaussian elimination for a general nonsingular square system."""
    size = len(coefficients)
    rows = [list(coefficients[i]) + [right_hand_side[i]] for i in range(size)]
    for column in range(size):
        pivot = next(
            row for row in range(column, size) if rows[row][column] != 0
        )
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [entry / scale for entry in rows[column]]
        for row in range(size):
            if row == column:
                continue
            scale = rows[row][column]
            rows[row] = [
                rows[row][j] - scale * rows[column][j]
                for j in range(size + 1)
            ]
    return tuple(rows[i][size] for i in range(size))


def determinant_square(
    matrix: Sequence[Sequence[Fraction]],
) -> Fraction:
    """Exact determinant by fraction-preserving Gaussian elimination."""
    size = len(matrix)
    rows = [list(row) for row in matrix]
    determinant = Fraction(1)
    for column in range(size):
        pivot = next(
            (row for row in range(column, size) if rows[row][column] != 0),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            rows[column], rows[pivot] = rows[pivot], rows[column]
            determinant = -determinant
        pivot_value = rows[column][column]
        determinant *= pivot_value
        for row in range(column + 1, size):
            factor = rows[row][column] / pivot_value
            for j in range(column + 1, size):
                rows[row][j] -= factor * rows[column][j]
    return determinant


def matrix_inverse(matrix: RMatrix) -> RMatrix:
    """Exact inverse of a nonsingular 3 by 3 rational matrix."""
    columns = []
    for index in range(3):
        rhs = tuple(Fraction(int(index == j)) for j in range(3))
        columns.append(solve_three_by_three(matrix, rhs))
    return tuple(
        tuple(columns[j][i] for j in range(3)) for i in range(3)
    )  # type: ignore[return-value]


def expanded_strain_square_term(h: RMatrix, strains: MatrixField) -> Fraction:
    """The integrated form 2 H_ab int tr(S partial_a S partial_b S)."""
    result = ZERO
    for p, q, r in product(strains, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        weight = -2 * sum(
            h[a][b] * q[a] * r[b] for a in range(3) for b in range(3)
        )
        contraction = ZERO
        for i in range(3):
            for j in range(3):
                for ell in range(3):
                    contraction = gadd(
                        contraction,
                        gmul(strains[p][i][j], gmul(strains[q][j][ell], strains[r][ell][i])),
                    )
        result = gadd(result, gscale(contraction, weight))
    return real(result)


def advected_strain(u: VectorField, strains: MatrixField) -> MatrixField:
    result: Dict[Vec, list[list[Gaussian]]] = {}
    for p, q in product(u, strains):
        k = add(p, q)
        if k not in result:
            result[k] = [[ZERO for _ in range(3)] for _ in range(3)]
        factor = gmul(IMAGINARY_UNIT, gdot(u[p], q))
        for i in range(3):
            for j in range(3):
                result[k][i][j] = gadd(
                    result[k][i][j], gmul(factor, strains[q][i][j])
                )
    return {
        k: tuple(tuple(row) for row in matrix)  # type: ignore[misc]
        for k, matrix in result.items()
        if any(value != ZERO for row in matrix for value in row)
    }


def make_admissible_h(q_tensor: RMatrix) -> RMatrix:
    trace_q = sum(q_tensor[i][i] for i in range(3))
    assert trace_q == 0
    q_norm_squared = matrix_inner(q_tensor, q_tensor)
    assert q_norm_squared > 0
    candidates: Iterable[RMatrix] = (
        ((Fraction(1), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(-1), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0))),
        ((Fraction(0), Fraction(1), Fraction(0)),
         (Fraction(1), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0))),
    )
    k_matrix = None
    for candidate in candidates:
        projected = matrix_subtract(
            candidate,
            matrix_scale(q_tensor, matrix_inner(candidate, q_tensor) / q_norm_squared),
        )
        if matrix_inner(projected, projected) > 0:
            k_matrix = projected
            break
    assert k_matrix is not None
    assert sum(k_matrix[i][i] for i in range(3)) == 0
    assert matrix_inner(k_matrix, q_tensor) == 0
    row_bound = max(sum(abs(value) for value in row) for row in k_matrix)
    epsilon = Fraction(1, 10) / (1 + row_bound)
    h = add_rmatrices(identity_matrix(), matrix_scale(k_matrix, epsilon))
    # Strict diagonal dominance supplies an exact positive-definiteness check.
    for i in range(3):
        assert h[i][i] > sum(abs(h[i][j]) for j in range(3) if j != i)
    assert matrix_inner(h, q_tensor) == 0
    assert h != identity_matrix()
    return h


def verify_energy_law(
    u: VectorField,
    viscosity: Fraction,
    h: RMatrix,
    h_dot: RMatrix,
) -> Tuple[Fraction, Fraction, Fraction, Fraction, Fraction]:
    u_dot = ns_velocity_derivative(u, viscosity)
    strains = strain_field(u)
    strains_dot = strain_field(u_dot)
    w = curl_field(u)
    m = gram_tensor(strains)
    n = gram_tensor(strains, extra_laplacian=True)
    q_tensor = directional_tensor(strains, w, w)
    transport = transport_term(h, u, strains)
    strain_square = strain_square_term(h, strains)
    assert strain_square == expanded_strain_square_term(h, strains)
    energy_derivative = Fraction(1, 2) * matrix_inner(h_dot, m)
    energy_derivative += energy_cross_term(h, strains_dot, strains)
    left = energy_derivative + viscosity * matrix_inner(h, n)
    right = (
        Fraction(1, 2) * matrix_inner(h_dot, m)
        - transport
        - strain_square
        + Fraction(1, 4) * matrix_inner(h, q_tensor)
    )
    assert left == right

    # Check the integration-by-parts formula for the transport contribution.
    transported = advected_strain(u, strains)
    direct_transport = energy_cross_term(h, strains, transported)
    assert direct_transport == transport
    return left, transport, strain_square, matrix_inner(h, q_tensor), matrix_inner(h_dot, m)


def deterministic_field(phase_shift: int) -> VectorField:
    field: VectorField = {}
    representatives = (
        (1, 0, 0),
        (0, 1, 0),
        (0, 0, 1),
        (1, 1, 0),
        (1, 0, 1),
        (0, 1, 1),
        (1, 1, 1),
    )
    phases = (ONE, IMAGINARY_UNIT, (Fraction(1), Fraction(1)), (Fraction(2), Fraction(-1)))
    for index, k in enumerate(representatives):
        add_real_mode(
            field,
            k,
            transverse_basis(k)[(index + phase_shift) % 2],
            phases[(index + phase_shift) % len(phases)],
        )
    return field


def semidefinite_obstruction_field() -> VectorField:
    """An exact seven-mode field for which span{Q,P} meets the SPD cone."""
    field: VectorField = {}
    data = (
        ((1, 0, 0), (0, 1, 0), (Fraction(1), Fraction(-2))),
        ((0, 1, 0), (2, 0, 2), (Fraction(-2), Fraction(0))),
        ((0, 0, 1), (2, 2, 0), (Fraction(2), Fraction(-1))),
        ((1, 1, 0), (-2, 2, 2), (Fraction(1), Fraction(1))),
        ((1, 0, 1), (1, -2, -1), (Fraction(-2), Fraction(2))),
        ((0, 1, 1), (2, 1, -1), (Fraction(2), Fraction(-2))),
        ((1, 1, 1), (-2, -1, 3), (Fraction(-2), Fraction(2))),
    )
    for wavevector, polarization, phase in data:
        add_real_mode(field, wavevector, polarization, phase)
    return field


def scalar_rigidity_witness_field() -> VectorField:
    """Three-mode field ruling out a universal fixed scalar pure-dissipation metric."""
    field: VectorField = {}
    add_real_mode(field, (-1, -1, -1), (0, -1, 1), ONE)
    add_real_mode(field, (0, 0, 1), (0, 1, 0), ONE)
    add_real_mode(field, (1, 1, 0), (0, 0, -1), IMAGINARY_UNIT)
    return field


def rank_two_production_field(with_strain_production: bool) -> VectorField:
    """Planar three-mode fields with rank-two M and exact active production."""
    field: VectorField = {}
    if with_strain_production:
        data = (
            ((1, 0, 0), (0, 0, 1), ONE),
            ((0, 1, 0), (1, 0, 0), ONE),
            ((1, 1, 0), (0, 0, -1), (Fraction(1), Fraction(1))),
        )
    else:
        data = (
            ((1, 0, 0), (0, 0, 1), ONE),
            ((0, 1, 0), (0, 0, -1), ONE),
            ((1, 1, 0), (1, -1, 0), IMAGINARY_UNIT),
        )
    for wavevector, polarization, phase in data:
        add_real_mode(field, wavevector, polarization, phase)
    return field


def one_sided_production_witness_field() -> VectorField:
    """Full-rank field separating trace and spectral production rates."""
    field: VectorField = {}
    data = (
        ((1, 0, 0), (0, -1, 0), (Fraction(1), Fraction(0))),
        ((0, 1, 0), (-1, 0, -1), (Fraction(-1), Fraction(-1))),
        ((0, 0, 1), (1, 1, 0), (Fraction(1), Fraction(0))),
        ((1, 1, 0), (1, -1, -1), (Fraction(-1), Fraction(0))),
        ((1, 0, 1), (1, 1, -1), (Fraction(-1), Fraction(1))),
        ((0, 1, 1), (1, 0, 0), (Fraction(1), Fraction(1))),
        ((1, 1, 1), (1, 0, -1), (Fraction(-1), Fraction(-1))),
    )
    for wavevector, polarization, phase in data:
        assert sum(
            wavevector[i] * polarization[i] for i in range(3)
        ) == 0
        add_real_mode(field, wavevector, polarization, phase)
    return field


def verify_adaptive_case(u: VectorField, viscosity: Fraction) -> Tuple[Fraction, Fraction]:
    u_dot = ns_velocity_derivative(u, viscosity)
    strains = strain_field(u)
    strains_dot = strain_field(u_dot)
    w = curl_field(u)
    w_dot = curl_field(u_dot)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, w, w)
    q_dot = add_rmatrices(
        directional_tensor(strains_dot, w, w),
        directional_tensor(strains, w_dot, w),
        directional_tensor(strains, w, w_dot),
    )
    assert sum(q_tensor[i][i] for i in range(3)) == 0
    assert sum(q_dot[i][i] for i in range(3)) == 0
    h = make_admissible_h(q_tensor)

    m_norm_squared = matrix_inner(m, m)
    assert m_norm_squared > 0
    v = matrix_subtract(
        q_tensor,
        matrix_scale(m, matrix_inner(q_tensor, m) / m_norm_squared),
    )
    v_norm_squared = matrix_inner(v, v)
    q_norm_squared = matrix_inner(q_tensor, q_tensor)
    assert 3 * v_norm_squared >= q_norm_squared
    h_dot = matrix_scale(v, -matrix_inner(h, q_dot) / v_norm_squared)
    assert matrix_inner(h_dot, m) == 0
    assert matrix_inner(h_dot, q_tensor) + matrix_inner(h, q_dot) == 0
    assert matrix_inner(h, q_tensor) == 0
    verify_energy_law(u, viscosity, h, h_dot)

    # The reduced adaptive balance has neither metric work nor Q coupling.
    reduced = verify_energy_law(u, viscosity, h, h_dot)
    left, transport, strain_square, hq, hdotm = reduced
    assert hq == 0 and hdotm == 0
    assert left == -transport - strain_square

    # Quantitative speed bound following from transversality and Cauchy--Schwarz.
    assert (
        matrix_inner(h_dot, h_dot) * q_norm_squared
        <= 3 * matrix_inner(h, h) * matrix_inner(q_dot, q_dot)
    )
    return v_norm_squared / q_norm_squared, matrix_inner(h_dot, h_dot)


def verify_commutator_rescaling(u: VectorField, viscosity: Fraction) -> Fraction:
    """Check the nonsingular explicit metric H=c(I+eps[Q,A])."""
    u_dot = ns_velocity_derivative(u, viscosity)
    strains = strain_field(u)
    strains_dot = strain_field(u_dot)
    w = curl_field(u)
    w_dot = curl_field(u_dot)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, w, w)
    q_dot = add_rmatrices(
        directional_tensor(strains_dot, w, w),
        directional_tensor(strains, w_dot, w),
        directional_tensor(strains, w, w_dot),
    )
    skew: RMatrix = (
        (Fraction(0), Fraction(1), Fraction(-1)),
        (Fraction(-1), Fraction(0), Fraction(2)),
        (Fraction(1), Fraction(-2), Fraction(0)),
    )
    k_matrix = commutator(q_tensor, skew)
    k_dot = commutator(q_dot, skew)
    assert k_matrix != ((Fraction(0),) * 3,) * 3
    assert all(k_matrix[i][j] == k_matrix[j][i] for i in range(3) for j in range(3))
    assert sum(k_matrix[i][i] for i in range(3)) == 0
    assert matrix_inner(k_matrix, q_tensor) == 0
    row_bound = max(sum(abs(value) for value in row) for row in k_matrix)
    epsilon = Fraction(1, 10) / (1 + row_bound)
    h_tilde = add_rmatrices(identity_matrix(), matrix_scale(k_matrix, epsilon))
    h_tilde_dot = matrix_scale(k_dot, epsilon)
    for i in range(3):
        assert h_tilde[i][i] > sum(abs(h_tilde[i][j]) for j in range(3) if j != i)
    assert matrix_inner(h_tilde, q_tensor) == 0
    # At c=1, choose c_dot so that H_dot:M vanishes.
    denominator = matrix_inner(h_tilde, m)
    assert denominator > 0
    c_dot = -matrix_inner(h_tilde_dot, m) / denominator
    h_dot = add_rmatrices(matrix_scale(h_tilde, c_dot), h_tilde_dot)
    assert matrix_inner(h_dot, m) == 0
    assert matrix_inner(h_dot, q_tensor) + matrix_inner(h_tilde, q_dot) == 0
    left, transport, strain_square, hq, hdotm = verify_energy_law(
        u, viscosity, h_tilde, h_dot
    )
    assert hq == 0 and hdotm == 0
    assert left == -transport - strain_square
    return c_dot


def verify_fully_cancelling_connection(
    u: VectorField, viscosity: Fraction
) -> Tuple[RMatrix, RMatrix, Fraction]:
    """Check the three-constraint connection eliminating all cubic production."""
    u_dot = ns_velocity_derivative(u, viscosity)
    strains = strain_field(u)
    strains_dot = strain_field(u_dot)
    w = curl_field(u)
    w_dot = curl_field(u_dot)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, w, w)
    q_dot = add_rmatrices(
        directional_tensor(strains_dot, w, w),
        directional_tensor(strains, w_dot, w),
        directional_tensor(strains, w, w_dot),
    )
    p_tensor = production_tensor(u, strains)
    p_dot = production_tensor_derivative(u, u_dot, strains, strains_dot)

    expected_q: RMatrix = (
        (Fraction(-8), Fraction(-2), Fraction(14)),
        (Fraction(-2), Fraction(-8), Fraction(8)),
        (Fraction(14), Fraction(8), Fraction(16)),
    )
    expected_p: RMatrix = (
        (Fraction(-5), Fraction(-9, 2), Fraction(-17, 2)),
        (Fraction(-9, 2), Fraction(-5), Fraction(-8)),
        (Fraction(-17, 2), Fraction(-8), Fraction(-7)),
    )
    h: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(-10, 11)),
        (Fraction(0), Fraction(1), Fraction(-31, 22)),
        (Fraction(-10, 11), Fraction(-31, 22), Fraction(4)),
    )
    assert q_tensor == expected_q
    assert p_tensor == expected_p
    assert matrix_inner(h, q_tensor) == 0
    assert matrix_inner(h, p_tensor) == 0
    # Sylvester's criterion: the leading principal minors are 1, 1, 575/484.
    determinant_h = (
        h[0][0] * (h[1][1] * h[2][2] - h[1][2] * h[2][1])
        - h[0][1] * (h[1][0] * h[2][2] - h[1][2] * h[2][0])
        + h[0][2] * (h[1][0] * h[2][1] - h[1][1] * h[2][0])
    )
    assert h[0][0] == 1
    assert h[0][0] * h[1][1] - h[0][1] * h[1][0] == 1
    assert determinant_h == Fraction(575, 484)

    generators = (m, q_tensor, p_tensor)
    gram = tuple(
        tuple(matrix_inner(generators[i], generators[j]) for j in range(3))
        for i in range(3)
    )
    right_hand_side = (
        Fraction(0),
        -matrix_inner(h, q_dot),
        -matrix_inner(h, p_dot),
    )
    coefficients = solve_three_by_three(gram, right_hand_side)
    h_dot = add_rmatrices(
        *(matrix_scale(generators[i], coefficients[i]) for i in range(3))
    )
    assert matrix_inner(h_dot, m) == 0
    assert matrix_inner(h_dot, q_tensor) + matrix_inner(h, q_dot) == 0
    assert matrix_inner(h_dot, p_tensor) + matrix_inner(h, p_dot) == 0

    # The exact energy law now contains viscosity and no cubic production.
    left, transport, strain_square, hq, hdotm = verify_energy_law(
        u, viscosity, h, h_dot
    )
    assert transport + strain_square == matrix_inner(h, p_tensor) == 0
    assert hq == 0 and hdotm == 0 and left == 0

    gram_determinant = (
        gram[0][0] * (gram[1][1] * gram[2][2] - gram[1][2] * gram[2][1])
        - gram[0][1] * (gram[1][0] * gram[2][2] - gram[1][2] * gram[2][0])
        + gram[0][2] * (gram[1][0] * gram[2][1] - gram[1][1] * gram[2][0])
    )
    assert gram_determinant > 0
    return p_tensor, h, gram_determinant


def verify_semidefinite_obstruction() -> RMatrix:
    """Exhibit an actual flow state where no fully cancelling SPD H exists."""
    u = semidefinite_obstruction_field()
    strains = strain_field(u)
    w = curl_field(u)
    q_tensor = directional_tensor(strains, w, w)
    p_tensor = production_tensor(u, strains)
    expected_q: RMatrix = (
        (Fraction(176), Fraction(-272), Fraction(-528)),
        (Fraction(-272), Fraction(-64), Fraction(-384)),
        (Fraction(-528), Fraction(-384), Fraction(-112)),
    )
    expected_p: RMatrix = (
        (Fraction(464), Fraction(332), Fraction(908)),
        (Fraction(332), Fraction(288), Fraction(800)),
        (Fraction(908), Fraction(800), Fraction(992)),
    )
    assert q_tensor == expected_q
    assert p_tensor == expected_p
    positive_pencil = add_rmatrices(p_tensor, matrix_scale(q_tensor, Fraction(2)))
    expected_pencil: RMatrix = (
        (Fraction(816), Fraction(-212), Fraction(-148)),
        (Fraction(-212), Fraction(160), Fraction(32)),
        (Fraction(-148), Fraction(32), Fraction(768)),
    )
    assert positive_pencil == expected_pencil
    first_minor = positive_pencil[0][0]
    second_minor = (
        positive_pencil[0][0] * positive_pencil[1][1]
        - positive_pencil[0][1] * positive_pencil[1][0]
    )
    determinant = (
        positive_pencil[0][0]
        * (
            positive_pencil[1][1] * positive_pencil[2][2]
            - positive_pencil[1][2] * positive_pencil[2][1]
        )
        - positive_pencil[0][1]
        * (
            positive_pencil[1][0] * positive_pencil[2][2]
            - positive_pencil[1][2] * positive_pencil[2][0]
        )
        + positive_pencil[0][2]
        * (
            positive_pencil[1][0] * positive_pencil[2][1]
            - positive_pencil[1][1] * positive_pencil[2][0]
        )
    )
    assert (first_minor, second_minor, determinant) == (
        Fraction(816),
        Fraction(85616),
        Fraction(63420928),
    )
    return positive_pencil


def verify_canonical_production_metric() -> RMatrix:
    """Check the explicit minimum-Frobenius fixed-time metric H_* from Q,P."""
    u = deterministic_field(1)
    strains = strain_field(u)
    w_field = curl_field(u)
    q_tensor = directional_tensor(strains, w_field, w_field)
    p_tensor = production_tensor(u, strains)
    trace_p = sum(p_tensor[i][i] for i in range(3))
    p_trace_free = matrix_subtract(
        p_tensor, matrix_scale(identity_matrix(), trace_p / 3)
    )
    w_tensor = matrix_subtract(
        p_trace_free,
        matrix_scale(
            q_tensor,
            matrix_inner(p_trace_free, q_tensor) / matrix_inner(q_tensor, q_tensor),
        ),
    )
    h_star = matrix_subtract(
        identity_matrix(),
        matrix_scale(w_tensor, trace_p / matrix_inner(w_tensor, w_tensor)),
    )
    expected: RMatrix = (
        (Fraction(503, 408), Fraction(-95, 408), Fraction(35, 408)),
        (Fraction(-95, 408), Fraction(91, 136), Fraction(-35, 136)),
        (Fraction(35, 408), Fraction(-35, 136), Fraction(56, 51)),
    )
    assert h_star == expected
    assert matrix_inner(h_star, q_tensor) == 0
    assert matrix_inner(h_star, p_tensor) == 0
    first_minor = h_star[0][0]
    second_minor = h_star[0][0] * h_star[1][1] - h_star[0][1] * h_star[1][0]
    determinant = (
        h_star[0][0] * (h_star[1][1] * h_star[2][2] - h_star[1][2] * h_star[2][1])
        - h_star[0][1] * (h_star[1][0] * h_star[2][2] - h_star[1][2] * h_star[2][0])
        + h_star[0][2] * (h_star[1][0] * h_star[2][1] - h_star[1][1] * h_star[2][0])
    )
    assert first_minor > 0 and second_minor > 0 and determinant > 0
    return h_star


def verify_fixed_scalar_production_obstruction() -> Tuple[RMatrix, RMatrix]:
    """Check the exact field used by Proposition 8.1 of the rigidity note."""
    u = scalar_rigidity_witness_field()
    strains = strain_field(u)
    w_field = curl_field(u)
    q_tensor = directional_tensor(strains, w_field, w_field)
    p_tensor = production_tensor(u, strains)
    expected_q: RMatrix = (
        (Fraction(0), Fraction(0), Fraction(2)),
        (Fraction(0), Fraction(0), Fraction(2)),
        (Fraction(2), Fraction(2), Fraction(0)),
    )
    expected_p: RMatrix = (
        (Fraction(-2), Fraction(-2), Fraction(1, 2)),
        (Fraction(-2), Fraction(-2), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1, 2), Fraction(1)),
    )
    assert q_tensor == expected_q
    assert p_tensor == expected_p
    assert sum(q_tensor[i][i] for i in range(3)) == 0
    assert sum(p_tensor[i][i] for i in range(3)) == -3
    return q_tensor, p_tensor


def verify_two_barrier_connection(
    u: VectorField, viscosity: Fraction
) -> Tuple[Fraction, Fraction]:
    """Check the norm/determinant-preserving pure-dissipation connection."""
    strains = strain_field(u)
    w_field = curl_field(u)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, w_field, w_field)
    p_tensor = production_tensor(u, strains)
    h: RMatrix = (
        (Fraction(3), Fraction(1, 2), Fraction(-1, 3)),
        (Fraction(1, 2), Fraction(2), Fraction(1, 4)),
        (Fraction(-1, 3), Fraction(1, 4), Fraction(4)),
    )
    h_inverse = matrix_inverse(h)
    # Project M orthogonally off span{H,H^{-1}}.
    gram = (
        (matrix_inner(h, h), matrix_inner(h, h_inverse)),
        (matrix_inner(h_inverse, h), matrix_inner(h_inverse, h_inverse)),
    )
    projection_rhs = (
        matrix_inner(m, h),
        matrix_inner(m, h_inverse),
    )
    coefficients = solve_square_system(gram, projection_rhs)
    residual = matrix_subtract(
        m,
        add_rmatrices(
            matrix_scale(h, coefficients[0]),
            matrix_scale(h_inverse, coefficients[1]),
        ),
    )
    residual_norm_squared = matrix_inner(residual, residual)
    assert residual_norm_squared > 0
    production_scalar = (
        2 * matrix_inner(h, p_tensor)
        - Fraction(1, 2) * matrix_inner(h, q_tensor)
    )
    h_dot = matrix_scale(
        residual, production_scalar / residual_norm_squared
    )
    assert matrix_inner(h_dot, m) == production_scalar
    assert matrix_inner(h_dot, h) == 0
    assert matrix_inner(h_dot, h_inverse) == 0
    # The full energy identity now has exact pure dissipation without requiring
    # H:Q=0 or H:P=0 separately.
    left, transport, strain_square, hq, hdotm = verify_energy_law(
        u, viscosity, h, h_dot
    )
    assert hdotm == production_scalar
    assert left == 0
    determinant_h = determinant_square(h)
    norm_squared = matrix_inner(h, h)
    assert determinant_h > 0 and norm_squared > 0
    assert 2 * determinant_h / norm_squared > 0
    return production_scalar, residual_norm_squared


def verify_rank_aware_schatten_connections(
    viscosity: Fraction,
) -> Tuple[Fraction, Fraction, Fraction]:
    """Check singular-M support and the affine Frobenius/operator controllers."""
    h: RMatrix = (
        (Fraction(3), Fraction(1, 2), Fraction(-1, 3)),
        (Fraction(1, 2), Fraction(2), Fraction(1, 4)),
        (Fraction(-1, 3), Fraction(1, 4), Fraction(4)),
    )
    expected_m: RMatrix = (
        (Fraction(5), Fraction(4), Fraction(0)),
        (Fraction(4), Fraction(5), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )

    # First certify ker(M) subset ker(P) intersect ker(Q) on a case where
    # both P and Q are nonzero.  This is the rank-deficient support lemma
    # used by the Moore--Penrose normalization in the note.
    support_field = rank_two_production_field(with_strain_production=True)
    support_strains = strain_field(support_field)
    support_vorticity = curl_field(support_field)
    support_m = gram_tensor(support_strains)
    support_q = directional_tensor(
        support_strains, support_vorticity, support_vorticity
    )
    support_p = production_tensor(support_field, support_strains)
    support_c = matrix_subtract(
        matrix_scale(support_p, Fraction(2)),
        matrix_scale(support_q, Fraction(1, 2)),
    )
    assert support_m == expected_m
    assert support_p != tuple(
        tuple(Fraction(0) for _ in range(3)) for _ in range(3)
    )
    assert support_q != tuple(
        tuple(Fraction(0) for _ in range(3)) for _ in range(3)
    )
    for tensor in (support_m, support_p, support_q, support_c):
        assert tensor[2] == (Fraction(0), Fraction(0), Fraction(0))
        assert tuple(row[2] for row in tensor) == (
            Fraction(0), Fraction(0), Fraction(0)
        )

    # The six-component tensor evolution is Mdot+2 nu N+C=0.
    support_strains_dot = strain_field(
        ns_velocity_derivative(support_field, viscosity)
    )
    support_m_dot = symmetric_coefficient_tensor(
        lambda test_h: 2
        * energy_cross_term(test_h, support_strains_dot, support_strains)
    )
    support_n = gram_tensor(support_strains, extra_laplacian=True)
    assert add_rmatrices(
        support_m_dot,
        matrix_scale(support_n, 2 * viscosity),
        support_c,
    ) == tuple(tuple(Fraction(0) for _ in range(3)) for _ in range(3))

    # A second field has the same singular Gram tensor and a rational
    # Moore--Penrose inverse square root, making the normalized production
    # and both canonical controllers exactly auditable.
    field = rank_two_production_field(with_strain_production=False)
    strains = strain_field(field)
    vorticity = curl_field(field)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, vorticity, vorticity)
    p_tensor = production_tensor(field, strains)
    c_tensor = matrix_subtract(
        matrix_scale(p_tensor, Fraction(2)),
        matrix_scale(q_tensor, Fraction(1, 2)),
    )
    assert m == expected_m
    assert c_tensor == (
        (Fraction(2), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    inverse_square_root: RMatrix = (
        (Fraction(2, 3), Fraction(-1, 3), Fraction(0)),
        (Fraction(-1, 3), Fraction(2, 3), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    range_projection: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    assert matrix_multiply(
        inverse_square_root,
        matrix_multiply(m, inverse_square_root),
    ) == range_projection
    normalized = matrix_multiply(
        inverse_square_root,
        matrix_multiply(c_tensor, inverse_square_root),
    )
    assert normalized == (
        (Fraction(2, 3), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-2, 3), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )

    forcing = matrix_inner(h, c_tensor)
    assert forcing == 2
    hm = matrix_inner(h, m)
    assert hm == 29

    # p=infinity: minimum relative operator-speed controller X=aH.
    scalar_rate = forcing / hm
    scalar_dot = matrix_scale(h, scalar_rate)
    assert matrix_inner(scalar_dot, m) == forcing
    assert abs(scalar_rate) <= Fraction(2, 3)
    left, _, _, _, work = verify_energy_law(
        field, viscosity, h, scalar_dot
    )
    assert left == 0 and work == forcing

    # p=2: unique minimum affine-Riemannian Frobenius-speed controller.
    hmh = matrix_multiply(h, matrix_multiply(m, h))
    denominator = matrix_inner(hmh, m)
    assert denominator == Fraction(1475, 2)
    affine_dot = matrix_scale(hmh, forcing / denominator)
    assert matrix_inner(affine_dot, m) == forcing
    h_inverse = matrix_inverse(h)
    affine_speed_squared = matrix_inner(
        matrix_multiply(
            h_inverse, matrix_multiply(affine_dot, h_inverse)
        ),
        affine_dot,
    )
    assert affine_speed_squared == forcing * forcing / denominator == Fraction(8, 1475)
    assert affine_speed_squared <= matrix_inner(normalized, normalized)
    left, _, _, _, work = verify_energy_law(
        field, viscosity, h, affine_dot
    )
    assert left == 0 and work == forcing
    return scalar_rate, affine_speed_squared, matrix_inner(normalized, normalized)


def verify_one_sided_production_witness() -> Tuple[RMatrix, RMatrix]:
    """Certify an actual state with zero trace danger but negative spectrum."""
    field = one_sided_production_witness_field()
    strains = strain_field(field)
    vorticity = curl_field(field)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, vorticity, vorticity)
    p_tensor = production_tensor(field, strains)
    c_tensor = matrix_subtract(
        matrix_scale(p_tensor, Fraction(2)),
        matrix_scale(q_tensor, Fraction(1, 2)),
    )
    assert m == (
        (Fraction(31), Fraction(18), Fraction(24)),
        (Fraction(18), Fraction(26), Fraction(16)),
        (Fraction(24), Fraction(16), Fraction(30)),
    )
    assert m[0][0] == 31
    assert m[0][0] * m[1][1] - m[0][1] ** 2 == 482
    assert determinant_square(m) == 5372
    assert c_tensor == (
        (Fraction(20), Fraction(54), Fraction(30)),
        (Fraction(54), Fraction(54), Fraction(66)),
        (Fraction(30), Fraction(66), Fraction(30)),
    )
    assert c_tensor[0][0] * c_tensor[1][1] - c_tensor[0][1] ** 2 == -1836
    assert determinant_square(c_tensor) == 23040
    assert sum(c_tensor[i][i] for i in range(3)) == 104
    assert sum(p_tensor[i][i] for i in range(3)) == 52
    assert sum(q_tensor[i][i] for i in range(3)) == 0
    # The nonzero leading principal minors give LDL pivots with signs +,-,-.
    # Congruence by M^{-1/2} preserves this inertia, so Xi has a negative
    # spectral part although [-tr(C)]_+/tr(M) is exactly zero.
    assert Fraction(-1836, 20) == Fraction(-459, 5)
    assert Fraction(23040, -1836) == Fraction(-640, 51)
    return m, c_tensor


def project_off_frame(matrix: RMatrix, frame: Sequence[RMatrix]) -> RMatrix:
    """Frobenius-project a symmetric matrix off an independent frame."""
    gram = tuple(
        tuple(matrix_inner(left, right) for right in frame) for left in frame
    )
    rhs = tuple(matrix_inner(matrix, basis) for basis in frame)
    coefficients = solve_square_system(gram, rhs)
    return matrix_subtract(
        matrix,
        add_rmatrices(
            *(matrix_scale(basis, coefficient) for basis, coefficient in zip(frame, coefficients))
        ),
    )


def verify_two_barrier_obstruction_states() -> Tuple[Fraction, Fraction]:
    """Certify both signs of V_H=0,F_H!=0 on actual Fourier states."""
    expected_matrices: Tuple[RMatrix, RMatrix] = (
        (
            (Fraction(35), Fraction(32), Fraction(14)),
            (Fraction(32), Fraction(35), Fraction(14)),
            (Fraction(14), Fraction(14), Fraction(18)),
        ),
        (
            (Fraction(37), Fraction(32), Fraction(34)),
            (Fraction(32), Fraction(42), Fraction(38)),
            (Fraction(34), Fraction(38), Fraction(47)),
        ),
    )
    expected_productions = (Fraction(-2560), Fraction(1350))
    observed = []
    for phase_shift, (expected_m, expected_f) in enumerate(
        zip(expected_matrices, expected_productions)
    ):
        u = deterministic_field(phase_shift)
        strains = strain_field(u)
        w_field = curl_field(u)
        m = gram_tensor(strains)
        q_tensor = directional_tensor(strains, w_field, w_field)
        p_tensor = production_tensor(u, strains)
        assert m == expected_m
        first_minor = m[0][0]
        second_minor = m[0][0] * m[1][1] - m[0][1] * m[1][0]
        assert first_minor > 0 and second_minor > 0 and determinant_square(m) > 0
        h_inverse = matrix_inverse(m)
        residual = project_off_frame(m, (m, h_inverse))
        assert matrix_inner(residual, residual) == 0
        production = (
            2 * matrix_inner(m, p_tensor)
            - Fraction(1, 2) * matrix_inner(m, q_tensor)
        )
        assert production == expected_f != 0
        if phase_shift == 0:
            assert matrix_inner(m, p_tensor) == -1226
            assert matrix_inner(m, q_tensor) == 216
            # Moving-center obstruction on the trace-free sphere.  Writing
            # t-t^{-1}=88/3, D=-(M-(88/3)I) gives
            # G_D=(t-t^{-1})I-D=M, while F_{tI}=-34t.
            assert sum(m[i][i] for i in range(3)) == 88
            assert sum(p_tensor[i][i] for i in range(3)) == -17
            assert sum(q_tensor[i][i] for i in range(3)) == 0
            trace_free = matrix_subtract(
                m, matrix_scale(identity_matrix(), Fraction(88, 3))
            )
            center = matrix_scale(trace_free, Fraction(-1))
            gradient = matrix_subtract(
                matrix_scale(identity_matrix(), Fraction(88, 3)), center
            )
            assert gradient == m
            assert sum(center[i][i] for i in range(3)) == 0
        observed.append(production)

    # At H=tI,M=I, charts 0 and 1 are collinear with M.  The only valid
    # anisotropic chart has the exact level jump Phi_2-Phi_1=3t-1/2.
    t = Fraction(2)
    identity = identity_matrix()
    j_matrix: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    h = matrix_scale(identity, t)
    phi_1_quadratic = Fraction(1, 2) * matrix_inner(
        matrix_subtract(h, identity), matrix_subtract(h, identity)
    )
    phi_2_quadratic = Fraction(1, 2) * matrix_inner(
        matrix_subtract(h, j_matrix), matrix_subtract(h, j_matrix)
    )
    assert phi_2_quadratic - phi_1_quadratic == 3 * t - Fraction(1, 2)
    return observed[0], observed[1]


def verify_two_barrier_margin_steering() -> Tuple[Fraction, Fraction]:
    """Check the exact gauge formula prescribing d/dt |V_H|^2."""
    h: RMatrix = (
        (Fraction(3), Fraction(1, 2), Fraction(-1, 3)),
        (Fraction(1, 2), Fraction(2), Fraction(1, 4)),
        (Fraction(-1, 3), Fraction(1, 4), Fraction(4)),
    )
    h_inverse = matrix_inverse(h)
    m = gram_tensor(strain_field(deterministic_field(0)))
    gram = (
        (matrix_inner(h, h), matrix_inner(h, h_inverse)),
        (matrix_inner(h_inverse, h), matrix_inner(h_inverse, h_inverse)),
    )
    coefficients = solve_square_system(
        gram, (matrix_inner(m, h), matrix_inner(m, h_inverse))
    )
    alpha, beta = coefficients
    v = project_off_frame(m, (h, h_inverse))
    g = matrix_inner(v, v)
    assert beta != 0 and g > 0
    c_matrix = matrix_multiply(h_inverse, matrix_multiply(v, h_inverse))
    w = project_off_frame(c_matrix, (h, h_inverse, v))
    w_norm_squared = matrix_inner(w, w)
    assert w_norm_squared > 0
    m_dot: RMatrix = (
        (Fraction(1), Fraction(-2), Fraction(1, 3)),
        (Fraction(-2), Fraction(3), Fraction(2, 5)),
        (Fraction(1, 3), Fraction(2, 5), Fraction(-1)),
    )
    forcing = Fraction(-7, 3)
    target_rate = Fraction(5, 7)
    c_v = matrix_inner(c_matrix, v)
    base_rate = (
        2 * matrix_inner(v, m_dot)
        - 2 * forcing * (alpha * g - beta * c_v) / g
    )
    z = matrix_scale(
        w, (target_rate - base_rate) / (2 * beta * w_norm_squared)
    )
    assert matrix_inner(z, h) == 0
    assert matrix_inner(z, h_inverse) == 0
    assert matrix_inner(z, v) == 0
    h_dot = add_rmatrices(matrix_scale(v, forcing / g), z)
    assert matrix_inner(h_dot, m) == forcing
    direct_rate = (
        2 * matrix_inner(v, m_dot)
        - 2
        * matrix_inner(
            add_rmatrices(
                matrix_scale(v, alpha), matrix_scale(c_matrix, -beta)
            ),
            h_dot,
        )
    )
    assert direct_rate == target_rate

    # Exact first-order failure of the gauge leverage when beta=0.
    diagonal_h: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(3)),
    )
    e12: RMatrix = (
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    s = Fraction(1, 2)
    s_dot = Fraction(-1, 3)
    diagonal_m = add_rmatrices(diagonal_h, matrix_scale(e12, s))
    diagonal_inverse = matrix_inverse(diagonal_h)
    diagonal_v = project_off_frame(diagonal_m, (diagonal_h, diagonal_inverse))
    assert diagonal_v == matrix_scale(e12, s)
    unavoidable_rate = 2 * matrix_inner(
        diagonal_v, matrix_scale(e12, s_dot)
    )
    assert unavoidable_rate == 4 * s * s_dot < 0
    return target_rate, unavoidable_rate


def verify_coercive_barrier_atlas(
    u: VectorField, viscosity: Fraction
) -> Tuple[int, Fraction, Fraction]:
    """Check the three translated log-det barrier charts exactly."""
    h: RMatrix = (
        (Fraction(3), Fraction(1, 2), Fraction(-1, 3)),
        (Fraction(1, 2), Fraction(2), Fraction(1, 4)),
        (Fraction(-1, 3), Fraction(1, 4), Fraction(4)),
    )
    h_inverse = matrix_inverse(h)
    zero: RMatrix = tuple(tuple(Fraction(0) for _ in range(3)) for _ in range(3))
    identity = identity_matrix()
    j_matrix: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    centers = (zero, identity, j_matrix)
    gradients = tuple(
        matrix_subtract(matrix_subtract(h, center), h_inverse)
        for center in centers
    )
    strains = strain_field(u)
    w_field = curl_field(u)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, w_field, w_field)
    p_tensor = production_tensor(u, strains)
    residuals = []
    for gradient in gradients:
        gradient_norm = matrix_inner(gradient, gradient)
        assert gradient_norm > 0
        residuals.append(project_off_frame(m, (gradient,)))
    valid = [
        index
        for index, residual in enumerate(residuals)
        if matrix_inner(residual, residual) > 0
    ]
    assert valid
    chart = max(valid, key=lambda index: matrix_inner(residuals[index], residuals[index]))
    residual = residuals[chart]
    residual_norm = matrix_inner(residual, residual)
    forcing = (
        2 * matrix_inner(h, p_tensor)
        - Fraction(1, 2) * matrix_inner(h, q_tensor)
    )
    h_dot = matrix_scale(residual, forcing / residual_norm)
    assert matrix_inner(h_dot, m) == forcing
    assert matrix_inner(h_dot, gradients[chart]) == 0
    left, _, _, _, _ = verify_energy_law(u, viscosity, h, h_dot)
    assert left == 0

    # Chart 0 can fail while chart 1 is exact and transverse.
    edge_h: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(3)),
    )
    edge_inverse = matrix_inverse(edge_h)
    edge_m = matrix_subtract(edge_h, edge_inverse)
    edge_g1 = matrix_subtract(edge_m, identity)
    assert matrix_inner(project_off_frame(edge_m, (edge_m,)), project_off_frame(edge_m, (edge_m,))) == 0
    edge_v1 = project_off_frame(edge_m, (edge_g1,))
    assert matrix_inner(edge_v1, edge_v1) == Fraction(386, 145)

    # At a scalar H,M the first two charts fail, but the anisotropic chart works.
    scalar_h = matrix_scale(identity, Fraction(2))
    scalar_inverse = matrix_scale(identity, Fraction(1, 2))
    scalar_g0 = matrix_subtract(scalar_h, scalar_inverse)
    scalar_g1 = matrix_subtract(scalar_g0, identity)
    scalar_g2 = matrix_subtract(scalar_g0, j_matrix)
    assert matrix_inner(project_off_frame(identity, (scalar_g0,)), project_off_frame(identity, (scalar_g0,))) == 0
    assert matrix_inner(project_off_frame(identity, (scalar_g1,)), project_off_frame(identity, (scalar_g1,))) == 0
    scalar_v2 = project_off_frame(identity, (scalar_g2,))
    scalar_residual = matrix_inner(scalar_v2, scalar_v2)
    assert scalar_residual == Fraction(24, 35)

    # Exact equality case behind the finite-frame gap: m=I+J.
    equality_m = add_rmatrices(identity, j_matrix)
    assert matrix_inner(equality_m, equality_m) == 5
    distance_i = matrix_inner(project_off_frame(identity, (equality_m,)), project_off_frame(identity, (equality_m,)))
    distance_j = matrix_inner(project_off_frame(j_matrix, (equality_m,)), project_off_frame(j_matrix, (equality_m,)))
    assert distance_i == distance_j == Fraction(6, 5)
    return chart, residual_norm, scalar_residual


def verify_isospectral_scalar_connection(
    u: VectorField, viscosity: Fraction
) -> Tuple[Fraction, Fraction]:
    """Check the flexible isospectral scalar-production gauge."""
    strains = strain_field(u)
    w_field = curl_field(u)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, w_field, w_field)
    p_tensor = production_tensor(u, strains)
    h: RMatrix = (
        (Fraction(3), Fraction(1, 2), Fraction(-1, 3)),
        (Fraction(1, 2), Fraction(2), Fraction(1, 4)),
        (Fraction(-1, 3), Fraction(1, 4), Fraction(4)),
    )
    commutator_hm = matrix_subtract(
        matrix_multiply(h, m), matrix_multiply(m, h)
    )
    commutator_norm_squared = matrix_inner(commutator_hm, commutator_hm)
    assert commutator_norm_squared > 0
    production_scalar = (
        2 * matrix_inner(h, p_tensor)
        - Fraction(1, 2) * matrix_inner(h, q_tensor)
    )
    omega = matrix_scale(
        commutator_hm,
        -production_scalar / commutator_norm_squared,
    )
    h_dot = matrix_subtract(
        matrix_multiply(omega, h), matrix_multiply(h, omega)
    )
    assert matrix_inner(h_dot, m) == production_scalar
    h_squared = matrix_multiply(h, h)
    assert matrix_inner(h_dot, identity_matrix()) == 0
    assert matrix_inner(h_dot, h) == 0
    assert matrix_inner(h_dot, h_squared) == 0
    left, _, _, _, _ = verify_energy_law(u, viscosity, h, h_dot)
    assert left == 0
    return production_scalar, commutator_norm_squared


def verify_six_frame_isospectral_connection(
    u: VectorField, viscosity: Fraction
) -> Fraction:
    """Check the six-frame realization of the tensorwise cancellation."""
    u_dot = ns_velocity_derivative(u, viscosity)
    strains = strain_field(u)
    strains_dot = strain_field(u_dot)
    w = curl_field(u)
    w_dot = curl_field(u_dot)
    m = gram_tensor(strains)
    q_tensor = directional_tensor(strains, w, w)
    q_dot = add_rmatrices(
        directional_tensor(strains_dot, w, w),
        directional_tensor(strains, w_dot, w),
        directional_tensor(strains, w, w_dot),
    )
    p_tensor = production_tensor(u, strains)
    p_dot = production_tensor_derivative(u, u_dot, strains, strains_dot)
    h: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(-10, 11)),
        (Fraction(0), Fraction(1), Fraction(-31, 22)),
        (Fraction(-10, 11), Fraction(-31, 22), Fraction(4)),
    )
    h_squared = matrix_multiply(h, h)
    identity = identity_matrix()
    frame = (m, q_tensor, p_tensor, identity, h, h_squared)
    gram = tuple(
        tuple(matrix_inner(frame[i], frame[j]) for j in range(6))
        for i in range(6)
    )
    gram_determinant = determinant_square(gram)
    assert gram_determinant == Fraction(713075927328, 14641)
    rhs = (
        Fraction(0),
        -matrix_inner(h, q_dot),
        -matrix_inner(h, p_dot),
        Fraction(0),
        Fraction(0),
        Fraction(0),
    )
    coefficients = solve_square_system(gram, rhs)
    h_dot = add_rmatrices(
        *(matrix_scale(frame[i], coefficients[i]) for i in range(6))
    )
    assert matrix_inner(h_dot, m) == 0
    assert matrix_inner(h_dot, q_tensor) + matrix_inner(h, q_dot) == 0
    assert matrix_inner(h_dot, p_tensor) + matrix_inner(h, p_dot) == 0
    assert matrix_inner(h_dot, identity) == 0
    assert matrix_inner(h_dot, h) == 0
    assert matrix_inner(h_dot, h_squared) == 0
    left, transport, strain_square, hq, hdotm = verify_energy_law(
        u, viscosity, h, h_dot
    )
    assert transport + strain_square == matrix_inner(h, p_tensor) == 0
    assert hq == 0 and hdotm == 0 and left == 0
    return gram_determinant


def verify_sharp_transversality() -> None:
    m: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    q: RMatrix = (
        (Fraction(2, 3), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-1, 3), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(-1, 3)),
    )
    v = matrix_subtract(q, matrix_scale(m, matrix_inner(q, m) / matrix_inner(m, m)))
    assert matrix_inner(v, v) * 3 == matrix_inner(q, q)


def main() -> None:
    viscosity = Fraction(2, 3)
    arbitrary_h: RMatrix = (
        (Fraction(3), Fraction(1, 2), Fraction(-1, 3)),
        (Fraction(1, 2), Fraction(2), Fraction(1, 4)),
        (Fraction(-1, 3), Fraction(1, 4), Fraction(4)),
    )
    arbitrary_h_dot: RMatrix = (
        (Fraction(1, 5), Fraction(-1, 7), Fraction(0)),
        (Fraction(-1, 7), Fraction(2, 5), Fraction(1, 6)),
        (Fraction(0), Fraction(1, 6), Fraction(-3, 5)),
    )
    ratios = []
    speeds = []
    rescaling_rates = []
    for phase_shift in range(2):
        field = deterministic_field(phase_shift)
        verify_energy_law(field, viscosity, arbitrary_h, arbitrary_h_dot)
        ratio, speed = verify_adaptive_case(field, viscosity)
        rescaling_rates.append(verify_commutator_rescaling(field, viscosity))
        ratios.append(ratio)
        speeds.append(speed)
    production, fully_cancelling_h, production_gram_determinant = (
        verify_fully_cancelling_connection(deterministic_field(0), viscosity)
    )
    obstruction = verify_semidefinite_obstruction()
    canonical_production_h = verify_canonical_production_metric()
    scalar_witness_q, scalar_witness_p = verify_fixed_scalar_production_obstruction()
    two_barrier_scalar, two_barrier_residual = verify_two_barrier_connection(
        deterministic_field(0), viscosity
    )
    schatten_scalar_rate, schatten_affine_speed, normalized_production_norm = (
        verify_rank_aware_schatten_connections(viscosity)
    )
    one_sided_m, one_sided_c = verify_one_sided_production_witness()
    two_barrier_obstruction_signs = verify_two_barrier_obstruction_states()
    margin_target, margin_unavoidable = verify_two_barrier_margin_steering()
    atlas_chart, atlas_residual, atlas_scalar_edge = verify_coercive_barrier_atlas(
        deterministic_field(0), viscosity
    )
    isospectral_scalar, isospectral_commutator = (
        verify_isospectral_scalar_connection(deterministic_field(0), viscosity)
    )
    six_frame_determinant = verify_six_frame_isospectral_connection(
        deterministic_field(0), viscosity
    )
    verify_sharp_transversality()
    print(
        "Adaptive Miller metric: PASS "
        "(2 projected Navier--Stokes energy laws; 2 minimal-connection checks; "
        "2 commutator-rescaling checks; 1 fully cancelling connection; "
        "1 canonical fixed-time production metric; 1 exact semidefinite obstruction; "
        "1 fixed-scalar no-go witness; 1 two-barrier connection; "
        "2 rank-aware Schatten-optimal connections; "
        "1 one-sided spectral-production witness; "
        "2 exact two-barrier obstruction states; 1 margin-steering gauge; "
        "1 three-chart coercive atlas; "
        "1 isospectral scalar connection; 1 six-frame connection; "
        "sharp transversality witness)"
    )
    print(f"Observed ||Pi_(M-perp) Q||^2/||Q||^2 ratios: {ratios}")
    print(f"Exact adaptive metric speeds ||H_dot||^2: {speeds}")
    print(f"Exact commutator rescaling rates c_dot/c: {rescaling_rates}")
    print(f"Exact cubic-production tensor P: {production}")
    print(f"Exact fully cancelling SPD metric H: {fully_cancelling_h}")
    print(f"Gram determinant det Gram(M,Q,P): {production_gram_determinant}")
    print(f"Exact positive obstruction P+2Q: {obstruction}")
    print(f"Canonical fixed-time production metric H_*: {canonical_production_h}")
    print(f"Fixed-scalar no-go witness (Q,P): {(scalar_witness_q, scalar_witness_p)}")
    print(
        f"Two-barrier production/residual norms: "
        f"{(two_barrier_scalar, two_barrier_residual)}"
    )
    print(
        "Rank-aware scalar-rate/affine-speed^2/normalized-production^2: "
        f"{(schatten_scalar_rate, schatten_affine_speed, normalized_production_norm)}"
    )
    print(
        "One-sided trace/spectral separation tensors (M,C): "
        f"{(one_sided_m, one_sided_c)}"
    )
    print(f"Two-barrier actual-state obstruction signs: {two_barrier_obstruction_signs}")
    print(f"Margin steering target/unavoidable rates: {(margin_target, margin_unavoidable)}")
    print(
        "Coercive barrier atlas chart/residual/scalar-edge: "
        f"{(atlas_chart, atlas_residual, atlas_scalar_edge)}"
    )
    print(
        f"Isospectral scalar production/commutator norms: "
        f"{(isospectral_scalar, isospectral_commutator)}"
    )
    print(f"Six-frame Gram determinant: {six_frame_determinant}")


if __name__ == "__main__":
    main()
