#!/usr/bin/env python3
"""Independent exact check of the adaptive anisotropic strain-energy law.

All Fourier arithmetic is rational Gaussian arithmetic and all products are
formed by fresh convolutions.  For a real divergence-free trigonometric field
on T^3 this checks, at one time slice of Navier--Stokes,

  d/dt (H:M)/2 + nu H:N
      = (Hdot:M)/2 - T_H - R_H + (H:Q)/4,

where M_ab=<d_a S,d_b S>, N_ab=sum_c<d_ac S,d_bc S>,
Q_ab=<d_ab S,omega tensor omega>,
T_H=<L_H S,u dot grad S>, R_H=<L_H S,S^2>, and L_H=-H_ab d_ab.

It also checks the pressure pairing <L_H S,Hess p>=0, the projected strain
equation, trace(Q)=0, and the adaptive ODE constraints
Hdot:M=0 and Hdot:Q+H:Qdot=0.  At the end it independently checks the
three-constraint production-tensor algebra on abstract rational symmetric
matrices, including one SPD-feasible case and one exact SPD obstruction.  It
also checks the two-barrier and isospectral gauges, including a six-frame
system.  The abstract checks do not claim to rebuild the primary verifier's
seven-mode flow witnesses.  This file intentionally does not import any of the project's
Fourier row builders or tensorial-identity verifier.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import product
from typing import Dict, Iterable, Sequence, Tuple

G = Tuple[F, F]
V = Tuple[G, G, G]
K = Tuple[int, int, int]
Field = Dict[K, V]
ScalarField = Dict[K, G]
MatrixField = Dict[K, Tuple[Tuple[G, G, G], Tuple[G, G, G], Tuple[G, G, G]]]
Z: G = (F(0), F(0))
I: G = (F(0), F(1))
ZERO_K: K = (0, 0, 0)


def ga(x: int | F) -> G:
    return F(x), F(0)


def add(a: G, b: G) -> G:
    return a[0] + b[0], a[1] + b[1]


def neg(a: G) -> G:
    return -a[0], -a[1]


def mul(a: G, b: G) -> G:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(a: G, x: int | F) -> G:
    return mul(ga(x), a)


def conj(a: G) -> G:
    return a[0], -a[1]


def kneg(k: K) -> K:
    return tuple(-x for x in k)  # type: ignore[return-value]


def kadd(k: K, l: K) -> K:
    return tuple(k[i] + l[i] for i in range(3))  # type: ignore[return-value]


def vadd(a: V, b: V) -> V:
    return tuple(add(x, y) for x, y in zip(a, b))  # type: ignore[return-value]


def vneg(a: V) -> V:
    return tuple(neg(x) for x in a)  # type: ignore[return-value]


def vscale(a: V, x: int | F | G) -> V:
    f = x if isinstance(x, tuple) else ga(x)
    return tuple(mul(f, y) for y in a)  # type: ignore[return-value]


def vdot(a: Sequence[G], b: Sequence[G | int]) -> G:
    out = Z
    for x, y in zip(a, b):
        yy = y if isinstance(y, tuple) else ga(y)
        out = add(out, mul(x, yy))
    return out


def mode_add(field: Dict[K, object], k: K, value: object) -> None:
    field[k] = value  # callers use explicit typed accumulators below


def add_scalar(field: ScalarField, k: K, value: G) -> None:
    field[k] = add(field.get(k, Z), value)


def add_vector(field: Field, k: K, value: V) -> None:
    field[k] = vadd(field.get(k, (Z, Z, Z)), value)


def add_matrix(
    field: MatrixField,
    k: K,
    value: Tuple[Tuple[G, G, G], Tuple[G, G, G], Tuple[G, G, G]],
) -> None:
    old = field.get(k, ((Z, Z, Z), (Z, Z, Z), (Z, Z, Z)))
    field[k] = tuple(
        tuple(add(old[i][j], value[i][j]) for j in range(3)) for i in range(3)
    )  # type: ignore[assignment]


def derivative(field: Field, a: int) -> Field:
    return {k: vscale(value, (0, F(k[a]))) for k, value in field.items()}


def derivative_scalar(field: ScalarField, a: int) -> ScalarField:
    return {k: mul((0, F(k[a])), value) for k, value in field.items()}


def laplacian(field: Field) -> Field:
    return {k: vscale(value, -sum(x * x for x in k)) for k, value in field.items()}


def scalar_laplacian(field: ScalarField) -> ScalarField:
    return {k: scale(value, -sum(x * x for x in k)) for k, value in field.items()}


def curl(field: Field) -> Field:
    out: Field = {}
    for k, value in field.items():
        out[k] = (
            add(scale(value[2], -k[1]), scale(value[1], k[2])),
            add(scale(value[0], -k[2]), scale(value[2], k[0])),
            add(scale(value[1], -k[0]), scale(value[0], k[1])),
        )
        out[k] = vscale(out[k], I)
    return out


def strain(field: Field) -> MatrixField:
    out: MatrixField = {}
    for k, value in field.items():
        out[k] = tuple(
            tuple(
                mul(I, scale(add(scale(value[j], k[i]), scale(value[i], k[j])), F(1, 2)))
                for j in range(3)
            )
            for i in range(3)
        )  # type: ignore[assignment]
    return out


def rotation(field: Field) -> MatrixField:
    """Skew part of the velocity gradient, with Omega=(grad-grad^T)/2."""
    out: MatrixField = {}
    for k, value in field.items():
        out[k] = tuple(
            tuple(
                mul(I, scale(add(scale(value[j], k[i]), scale(value[i], -k[j])), F(1, 2)))
                for j in range(3)
            )
            for i in range(3)
        )  # type: ignore[assignment]
    return out


def matrix_add(a: MatrixField, b: MatrixField) -> MatrixField:
    out: MatrixField = {}
    for k in set(a) | set(b):
        aa = a.get(k, ((Z, Z, Z), (Z, Z, Z), (Z, Z, Z)))
        bb = b.get(k, ((Z, Z, Z), (Z, Z, Z), (Z, Z, Z)))
        out[k] = tuple(tuple(add(aa[i][j], bb[i][j]) for j in range(3)) for i in range(3))  # type: ignore[assignment]
    return out


def matrix_scale(a: MatrixField, x: int | F) -> MatrixField:
    return {k: tuple(tuple(scale(a[k][i][j], x) for j in range(3)) for i in range(3)) for k in a}  # type: ignore[return-value]


def matrix_derivative(a: MatrixField, axis: int) -> MatrixField:
    return {k: tuple(tuple(mul((0, F(k[axis])), a[k][i][j]) for j in range(3)) for i in range(3)) for k in a}  # type: ignore[return-value]


def matrix_laplacian(a: MatrixField) -> MatrixField:
    return {k: tuple(tuple(scale(a[k][i][j], -sum(x * x for x in k)) for j in range(3)) for i in range(3)) for k in a}  # type: ignore[return-value]


def convolve_scalar(a: ScalarField, b: ScalarField) -> ScalarField:
    out: ScalarField = {}
    for k, x in a.items():
        for l, y in b.items():
            add_scalar(out, kadd(k, l), mul(x, y))
    return out


def dot_field(a: Field, b: Field) -> ScalarField:
    out: ScalarField = {}
    for k, x in a.items():
        for l, y in b.items():
            add_scalar(out, kadd(k, l), vdot(x, y))
    return out


def vector_scalar(a: Field, b: ScalarField) -> Field:
    out: Field = {}
    for k, x in a.items():
        for l, y in b.items():
            add_vector(out, kadd(k, l), vscale(x, y))
    return out


def matrix_product(a: MatrixField, b: MatrixField) -> MatrixField:
    out: MatrixField = {}
    for k, x in a.items():
        for l, y in b.items():
            value = tuple(
                tuple(
                    sum_gaussian(
                        mul(x[i][m], y[m][j]) for m in range(3)
                    )
                    for j in range(3)
                )
                for i in range(3)
            )
            add_matrix(out, kadd(k, l), value)  # type: ignore[arg-type]
    return out


def matrix_scalar_pair(a: MatrixField, b: MatrixField) -> G:
    total = Z
    for k, x in a.items():
        y = b.get(kneg(k))
        if y is None:
            continue
        for i in range(3):
            for j in range(3):
                total = add(total, mul(x[i][j], y[i][j]))
    return total


def scalar_pair(a: ScalarField, b: ScalarField) -> G:
    total = Z
    for k, x in a.items():
        y = b.get(kneg(k))
        if y is not None:
            total = add(total, mul(x, y))
    return total


def sum_gaussian(values: Iterable[G]) -> G:
    total = Z
    for value in values:
        total = add(total, value)
    return total


def matrix_apply_constant(a: MatrixField, h: Sequence[Sequence[int]]) -> MatrixField:
    # L_H has Fourier multiplier k^T H k on each matrix component.
    out: MatrixField = {}
    for k, value in a.items():
        hk = sum(h[i][j] * k[i] * k[j] for i in range(3) for j in range(3))
        out[k] = tuple(tuple(scale(value[i][j], hk) for j in range(3)) for i in range(3))  # type: ignore[assignment]
    return out


def matrix_hessian_scalar(p: ScalarField) -> MatrixField:
    return {
        k: tuple(tuple(scale(p.get(k, Z), -k[i] * k[j]) for j in range(3)) for i in range(3))  # type: ignore[return-value]
        for k in p
    }


def matrix_omega_square(w: Field) -> MatrixField:
    # Pointwise matrix product of the skew matrix Omega, equivalently
    # 1/4 (omega tensor omega - |omega|^2 I).
    ww: MatrixField = {}
    for k, x in w.items():
        for l, y in w.items():
            value = tuple(
                tuple(
                    add(
                        scale(mul(x[i], y[j]), F(1, 4)),
                        neg(scale(vdot(x, y), F(1, 4))) if i == j else Z,
                    )
                    for j in range(3)
                )
                for i in range(3)
            )
            add_matrix(ww, kadd(k, l), value)  # type: ignore[arg-type]
    return ww


def advective(field: Field) -> Field:
    out: Field = {}
    for q, x in field.items():
        for r, y in field.items():
            coeff = mul(I, vdot(x, r))
            add_vector(out, kadd(q, r), vscale(y, coeff))
    return out


def divergence(field: Field) -> ScalarField:
    return {k: mul(I, vdot(value, k)) for k, value in field.items()}


def grad(field: ScalarField) -> Field:
    out: Field = {}
    for k, value in field.items():
        out[k] = tuple(mul(I, scale(value, k[a])) for a in range(3))  # type: ignore[return-value]
    return out


def field_sum(*fields: Field) -> Field:
    out: Field = {}
    for field in fields:
        for k, value in field.items():
            add_vector(out, k, value)
    return out


def field_neg(field: Field) -> Field:
    return {k: vneg(value) for k, value in field.items()}


def pair(a: MatrixField, b: MatrixField) -> F:
    value = matrix_scalar_pair(a, b)
    assert value[1] == 0, value
    return value[0]


def hpair(h: Sequence[Sequence[int]], x: Sequence[Sequence[F]]) -> F:
    return sum(h[i][j] * x[i][j] for i in range(3) for j in range(3))


RMatrix = Tuple[Tuple[F, F, F], Tuple[F, F, F], Tuple[F, F, F]]


def rinner(left: RMatrix, right: RMatrix) -> F:
    """Frobenius inner product for abstract rational symmetric matrices."""
    return sum(left[i][j] * right[i][j] for i in range(3) for j in range(3))


def rscale(matrix: RMatrix, scalar: F) -> RMatrix:
    return tuple(
        tuple(scalar * matrix[i][j] for j in range(3)) for i in range(3)
    )  # type: ignore[return-value]


def radd(*matrices: RMatrix) -> RMatrix:
    return tuple(
        tuple(sum(matrix[i][j] for matrix in matrices) for j in range(3))
        for i in range(3)
    )  # type: ignore[return-value]


def rmultiply(left: RMatrix, right: RMatrix) -> RMatrix:
    return tuple(
        tuple(
            sum(left[i][k] * right[k][j] for k in range(3))
            for j in range(3)
        )
        for i in range(3)
    )  # type: ignore[return-value]


def rdet(matrix: RMatrix) -> F:
    return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


def assert_spd(matrix: RMatrix) -> None:
    """Sylvester test for a real symmetric 3 by 3 matrix."""
    first = matrix[0][0]
    second = matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    assert first > 0 and second > 0 and rdet(matrix) > 0


def solve_rational_3x3(
    coefficients: RMatrix, rhs: Tuple[F, F, F]
) -> Tuple[F, F, F]:
    """Exact Gaussian elimination for a nonsingular Gram system."""
    rows = [list(coefficients[i]) + [rhs[i]] for i in range(3)]
    for column in range(3):
        pivot = next(row for row in range(column, 3) if rows[row][column] != 0)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        factor = rows[column][column]
        rows[column] = [entry / factor for entry in rows[column]]
        for row in range(3):
            if row == column:
                continue
            factor = rows[row][column]
            rows[row] = [
                rows[row][j] - factor * rows[column][j] for j in range(4)
            ]
    return tuple(rows[i][3] for i in range(3))  # type: ignore[return-value]


def solve_rational_square(
    coefficients: Sequence[Sequence[F]],
    rhs: Sequence[F],
) -> Tuple[F, ...]:
    """Exact Gaussian elimination for an arbitrary square system."""
    size = len(coefficients)
    rows = [list(coefficients[i]) + [rhs[i]] for i in range(size)]
    for column in range(size):
        pivot = next(
            row for row in range(column, size) if rows[row][column] != 0
        )
        rows[column], rows[pivot] = rows[pivot], rows[column]
        factor = rows[column][column]
        rows[column] = [entry / factor for entry in rows[column]]
        for row in range(size):
            if row == column:
                continue
            factor = rows[row][column]
            rows[row] = [
                rows[row][j] - factor * rows[column][j]
                for j in range(size + 1)
            ]
    return tuple(rows[i][size] for i in range(size))


def rproject_off_frame(matrix: RMatrix, frame: Sequence[RMatrix]) -> RMatrix:
    """Exact Frobenius projection off an independent rational frame."""
    gram = tuple(
        tuple(rinner(left, right) for right in frame) for left in frame
    )
    rhs = tuple(rinner(matrix, basis) for basis in frame)
    coefficients = solve_rational_square(gram, rhs)
    return radd(
        matrix,
        *(
            rscale(basis, -coefficient)
            for basis, coefficient in zip(frame, coefficients)
        ),
    )


def verify_production_connection_algebra() -> None:
    """Independently check the production connection and cone obstruction.

    These are abstract exact Sym(3) tests, deliberately separate from the
    primary verifier's Fourier construction.  The first set has
    H:Q=H:P=0 and uses the Gram connection to impose Hdot:M=0 while
    preserving both constraints.  The second has P+2Q=I, so the span of
    {Q,P} contains a positive-definite matrix and no SPD H can annihilate it.
    """
    m: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(1), F(0)),
        (F(0), F(0), F(1)),
    )
    q: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(-2), F(0)),
        (F(0), F(0), F(1)),
    )
    p: RMatrix = (
        (F(0), F(1), F(0)),
        (F(1), F(0), F(0)),
        (F(0), F(0), F(0)),
    )
    h: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(2), F(0)),
        (F(0), F(0), F(3)),
    )
    assert_spd(h)
    assert rinner(h, q) == 0 and rinner(h, p) == 0
    assert rinner(m, m) != 0 and rinner(q, q) != 0 and rinner(p, p) != 0

    q_dot = p
    p_dot: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(0), F(0)),
        (F(0), F(0), F(-1)),
    )
    generators = (m, q, p)
    gram = tuple(
        tuple(rinner(generators[i], generators[j]) for j in range(3))
        for i in range(3)
    )
    coefficients = solve_rational_3x3(
        gram,
        (F(0), -rinner(h, q_dot), -rinner(h, p_dot)),
    )
    h_dot = radd(
        *(rscale(generators[i], coefficients[i]) for i in range(3))
    )
    assert rinner(h_dot, m) == 0
    assert rinner(h_dot, q) + rinner(h, q_dot) == 0
    assert rinner(h_dot, p) + rinner(h, p_dot) == 0
    # The three constraints make the full cubic right-hand side vanish:
    # (Hdot:M)/2 - H:P + (H:Q)/4 = 0.
    assert (
        rinner(h_dot, m) / 2 - rinner(h, p) + rinner(h, q) / 4 == 0
    )
    # Squared form of the quantitative Gram estimate
    # |Hdot| gamma <= |H| sqrt(Gamma_+) D.
    gamma = F(2)       # lambda_min of diag(3,6,2)
    gamma_plus = F(6)  # lambda_max of diag(3,6,2)
    d_squared = rinner(q_dot, q_dot) + rinner(p_dot, p_dot)
    assert (
        rinner(h_dot, h_dot) * gamma * gamma
        <= rinner(h, h) * gamma_plus * d_squared
    )

    # Exact semidefinite alternative obstruction.  Here P is indefinite, but
    # P+2Q=I is positive definite, so no H>0 can satisfy H:Q=H:P=0.
    q_obstruction: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(-1), F(0)),
        (F(0), F(0), F(0)),
    )
    p_obstruction: RMatrix = (
        (F(-1), F(0), F(0)),
        (F(0), F(3), F(0)),
        (F(0), F(0), F(1)),
    )
    pencil = radd(p_obstruction, rscale(q_obstruction, F(2)))
    assert pencil == m
    assert_spd(pencil)
    assert p_obstruction[0][0] < 0 < p_obstruction[1][1]
    # For every SPD H, H:I=tr(H)>0, contradicting H:(P+2Q)=0.
    assert sum(h[i][i] for i in range(3)) > 0

    # Two spectral barriers: project a nonzero M off span{H,H^{-1}}.
    h_inv: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(1, 2), F(0)),
        (F(0), F(0), F(1, 3)),
    )
    two_barrier_m = m
    gram_two = (
        (rinner(h, h), rinner(h, h_inv)),
        (rinner(h_inv, h), rinner(h_inv, h_inv)),
    )
    rhs_two = (rinner(two_barrier_m, h), rinner(two_barrier_m, h_inv))
    coeff_two = solve_rational_square(gram_two, rhs_two)
    residual_two = radd(
        two_barrier_m,
        rscale(h, -coeff_two[0]),
        rscale(h_inv, -coeff_two[1]),
    )
    residual_two_norm = rinner(residual_two, residual_two)
    assert residual_two_norm > 0
    delta_two = gram_two[0][0] * gram_two[1][1] - gram_two[0][1] * gram_two[1][0]
    gram_three = tuple(
        tuple(
            rinner((h, h_inv, two_barrier_m)[i], (h, h_inv, two_barrier_m)[j])
            for j in range(3)
        )
        for i in range(3)
    )
    assert delta_two > 0
    assert residual_two_norm * delta_two == rdet(gram_three)
    f_two = F(12)
    hdot_two = rscale(residual_two, f_two / residual_two_norm)
    assert rinner(hdot_two, two_barrier_m) == f_two
    assert rinner(hdot_two, h) == 0
    assert rinner(hdot_two, h_inv) == 0
    assert rinner(hdot_two, hdot_two) == f_two * f_two / residual_two_norm
    # The barriers imply constant tr(H^2) and log det(H), hence the exact
    # eigenvalue bounds lambda_max <= ||H||_F and
    # lambda_min >= 2 det(H)/||H||_F^2.
    norm_h_squared = rinner(h, h)
    determinant_h = F(1) * F(2) * F(3)
    assert 2 * determinant_h / norm_h_squared > 0

    # Isospectral scalar gauge: M is a rank-one PSD matrix not commuting with
    # H, while P=I and Q=0 make F_H nonzero.
    rotated_m: RMatrix = (
        (F(1), F(1), F(0)),
        (F(1), F(1), F(0)),
        (F(0), F(0), F(0)),
    )
    comm_hm = radd(rmultiply(h, rotated_m), rscale(rmultiply(rotated_m, h), F(-1)))
    comm_norm = rinner(comm_hm, comm_hm)
    assert comm_norm > 0
    f_iso = F(12)
    omega_iso = rscale(comm_hm, -f_iso / comm_norm)
    hdot_iso = radd(rmultiply(omega_iso, h), rscale(rmultiply(h, omega_iso), F(-1)))
    assert rinner(hdot_iso, rotated_m) == f_iso
    assert rinner(hdot_iso, h) == 0
    assert rinner(hdot_iso, h_inv) == 0

    # Six-frame isospectral connection in an abstract simple-spectrum case.
    q_six: RMatrix = (
        (F(0), F(1), F(0)),
        (F(1), F(0), F(0)),
        (F(0), F(0), F(0)),
    )
    p_six: RMatrix = (
        (F(0), F(0), F(1)),
        (F(0), F(0), F(0)),
        (F(1), F(0), F(0)),
    )
    six_m: RMatrix = (
        (F(1), F(1), F(1)),
        (F(1), F(1), F(1)),
        (F(1), F(1), F(1)),
    )
    h_squared = rmultiply(h, h)
    six_frame = (six_m, q_six, p_six, m, h, h_squared)
    six_gram = tuple(
        tuple(rinner(six_frame[i], six_frame[j]) for j in range(6))
        for i in range(6)
    )
    six_rhs = (
        F(0),
        -rinner(h, m),
        -rinner(h, p_six),
        F(0),
        F(0),
        F(0),
    )
    six_coeff = solve_rational_square(six_gram, six_rhs)
    six_dot = radd(
        *(rscale(six_frame[i], six_coeff[i]) for i in range(6))
    )
    assert rinner(six_dot, six_m) == 0
    assert rinner(six_dot, q_six) + rinner(h, m) == 0
    assert rinner(six_dot, p_six) + rinner(h, p_six) == 0
    assert rinner(six_dot, m) == 0
    assert rinner(six_dot, h) == 0
    assert rinner(six_dot, h_squared) == 0


def verify_extended_barrier_algebra() -> None:
    """Independently check margin steering, exhaustion, and the finite atlas."""
    identity: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(1), F(0)),
        (F(0), F(0), F(1)),
    )
    zero: RMatrix = (
        (F(0), F(0), F(0)),
        (F(0), F(0), F(0)),
        (F(0), F(0), F(0)),
    )
    j_matrix: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(-1), F(0)),
        (F(0), F(0), F(0)),
    )
    h: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(2), F(0)),
        (F(0), F(0), F(3)),
    )
    h_inv: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(1, 2), F(0)),
        (F(0), F(0), F(1, 3)),
    )
    v: RMatrix = (
        (F(0), F(1), F(1)),
        (F(1), F(0), F(0)),
        (F(1), F(0), F(0)),
    )
    alpha, beta = F(2), F(3)
    m = radd(rscale(h, alpha), rscale(h_inv, beta), v)
    assert_spd(m)
    recovered = rproject_off_frame(m, (h, h_inv))
    assert recovered == v
    c_matrix = rmultiply(h_inv, rmultiply(v, h_inv))
    w = rproject_off_frame(c_matrix, (h, h_inv, v))
    w_norm = rinner(w, w)
    assert w_norm > 0
    m_dot: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(-1), F(1)),
        (F(0), F(1), F(0)),
    )
    g = rinner(v, v)
    forcing = F(7)
    target_rate = F(-2)
    base_rate = (
        2 * rinner(v, m_dot)
        - 2
        * forcing
        * (alpha * g - beta * rinner(c_matrix, v))
        / g
    )
    z = rscale(w, (target_rate - base_rate) / (2 * beta * w_norm))
    h_dot = radd(rscale(v, forcing / g), z)
    assert rinner(z, h) == rinner(z, h_inv) == rinner(z, v) == 0
    assert rinner(h_dot, m) == forcing
    l_matrix = radd(rscale(v, alpha), rscale(c_matrix, -beta))
    assert 2 * rinner(v, m_dot) - 2 * rinner(l_matrix, h_dot) == target_rate

    # A compact norm/determinant level has an exact height critical point.
    critical_h: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(1), F(0)),
        (F(0), F(0), F(2)),
    )
    critical_inv: RMatrix = (
        (F(1), F(0), F(0)),
        (F(0), F(1), F(0)),
        (F(0), F(0), F(1, 2)),
    )
    assert rproject_off_frame(identity, (critical_h, critical_inv)) == zero

    # Three translated log-det gradients: the exact atlas edge cases.
    g0 = radd(h, rscale(h_inv, F(-1)))
    edge_m = g0
    g1 = radd(g0, rscale(identity, F(-1)))
    edge_v1 = rproject_off_frame(edge_m, (g1,))
    assert rinner(rproject_off_frame(edge_m, (g0,)), rproject_off_frame(edge_m, (g0,))) == 0
    assert rinner(edge_v1, edge_v1) == F(386, 145)

    scalar_h = rscale(identity, F(2))
    scalar_inv = rscale(identity, F(1, 2))
    scalar_g0 = radd(scalar_h, rscale(scalar_inv, F(-1)))
    scalar_g1 = radd(scalar_g0, rscale(identity, F(-1)))
    scalar_g2 = radd(scalar_g0, rscale(j_matrix, F(-1)))
    assert rproject_off_frame(identity, (scalar_g0,)) == zero
    assert rproject_off_frame(identity, (scalar_g1,)) == zero
    scalar_v2 = rproject_off_frame(identity, (scalar_g2,))
    assert rinner(scalar_v2, scalar_v2) == F(24, 35)

    # Equality in the exact finite-frame angle gap.
    equality_m = radd(identity, j_matrix)
    distance_i = rinner(
        rproject_off_frame(identity, (equality_m,)),
        rproject_off_frame(identity, (equality_m,)),
    )
    distance_j = rinner(
        rproject_off_frame(j_matrix, (equality_m,)),
        rproject_off_frame(j_matrix, (equality_m,)),
    )
    assert distance_i == distance_j == F(6, 5)

    # Both exact actual-state Gram tensors are SPD and make V=0 at H=M.
    actual_grams: Tuple[RMatrix, RMatrix] = (
        (
            (F(35), F(32), F(14)),
            (F(32), F(35), F(14)),
            (F(14), F(14), F(18)),
        ),
        (
            (F(37), F(32), F(34)),
            (F(32), F(42), F(38)),
            (F(34), F(38), F(47)),
        ),
    )
    for actual_m in actual_grams:
        assert_spd(actual_m)


def verify_rank_aware_schatten_algebra() -> None:
    """Independent singular-Gram and dual-Schatten controller check."""
    zero: RMatrix = (
        (F(0), F(0), F(0)),
        (F(0), F(0), F(0)),
        (F(0), F(0), F(0)),
    )
    m: RMatrix = (
        (F(4), F(0), F(0)),
        (F(0), F(1), F(0)),
        (F(0), F(0), F(0)),
    )
    production: RMatrix = (
        (F(8), F(0), F(0)),
        (F(0), F(-3), F(0)),
        (F(0), F(0), F(0)),
    )
    inverse_square_root: RMatrix = (
        (F(1, 2), F(0), F(0)),
        (F(0), F(1), F(0)),
        (F(0), F(0), F(0)),
    )
    normalized = rmultiply(
        inverse_square_root, rmultiply(production, inverse_square_root)
    )
    assert normalized == (
        (F(2), F(0), F(0)),
        (F(0), F(-3), F(0)),
        (F(0), F(0), F(0)),
    )
    # The negative spectral edge rho=3 is the least one-sided scalar
    # compensation with C+rho M >= 0.  The trace rate is strictly smaller:
    # tr(C)=5>0 makes sigma=[-tr(C)]_+/tr(M)=0.
    rho = F(3)
    compensated = radd(production, rscale(m, rho))
    assert compensated == (
        (F(20), F(0), F(0)),
        (F(0), F(0), F(0)),
        (F(0), F(0), F(0)),
    )
    assert sum(production[i][i] for i in range(3)) == 5
    assert sum(m[i][i] for i in range(3)) == 5
    sigma = F(0)
    assert sigma < rho
    assert rmultiply(
        inverse_square_root, rmultiply(m, inverse_square_root)
    ) == (
        (F(1), F(0), F(0)),
        (F(0), F(1), F(0)),
        (F(0), F(0), F(0)),
    )

    h: RMatrix = (
        (F(2), F(0), F(0)),
        (F(0), F(3), F(0)),
        (F(0), F(0), F(5)),
    )
    h_inv: RMatrix = (
        (F(1, 2), F(0), F(0)),
        (F(0), F(1, 3), F(0)),
        (F(0), F(0), F(1, 5)),
    )
    forcing = rinner(h, production)
    assert forcing == 7

    # Relative operator-norm minimizer: X=(H:C)/(H:M) H.
    scalar_rate = forcing / rinner(h, m)
    assert scalar_rate == F(7, 11)
    scalar_dot = rscale(h, scalar_rate)
    assert rinner(scalar_dot, m) == forcing
    assert abs(scalar_rate) <= 3  # ||Xi||_op

    # Relative Frobenius minimizer: X=(H:C) H M H/tr(HMHM).
    hmh = rmultiply(h, rmultiply(m, h))
    denominator = rinner(hmh, m)
    assert denominator == 73
    affine_dot = rscale(hmh, forcing / denominator)
    assert rinner(affine_dot, m) == forcing
    relative_speed_squared = rinner(
        rmultiply(h_inv, rmultiply(affine_dot, h_inv)), affine_dot
    )
    assert relative_speed_squared == forcing * forcing / denominator == F(49, 73)
    assert relative_speed_squared <= rinner(normalized, normalized)

    # Exact equality in the p=infinity data bound when Xi is scalar on the
    # active range: C=2M gives (H:C)/(H:M)=||Xi||_op=2.
    scalar_normalized_production = rscale(m, F(2))
    equality_rate = rinner(h, scalar_normalized_production) / rinner(h, m)
    assert equality_rate == 2

    # Every tensor in the construction annihilates ker M=span(e_3).
    for tensor in (m, production, scalar_normalized_production):
        assert tensor[2] == zero[2]
        assert tuple(row[2] for row in tensor) == (F(0), F(0), F(0))


def make_field() -> Field:
    # A non-vacuous real divergence-free field, using the exact triad from
    # the tensorial Miller witness and its conjugate modes.
    modes = {
        (-1, -1, -1): (ga(0), ga(-1), ga(1)),
        (0, 0, 1): (ga(0), ga(1), ga(0)),
        (1, 1, 0): (ga(0), ga(0), Z),
    }
    # The third amplitude is (0,0,-i), not zero; write it explicitly.
    modes[(1, 1, 0)] = (ga(0), ga(0), (F(0), F(-1)))
    field: Field = {}
    for k, value in modes.items():
        field[k] = value
        field[kneg(k)] = tuple(conj(x) for x in value)  # type: ignore[assignment]
    return field


def q_matrix(s: MatrixField, w: Field) -> Tuple[Tuple[F, F, F], ...]:
    out = [[F(0) for _ in range(3)] for _ in range(3)]
    omega_components = [
        {k: value[i] for k, value in w.items()} for i in range(3)
    ]
    for a in range(3):
        for b in range(3):
            dd = matrix_derivative(matrix_derivative(s, a), b)
            total = Z
            for i in range(3):
                for j in range(3):
                    total = add(
                        total,
                        scalar_pair(
                            {k: dd[k][i][j] for k in dd},
                            convolve_scalar(omega_components[i], omega_components[j]),
                        ),
                    )
            assert total[1] == 0
            out[a][b] = total[0]
    return tuple(tuple(row) for row in out)  # type: ignore[return-value]


def m_matrix(s: MatrixField) -> Tuple[Tuple[F, F, F], ...]:
    out = [[F(0) for _ in range(3)] for _ in range(3)]
    ds = [matrix_derivative(s, a) for a in range(3)]
    for a in range(3):
        for b in range(3):
            out[a][b] = pair(ds[a], ds[b])
    return tuple(tuple(row) for row in out)  # type: ignore[return-value]


def n_matrix(s: MatrixField) -> Tuple[Tuple[F, F, F], ...]:
    out = [[F(0) for _ in range(3)] for _ in range(3)]
    d2 = [[matrix_derivative(matrix_derivative(s, a), c) for c in range(3)] for a in range(3)]
    for a in range(3):
        for b in range(3):
            out[a][b] = sum(pair(d2[a][c], d2[b][c]) for c in range(3))
    return tuple(tuple(row) for row in out)  # type: ignore[return-value]


def matrix_from_int(rows: Sequence[Sequence[int]]) -> Tuple[Tuple[int, int, int], ...]:
    return tuple(tuple(int(x) for x in row) for row in rows)  # type: ignore[return-value]


def main() -> None:
    u = make_field()
    assert all(vdot(value, k)[0] == 0 and vdot(value, k)[1] == 0 for k, value in u.items())
    s = strain(u)
    w = curl(u)
    n = advective(u)
    divn = divergence(n)
    p = {k: scale(value, F(1, sum(x * x for x in k))) for k, value in divn.items() if k != ZERO_K}
    nu = 3
    # Rebuild with the viscosity factor explicitly: du=-N-grad p+nu Delta u.
    du = field_sum(field_neg(n), field_neg(grad(p)), {k: vscale(value, nu) for k, value in laplacian(u).items()})
    st = strain(du)
    ss = matrix_product(s, s)
    om2 = matrix_omega_square(w)
    assert om2 == matrix_product(rotation(u), rotation(u)), "Omega^2 sign mismatch"
    hessp = matrix_hessian_scalar(p)
    ls = matrix_apply_constant(s, ((1, 0, 0), (0, 2, 0), (0, 0, 3)))
    dss = matrix_laplacian(s)
    advs = {}
    for k, value in u.items():
        for l, sv in s.items():
            coeff = mul(I, vdot(value, l))
            add_matrix(advs, kadd(k, l), tuple(tuple(mul(coeff, sv[i][j]) for j in range(3)) for i in range(3)))  # type: ignore[arg-type]
    strain_rhs = matrix_add(
        matrix_add(matrix_add(matrix_scale(advs, -1), matrix_scale(ss, -1)), matrix_scale(om2, -1)),
        matrix_add(matrix_scale(hessp, -1), matrix_scale(dss, nu)),
    )
    assert st == strain_rhs, "projected strain equation mismatch"
    h = ((1, 0, 0), (0, 2, 0), (0, 0, 3))
    m = m_matrix(s)
    q = q_matrix(s, w)
    nn = n_matrix(s)
    assert sum(q[i][i] for i in range(3)) == 0, q
    assert pair(ls, hessp) == 0, pair(ls, hessp)
    # An arbitrary trace-free Qdot produces the adaptive Hdot.
    qdot = ((F(1), F(2), F(0)), (F(2), F(-1), F(3)), (F(0), F(3), F(0)))
    mm = sum(m[i][j] * m[i][j] for i in range(3) for j in range(3))
    qm = sum(q[i][j] * m[i][j] for i in range(3) for j in range(3))
    assert mm != 0
    v = tuple(tuple(q[i][j] - qm * m[i][j] / mm for j in range(3)) for i in range(3))
    vv = sum(v[i][j] * v[i][j] for i in range(3) for j in range(3))
    hqdot = sum(h[i][j] * qdot[i][j] for i in range(3) for j in range(3))
    hdot = tuple(tuple(-hqdot * v[i][j] / vv for j in range(3)) for i in range(3))
    assert sum(hdot[i][j] * m[i][j] for i in range(3) for j in range(3)) == 0
    assert sum(hdot[i][j] * q[i][j] for i in range(3) for j in range(3)) + hqdot == 0
    # A gauge-enhanced continuation keeps the anisotropic part trace-free.
    # For K:Q=0 use Kdot=-(K:Qdot)Q/(Q:Q), then choose c'(t)I so that
    # (c'I+Kdot):M=0.  This avoids the minimal ODE's possible trace drift.
    k0 = ((F(1), F(0), F(0)), (F(0), F(-1), F(0)), (F(0), F(0), F(0)))
    assert sum(k0[i][j] * q[i][j] for i in range(3) for j in range(3)) == 0
    qq = sum(q[i][j] * q[i][j] for i in range(3) for j in range(3))
    kqdot = sum(k0[i][j] * qdot[i][j] for i in range(3) for j in range(3))
    kdot = tuple(tuple(-kqdot * q[i][j] / qq for j in range(3)) for i in range(3))
    c_dot = -sum(kdot[i][j] * m[i][j] for i in range(3) for j in range(3)) / sum(m[i][i] for i in range(3))
    assert sum(kdot[i][i] for i in range(3)) == 0
    assert sum(kdot[i][j] * q[i][j] for i in range(3) for j in range(3)) + kqdot == 0
    assert c_dot * sum(m[i][i] for i in range(3)) + sum(kdot[i][j] * m[i][j] for i in range(3) for j in range(3)) == 0
    # Polynomial section K(Q) gives a smooth (though isotropy-collapsing)
    # extension through Q=0 without dividing by |Q|.
    fixed = ((F(1), F(0), F(0)), (F(0), F(-1), F(0)), (F(0), F(0), F(0)))
    kpoly = tuple(
        tuple(qq * fixed[i][j] - sum(fixed[a][b] * q[a][b] for a in range(3) for b in range(3)) * q[i][j] for j in range(3))
        for i in range(3)
    )
    assert sum(kpoly[i][i] for i in range(3)) == 0
    assert sum(kpoly[i][j] * q[i][j] for i in range(3) for j in range(3)) == 0
    # Full energy law.  The direct derivative uses H constant at this slice;
    # the Hdot:M/2 term is then added separately.
    ds = [matrix_derivative(s, a) for a in range(3)]
    dst = [matrix_derivative(st, a) for a in range(3)]
    edot_fixed = sum(h[a][b] * pair(ds[a], dst[b]) for a in range(3) for b in range(3))
    edot = edot_fixed + F(1, 2) * sum(hdot[i][j] * m[i][j] for i in range(3) for j in range(3))
    transport = pair(ls, advs)
    strain_square = pair(ls, ss)
    rhs = (
        -transport
        -strain_square
        + F(1, 4) * sum(h[i][j] * q[i][j] for i in range(3) for j in range(3))
        - nu * sum(h[i][j] * nn[i][j] for i in range(3) for j in range(3))
    )
    assert edot == rhs, (edot, rhs)
    # Equality-case test for the sharp abstract 1/3 angle bound.
    qe = ((F(2), F(0), F(0)), (F(0), F(-1), F(0)), (F(0), F(0), F(-1)))
    me = ((F(1), F(0), F(0)), (F(0), F(0), F(0)), (F(0), F(0), F(0)))
    qme = sum(qe[i][j] * me[i][j] for i in range(3) for j in range(3))
    mme = sum(me[i][j] * me[i][j] for i in range(3) for j in range(3))
    proj2 = sum(qe[i][j] * qe[i][j] for i in range(3) for j in range(3)) - qme * qme / mme
    assert proj2 == F(1, 3) * sum(qe[i][j] * qe[i][j] for i in range(3) for j in range(3))
    verify_production_connection_algebra()
    verify_extended_barrier_algebra()
    verify_rank_aware_schatten_algebra()
    print("Adaptive anisotropic energy: PASS")
    print("  projected strain equation and pressure pairing: exact")
    print("  trace(Q)=0 and full energy-law signs: exact")
    print("  adaptive constraints Hdot:M=0, Hdot:Q+H:Qdot=0: exact")
    print("  sharp transversality equality case: exact")
    print("  abstract production connection and SPD obstruction: exact")
    print(
        "  abstract two-barrier (including Gram-residual certificate), "
        "isospectral, and six-frame gauges: exact"
    )
    print(
        "  margin steering, compact-height obstruction, and three-chart "
        "coercive atlas: exact"
    )
    print(
        "  rank-aware normalized production, one-sided spectral edge, and "
        "Schatten-optimal connections: exact"
    )


if __name__ == "__main__":
    main()
