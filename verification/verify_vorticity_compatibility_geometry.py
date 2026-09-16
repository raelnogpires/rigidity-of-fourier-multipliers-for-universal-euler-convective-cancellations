#!/usr/bin/env python3
"""Exact checks for the vorticity-only action of the tensorial Miller defect.

For S = sym(grad u), omega = curl u, and

    F_ab = omega_i omega_j (partial_ab S_ij - partial_ij S_ab),

the pointwise identity checked below is

    (F omega)_a
      = 1/2 [omega x D^2 omega(omega, omega)]_a.

All Fourier calculations use rational Gaussian arithmetic.
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
    exact_triad_modes,
    gadd,
    gdot,
    gmul,
    gsub,
)
from verify_laplacian_rigidity import Vec, neg, transverse_basis
from verify_tensorial_miller_identity import (
    add_vector_mode,
    contracted_tensor_field,
    cross_product_field,
    curl_field,
    gneg,
    gscale,
    gvscale,
    strain_entry,
)

ScalarField = Dict[Vec, Gaussian]
VectorField = Dict[Vec, GVec]
TensorField = Tuple[Tuple[ScalarField, ScalarField, ScalarField], ...]


def conjugate(value: Gaussian) -> Gaussian:
    return value[0], -value[1]


def divide(value: Gaussian, denominator: int) -> Gaussian:
    return value[0] / denominator, value[1] / denominator


def add_scalar_mode(field: ScalarField, k: Vec, value: Gaussian) -> None:
    field[k] = gadd(field.get(k, ZERO), value)


def prune_scalar(field: ScalarField) -> ScalarField:
    return {k: value for k, value in field.items() if value != ZERO}


def prune_vector(field: VectorField) -> VectorField:
    return {
        k: value
        for k, value in field.items()
        if any(component != ZERO for component in value)
    }


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


def symmetric_basis(a: int, b: int) -> Tuple[Tuple[Fraction, ...], ...]:
    matrix = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    matrix[a][b] = Fraction(1)
    matrix[b][a] = Fraction(1)
    return tuple(tuple(row) for row in matrix)


def component_tensor_field(u: VectorField) -> Tuple[VectorField, TensorField]:
    w = curl_field(u)
    components = [[{} for _ in range(3)] for _ in range(3)]
    for a in range(3):
        for b in range(a, 3):
            field = contracted_tensor_field(u, w, symmetric_basis(a, b))
            if a != b:
                field = {k: divide(value, 2) for k, value in field.items()}
            field = prune_scalar(field)
            components[a][b] = field
            components[b][a] = field
    return w, tuple(tuple(row) for row in components)  # type: ignore[return-value]


def tensor_times_vector(f: TensorField, w: VectorField) -> VectorField:
    result: VectorField = {}
    for a in range(3):
        for b in range(3):
            for p, value in f[a][b].items():
                for q, amplitude in w.items():
                    contribution = [ZERO, ZERO, ZERO]
                    contribution[a] = gmul(value, amplitude[b])
                    add_vector_mode(result, tuple(p[j] + q[j] for j in range(3)), contribution)
    return prune_vector(result)


def hessian_along_vorticity(w: VectorField) -> VectorField:
    """Return D^2 omega(omega, omega) by exact Fourier convolution."""
    result: VectorField = {}
    for p, q, r in product(w, repeat=3):
        factor = gneg(gmul(gdot(w[p], r), gdot(w[q], r)))
        contribution = tuple(gmul(factor, value) for value in w[r])
        k = tuple(p[j] + q[j] + r[j] for j in range(3))
        add_vector_mode(result, k, contribution)
    return prune_vector(result)


def quadratic_form(w: VectorField, fw: VectorField) -> ScalarField:
    result: ScalarField = {}
    for p, q in product(w, fw):
        k = tuple(p[j] + q[j] for j in range(3))
        add_scalar_mode(result, k, gdot(w[p], fw[q]))
    return result


def compare_vectors(left: VectorField, right: VectorField) -> int:
    support = set(left) | set(right)
    zero = (ZERO, ZERO, ZERO)
    assert all(left.get(k, zero) == right.get(k, zero) for k in support)
    return len(support)


def epsilon(a: int, b: int, c: int) -> int:
    if len({a, b, c}) < 3:
        return 0
    return 1 if (a, b, c) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)) else -1


def verify_first_compatibility(u: VectorField) -> int:
    checks = 0
    for k, amplitude in u.items():
        w = tuple(
            gmul(IMAGINARY_UNIT, value)
            for value in (
                gsub(gscale(amplitude[2], k[1]), gscale(amplitude[1], k[2])),
                gsub(gscale(amplitude[0], k[2]), gscale(amplitude[2], k[0])),
                gsub(gscale(amplitude[1], k[0]), gscale(amplitude[0], k[1])),
            )
        )
        for a, i, j in product(range(3), repeat=3):
            left = gsub(
                gscale(gmul(IMAGINARY_UNIT, strain_entry(k, amplitude, i, j)), k[a]),
                gscale(gmul(IMAGINARY_UNIT, strain_entry(k, amplitude, a, j)), k[i]),
            )
            right = ZERO
            for ell in range(3):
                right = gadd(
                    right,
                    gscale(
                        gmul(IMAGINARY_UNIT, w[ell]),
                        Fraction(epsilon(a, i, ell) * k[j], 2),
                    ),
                )
            assert left == right
            checks += 1
    return checks


def verify_field(u: VectorField) -> Tuple[int, int, int]:
    compatibility_checks = verify_first_compatibility(u)
    w, f = component_tensor_field(u)
    fw = tensor_times_vector(f, w)
    h = hessian_along_vorticity(w)
    cross = cross_product_field(w, h)
    half_cross = {k: gvscale(value, Fraction(1, 2)) for k, value in cross.items()}
    vector_checks = compare_vectors(fw, half_cross)
    null_field = quadratic_form(w, fw)
    assert not prune_scalar(null_field)
    assert fw
    return compatibility_checks, vector_checks, len(null_field)


def quarter_turn(power: int) -> Gaussian:
    return (ONE, IMAGINARY_UNIT, (Fraction(-1), Fraction(0)), (Fraction(0), Fraction(-1)))[power % 4]


def evaluate_scalar(field: ScalarField, point: Vec) -> Gaussian:
    result = ZERO
    for k, value in field.items():
        phase = quarter_turn(sum(k[j] * point[j] for j in range(3)))
        result = gadd(result, gmul(value, phase))
    return result


def evaluate_vector(field: VectorField, point: Vec) -> GVec:
    return tuple(
        evaluate_scalar({k: value[i] for k, value in field.items()}, point)
        for i in range(3)
    )  # type: ignore[return-value]


def evaluate_tensor(field: TensorField, point: Vec) -> Tuple[Tuple[Gaussian, ...], ...]:
    return tuple(
        tuple(evaluate_scalar(field[a][b], point) for b in range(3))
        for a in range(3)
    )


def real(value: Gaussian) -> Fraction:
    assert value[1] == 0
    return value[0]


def determinant(matrix: Sequence[Sequence[Fraction]]) -> Fraction:
    return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


def simple_witness() -> Tuple[Tuple[Fraction, ...], Tuple[Tuple[Fraction, ...], ...]]:
    # u = (2 cos(y+z), 0, 2 cos x), evaluated at (pi/2, 0, pi/2).
    u: VectorField = {}
    add_real_mode(u, (0, 1, 1), (1, 0, 0), ONE)
    add_real_mode(u, (1, 0, 0), (0, 0, 1), ONE)
    w, f = component_tensor_field(u)
    point = (1, 0, 1)
    w_value = tuple(real(value) for value in evaluate_vector(w, point))
    f_value = tuple(
        tuple(real(value) for value in row)
        for row in evaluate_tensor(f, point)
    )
    assert w_value == (Fraction(0), Fraction(0), Fraction(2))
    assert f_value == (
        (Fraction(0), Fraction(-4), Fraction(-4)),
        (Fraction(-4), Fraction(0), Fraction(0)),
        (Fraction(-4), Fraction(0), Fraction(0)),
    )
    fw = tuple(sum(f_value[a][b] * w_value[b] for b in range(3)) for a in range(3))
    assert fw == (Fraction(-8), Fraction(0), Fraction(0))
    assert sum(w_value[a] * fw[a] for a in range(3)) == 0
    return w_value, f_value


def full_rank_witness() -> Tuple[Fraction, Tuple[Fraction, ...]]:
    # u = -2[(sin(y-z)+sin(x-y-z))e1 + sin(z)e2 + sin(x-y-z)e3].
    u: VectorField = {}
    add_real_mode(u, (0, 0, 1), (0, 1, 0), IMAGINARY_UNIT)
    add_real_mode(u, (0, 1, -1), (1, 0, 0), IMAGINARY_UNIT)
    add_real_mode(u, (1, -1, -1), (1, 0, 1), IMAGINARY_UNIT)
    w, f = component_tensor_field(u)
    w_value = tuple(real(value) for value in evaluate_vector(w, (0, 0, 0)))
    f_value = tuple(
        tuple(real(value) for value in row)
        for row in evaluate_tensor(f, (0, 0, 0))
    )
    assert w_value == (Fraction(4), Fraction(6), Fraction(0))
    assert f_value == (
        (Fraction(-24), Fraction(-16), Fraction(52)),
        (Fraction(-16), Fraction(32), Fraction(-60)),
        (Fraction(52), Fraction(-60), Fraction(40)),
    )
    det = determinant(f_value)
    fw = tuple(sum(f_value[a][b] * w_value[b] for b in range(3)) for a in range(3))
    assert det == 58_752
    assert fw == (Fraction(-192), Fraction(128), Fraction(-152))
    assert sum(w_value[a] * fw[a] for a in range(3)) == 0
    return det, fw


def test_fields() -> Iterable[VectorField]:
    p, q, r = (-1, -1, -1), (0, 0, 1), (1, 1, 0)
    yield exact_triad_modes(
        p,
        q,
        r,
        (0, -1, 1),
        (0, 1, 0),
        (0, 0, -1),
        (ONE, ONE, IMAGINARY_UNIT),
    )

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
    for index, k in enumerate(representatives):
        add_real_mode(
            field,
            k,
            transverse_basis(k)[index % 2],
            (ONE, IMAGINARY_UNIT)[index % 2],
        )
    yield field


def main() -> None:
    compatibility_checks = 0
    vector_checks = 0
    null_coefficients = 0
    for field in test_fields():
        first, second, third = verify_field(field)
        compatibility_checks += first
        vector_checks += second
        null_coefficients += third

    simple_omega, simple_f = simple_witness()
    full_det, full_fw = full_rank_witness()
    print(
        "Vorticity compatibility geometry: PASS "
        f"({compatibility_checks} first-compatibility checks; "
        f"{vector_checks} coefficientwise vector checks; "
        f"{null_coefficients} pointwise-null coefficients)"
    )
    print(f"Simple F omega != 0 witness: omega={simple_omega}; F={simple_f}")
    print(f"Full-rank null-cone witness: det(F)={full_det}; F omega={full_fw}")


if __name__ == "__main__":
    main()
