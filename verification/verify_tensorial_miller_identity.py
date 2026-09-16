#!/usr/bin/env python3
"""Exact verification of the tensorial refinement of Miller's identity.

For a real, divergence-free trigonometric polynomial u, with
S = sym(grad u) and omega = curl u, the global identity is

    integral omega_i omega_j
      (partial_a partial_b S_ij - partial_i partial_j S_ab) = 0

for every a,b.  The verifier also checks the stronger pointwise Fourier law
H:F = -div(J_H) for a basis of constant symmetric H.  All arithmetic below is
rational Gaussian arithmetic.
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
    gdivide,
    gdot,
    gmul,
    gsub,
)
from verify_full_multiplier_rigidity import nonzero_vectors
from verify_laplacian_rigidity import Vec, add, cross, neg, transverse_basis

GMatrix = Tuple[Tuple[Gaussian, Gaussian, Gaussian], ...]


def gint(value: int | Fraction) -> Gaussian:
    return Fraction(value), Fraction(0)


def gscale(value: Gaussian, scalar: int | Fraction) -> Gaussian:
    return gmul(gint(scalar), value)


def gneg(value: Gaussian) -> Gaussian:
    return -value[0], -value[1]


def gvadd(left: Sequence[Gaussian], right: Sequence[Gaussian]) -> GVec:
    return tuple(gadd(a, b) for a, b in zip(left, right))  # type: ignore[return-value]


def gvscale(vector: Sequence[Gaussian], scalar: int | Fraction | Gaussian) -> GVec:
    factor = scalar if isinstance(scalar, tuple) else gint(scalar)
    return tuple(gmul(factor, value) for value in vector)  # type: ignore[return-value]


def gvcross(left: Sequence[Gaussian], right: Sequence[Gaussian]) -> GVec:
    return (
        gsub(gmul(left[1], right[2]), gmul(left[2], right[1])),
        gsub(gmul(left[2], right[0]), gmul(left[0], right[2])),
        gsub(gmul(left[0], right[1]), gmul(left[1], right[0])),
    )


def gcross(k: Vec, amplitude: Sequence[Gaussian]) -> GVec:
    return (
        gsub(gscale(amplitude[2], k[1]), gscale(amplitude[1], k[2])),
        gsub(gscale(amplitude[0], k[2]), gscale(amplitude[2], k[0])),
        gsub(gscale(amplitude[1], k[0]), gscale(amplitude[0], k[1])),
    )


def omega(k: Vec, amplitude: Sequence[Gaussian]) -> GVec:
    return tuple(gmul(IMAGINARY_UNIT, value) for value in gcross(k, amplitude))  # type: ignore[return-value]


def strain_entry(k: Vec, amplitude: Sequence[Gaussian], i: int, j: int) -> Gaussian:
    symmetric_derivative = gadd(gscale(amplitude[j], k[i]), gscale(amplitude[i], k[j]))
    return gdivide(gmul(IMAGINARY_UNIT, symmetric_derivative), 2)


def strain_matrix(k: Vec, amplitude: Sequence[Gaussian]) -> GMatrix:
    return tuple(
        tuple(strain_entry(k, amplitude, i, j) for j in range(3))
        for i in range(3)
    )


def tensor_sides(modes: Dict[Vec, GVec]) -> Tuple[GMatrix, GMatrix]:
    """Return the two tensors in the identity, before taking their difference."""
    directional = [[ZERO for _ in range(3)] for _ in range(3)]
    hessian = [[ZERO for _ in range(3)] for _ in range(3)]
    omega_modes = {k: omega(k, amplitude) for k, amplitude in modes.items()}
    strain_modes = {k: strain_matrix(k, amplitude) for k, amplitude in modes.items()}
    for p, q, r in product(modes, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        omega_q = omega_modes[q]
        omega_r = omega_modes[r]
        strain_p = strain_modes[p]
        strain_contraction = ZERO
        for i in range(3):
            for j in range(3):
                strain_contraction = gadd(
                    strain_contraction,
                    gmul(strain_p[i][j], gmul(omega_q[i], omega_r[j])),
                )
        hessian_factor = gmul(gdot(omega_q, p), gdot(omega_r, p))
        for a in range(3):
            for b in range(3):
                directional[a][b] = gadd(
                    directional[a][b],
                    gscale(strain_contraction, -p[a] * p[b]),
                )
                hessian[a][b] = gadd(
                    hessian[a][b],
                    gscale(gmul(strain_p[a][b], hessian_factor), -1),
                )
    return (
        tuple(tuple(row) for row in directional),
        tuple(tuple(row) for row in hessian),
    )


def real_matrix(matrix: GMatrix) -> Tuple[Tuple[Fraction, Fraction, Fraction], ...]:
    assert all(value[1] == 0 for row in matrix for value in row)
    return tuple(tuple(value[0] for value in row) for row in matrix)


def symmetric_basis() -> Iterable[Tuple[Tuple[Fraction, ...], ...]]:
    for a in range(3):
        for b in range(a, 3):
            matrix = [[Fraction(0) for _ in range(3)] for _ in range(3)]
            matrix[a][b] = Fraction(1)
            matrix[b][a] = Fraction(1)
            yield tuple(tuple(row) for row in matrix)


def matrix_vector(
    matrix: Sequence[Sequence[Fraction]], vector: Sequence[Gaussian]
) -> GVec:
    return tuple(
        sum_gaussians(gscale(vector[j], matrix[i][j]) for j in range(3))
        for i in range(3)
    )  # type: ignore[return-value]


def sum_gaussians(values: Iterable[Gaussian]) -> Gaussian:
    total = ZERO
    for value in values:
        total = gadd(total, value)
    return total


def add_scalar_mode(field: Dict[Vec, Gaussian], k: Vec, value: Gaussian) -> None:
    field[k] = gadd(field.get(k, ZERO), value)


def add_vector_mode(field: Dict[Vec, GVec], k: Vec, value: Sequence[Gaussian]) -> None:
    field[k] = gvadd(field.get(k, (ZERO, ZERO, ZERO)), value)


def curl_field(field: Dict[Vec, GVec]) -> Dict[Vec, GVec]:
    return {k: omega(k, value) for k, value in field.items()}


def apply_matrix(
    matrix: Sequence[Sequence[Fraction]], field: Dict[Vec, GVec]
) -> Dict[Vec, GVec]:
    return {k: matrix_vector(matrix, value) for k, value in field.items()}


def scalar_product_field(
    left: Dict[Vec, GVec], right: Dict[Vec, GVec]
) -> Dict[Vec, Gaussian]:
    result: Dict[Vec, Gaussian] = {}
    for q, r in product(left, right):
        add_scalar_mode(result, add(q, r), gdot(left[q], right[r]))
    return result


def vector_scalar_field(
    vector: Dict[Vec, GVec], scalar: Dict[Vec, Gaussian]
) -> Dict[Vec, GVec]:
    result: Dict[Vec, GVec] = {}
    for q, r in product(vector, scalar):
        add_vector_mode(result, add(q, r), gvscale(vector[q], scalar[r]))
    return result


def cross_product_field(
    left: Dict[Vec, GVec], right: Dict[Vec, GVec]
) -> Dict[Vec, GVec]:
    result: Dict[Vec, GVec] = {}
    for q, r in product(left, right):
        add_vector_mode(result, add(q, r), gvcross(left[q], right[r]))
    return result


def advective_field(w: Dict[Vec, GVec]) -> Dict[Vec, GVec]:
    result: Dict[Vec, GVec] = {}
    for q, r in product(w, repeat=2):
        derivative = gmul(IMAGINARY_UNIT, gdot(w[q], r))
        add_vector_mode(result, add(q, r), gvscale(w[r], derivative))
    return result


def divergence_field(vector: Dict[Vec, GVec]) -> Dict[Vec, Gaussian]:
    return {
        k: gmul(IMAGINARY_UNIT, gdot(value, k))
        for k, value in vector.items()
    }


def direct_d_field(w: Dict[Vec, GVec], rbw: Dict[Vec, GVec]) -> Dict[Vec, Gaussian]:
    result: Dict[Vec, Gaussian] = {}
    for p, q, r in product(rbw, w, w):
        derivative = gmul(IMAGINARY_UNIT, gdot(w[q], p))
        value = gmul(derivative, gdot(w[r], rbw[p]))
        add_scalar_mode(result, add(add(p, q), r), value)
    return result


def contracted_tensor_field(
    u: Dict[Vec, GVec], w: Dict[Vec, GVec], h: Sequence[Sequence[Fraction]]
) -> Dict[Vec, Gaussian]:
    """Fourier coefficients of H_ab omega_i omega_j(∂ab Sij-∂ij Sab)."""
    result: Dict[Vec, Gaussian] = {}
    strains = {k: strain_matrix(k, value) for k, value in u.items()}
    for p, q, r in product(u, w, w):
        strain_p = strains[p]
        contraction = sum_gaussians(
            gmul(strain_p[i][j], gmul(w[q][i], w[r][j]))
            for i in range(3)
            for j in range(3)
        )
        p_h_p = sum(h[a][b] * p[a] * p[b] for a in range(3) for b in range(3))
        h_strain = sum_gaussians(
            gscale(strain_p[a][b], h[a][b])
            for a in range(3)
            for b in range(3)
        )
        longitudinal = gmul(gdot(w[q], p), gdot(w[r], p))
        value = gadd(gscale(contraction, -p_h_p), gmul(h_strain, longitudinal))
        add_scalar_mode(result, add(add(p, q), r), value)
    return result


def compare_scalar_fields(left: Dict[Vec, Gaussian], right: Dict[Vec, Gaussian]) -> int:
    support = set(left) | set(right)
    assert all(left.get(k, ZERO) == right.get(k, ZERO) for k in support)
    return len(support)


def verify_local_flux(u: Dict[Vec, GVec]) -> Tuple[int, int]:
    """Check H:F=-div J_H mode by mode for a basis of symmetric H."""
    w = curl_field(u)
    eta = curl_field(w)
    v = advective_field(w)
    cases = 0
    coefficients = 0
    for h in symmetric_basis():
        trace = sum(h[i][i] for i in range(3))
        b = tuple(
            tuple((trace / 2 if i == j else 0) - h[i][j] for j in range(3))
            for i in range(3)
        )
        bw = apply_matrix(b, w)
        b_eta = apply_matrix(b, eta)
        curl_bw = curl_field(bw)
        rbw = {k: gvadd(b_eta[k], curl_bw[k]) for k in w}
        gamma = scalar_product_field(w, curl_bw)
        beta = scalar_product_field(w, bw)
        first = vector_scalar_field(w, gamma)
        second = vector_scalar_field(eta, beta)
        third = cross_product_field(bw, v)
        flux_support = set(first) | set(second) | set(third)
        flux = {
            k: gvadd(
                first.get(k, (ZERO, ZERO, ZERO)),
                gvadd(
                    gvscale(second.get(k, (ZERO, ZERO, ZERO)), Fraction(1, 2)),
                    gvscale(third.get(k, (ZERO, ZERO, ZERO)), -1),
                ),
            )
            for k in flux_support
        }
        div_flux = divergence_field(flux)
        d_field = direct_d_field(w, rbw)
        hf_field = contracted_tensor_field(u, w, h)
        coefficients += compare_scalar_fields(d_field, div_flux)
        coefficients += compare_scalar_fields(
            hf_field, {k: gneg(value) for k, value in d_field.items()}
        )
        cases += 1
    return cases, coefficients


def main() -> None:
    vectors = nonzero_vectors(1)
    vector_set = set(vectors)
    phases = tuple(product((ONE, IMAGINARY_UNIT), repeat=3))
    field_checks = 0
    component_checks = 0
    witness = None
    local_samples = []

    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vector_set or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            for polarizations in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                for phase in phases:
                    modes = exact_triad_modes(p, q, r, *polarizations, phase)
                    directional, hessian = tensor_sides(modes)
                    assert directional == hessian
                    assert all(directional[a][b] == directional[b][a] for a in range(3) for b in range(3))
                    component_checks += 6
                    field_checks += 1
                    if len(local_samples) < 3 and field_checks % 311 == 0:
                        local_samples.append(modes)
                    if witness is None and any(value != ZERO for row in directional for value in row):
                        witness = (p, q, r, polarizations, phase, real_matrix(directional))

    assert witness is not None
    local_cases = 0
    local_coefficients = 0
    for modes in local_samples:
        cases, coefficients = verify_local_flux(modes)
        local_cases += cases
        local_coefficients += coefficients
    p, q, r, polarizations, phase, matrix = witness
    print(
        "Tensorial Miller identity: PASS "
        f"({field_checks} exact real triad fields; {component_checks} symmetric-component checks)"
    )
    print("Non-vacuous exact witness:")
    print(f"  triad: {p}, {q}, {r}")
    print(f"  polarizations: {polarizations}")
    print(f"  phases: {phase}")
    print(f"  common nonzero tensor: {matrix}")
    print(
        "Local tensor-flux identity: PASS "
        f"({local_cases} symmetric-matrix cases; {local_coefficients} exact Fourier-coefficient comparisons)"
    )


if __name__ == "__main__":
    main()
