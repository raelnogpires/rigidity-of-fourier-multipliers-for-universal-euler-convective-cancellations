#!/usr/bin/env python3
"""Exact audit of the vorticity-only consequence of the tensorial identity.

For a divergence-free velocity u, write W = curl u and

    F_ab = W_i W_j (partial_ab S_ij - partial_ij S_ab),
    M_ab = ( ((W dot grad)W) x partial_b W )_a
         + ( ((W dot grad)W) x partial_a W )_b.

The kinematic Saint--Venant relation gives the coefficientwise identity

    M_ab = div(W (A_ab + A_ba)) - 2 F_ab,
    A_ab = (e_a x W) dot partial_b W.

Consequently the zero Fourier coefficient of every M_ab vanishes.  The
script also checks the polarized law, where

    B_ab(X;Y,Z) = 1/2 [ L_ab(X,Y,Z) + L_ab(X,Z,Y) ],
    L_ab(X,Y,Z) = (((X dot grad)Y) x partial_b Z)_a
                + (((X dot grad)Y) x partial_a Z)_b,

and

    integral [B_ab(X;Y,Z) + B_ab(Y;X,Z) + B_ab(Z;X,Y)] = 0.

All arithmetic is exact rational Gaussian Fourier arithmetic.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Dict, Sequence, Tuple

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
    gaussian,
)
from verify_laplacian_rigidity import Vec, add
from verify_tensorial_miller_identity import (
    add_scalar_mode,
    advective_field,
    cross_product_field,
    divergence_field,
    gscale,
    gvadd,
    gvscale,
    strain_matrix,
    sum_gaussians,
    vector_scalar_field,
    curl_field,
)


def gneg(value: Gaussian) -> Gaussian:
    return -value[0], -value[1]


def partial_field(field: Dict[Vec, GVec], direction: int) -> Dict[Vec, GVec]:
    return {
        k: gvscale(value, gscale(IMAGINARY_UNIT, k[direction]))
        for k, value in field.items()
    }


def epsilon(i: int, j: int, k: int) -> int:
    if (i, j, k) in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
        return 1
    if (i, j, k) in ((0, 2, 1), (2, 1, 0), (1, 0, 2)):
        return -1
    return 0


def direct_F_fields(
    velocity: Dict[Vec, GVec], vorticity: Dict[Vec, GVec]
) -> list[list[Dict[Vec, Gaussian]]]:
    """Fourier fields of F_ab, with no zero-mode assumption."""
    strains = {k: strain_matrix(k, value) for k, value in velocity.items()}
    result = [[{} for _ in range(3)] for _ in range(3)]
    for p, q, r in product(strains, vorticity, vorticity):
        target = add(add(p, q), r)
        strain = strains[p]
        left = vorticity[q]
        right = vorticity[r]
        contraction = sum_gaussians(
            gmul(strain[i][j], gmul(left[i], right[j]))
            for i in range(3)
            for j in range(3)
        )
        longitudinal = gmul(gdot(left, p), gdot(right, p))
        for a, b in product(range(3), repeat=2):
            value = gadd(
                gscale(contraction, -p[a] * p[b]),
                gmul(strain[a][b], longitudinal),
            )
            add_scalar_mode(result[a][b], target, value)
    return result


def M_fields(
    vorticity: Dict[Vec, GVec]
) -> list[list[Dict[Vec, Gaussian]]]:
    """Fourier fields of the symmetric vorticity-gradient tensor M."""
    advective = advective_field(vorticity)
    result = [[{} for _ in range(3)] for _ in range(3)]
    for a, b in product(range(3), repeat=2):
        first = cross_product_field(advective, partial_field(vorticity, b))
        second = cross_product_field(advective, partial_field(vorticity, a))
        support = set(first) | set(second)
        for k in support:
            value = gadd(
                first.get(k, (ZERO, ZERO, ZERO))[a],
                second.get(k, (ZERO, ZERO, ZERO))[b],
            )
            add_scalar_mode(result[a][b], k, value)
    return result


def A_fields(
    vorticity: Dict[Vec, GVec]
) -> list[list[Dict[Vec, Gaussian]]]:
    """Fourier fields of A_ab=(e_a x W) dot partial_b W."""
    result = [[{} for _ in range(3)] for _ in range(3)]
    for a, b in product(range(3), repeat=2):
        # e_a is spatially constant: apply it modewise, rather than making
        # a fake copy of e_a at every Fourier mode.
        ea = [ZERO, ZERO, ZERO]
        ea[a] = ONE
        eaw = {k: _cross_constant(ea, value) for k, value in vorticity.items()}
        result[a][b] = _scalar_product_field(eaw, partial_field(vorticity, b))
    return result


def _cross_constant(left: Sequence[Gaussian], right: Sequence[Gaussian]) -> GVec:
    return (
        gadd(gmul(left[1], right[2]), gneg(gmul(left[2], right[1]))),
        gadd(gmul(left[2], right[0]), gneg(gmul(left[0], right[2]))),
        gadd(gmul(left[0], right[1]), gneg(gmul(left[1], right[0]))),
    )


def _scalar_product_field(
    left: Dict[Vec, GVec], right: Dict[Vec, GVec]
) -> Dict[Vec, Gaussian]:
    result: Dict[Vec, Gaussian] = {}
    for q, r in product(left, right):
        add_scalar_mode(result, add(q, r), gdot(left[q], right[r]))
    return result


def compare_from_F(velocity: Dict[Vec, GVec]) -> int:
    """Check M=div(W(A+A^T))-2F coefficient by coefficient."""
    w = curl_field(velocity)
    F = direct_F_fields(velocity, w)
    M = M_fields(w)
    A = A_fields(w)
    comparisons = 0
    for a, b in product(range(3), repeat=2):
        asym = {
            k: gadd(A[a][b].get(k, ZERO), A[b][a].get(k, ZERO))
            for k in set(A[a][b]) | set(A[b][a])
        }
        div_WA = divergence_field(vector_scalar_field(w, asym))
        support = set(F[a][b]) | set(M[a][b]) | set(div_WA)
        for k in support:
            expected = gsub(
                div_WA.get(k, ZERO),
                gscale(F[a][b].get(k, ZERO), 2),
            )
            assert M[a][b].get(k, ZERO) == expected, (
                a,
                b,
                k,
                M[a][b].get(k, ZERO),
                expected,
            )
            comparisons += 1
    return comparisons


def trilinear_L(
    x: Dict[Vec, GVec],
    y: Dict[Vec, GVec],
    z: Dict[Vec, GVec],
    a: int,
    b: int,
) -> Gaussian:
    """Zero-mode integral of L_ab(X,Y,Z)."""
    total = ZERO
    for kx, xx in x.items():
        for ky, yy in y.items():
            advective = gvscale(
                yy,
                gmul(IMAGINARY_UNIT, gdot(xx, ky)),
            )
            for kz, zz in z.items():
                if add(add(kx, ky), kz) != (0, 0, 0):
                    continue
                d_b = gvscale(zz, gscale(IMAGINARY_UNIT, kz[b]))
                d_a = gvscale(zz, gscale(IMAGINARY_UNIT, kz[a]))
                cross_b = _cross_constant(advective, d_b)
                cross_a = _cross_constant(advective, d_a)
                total = gadd(total, gadd(cross_b[a], cross_a[b]))
    return total


def trilinear_B(
    x: Dict[Vec, GVec],
    y: Dict[Vec, GVec],
    z: Dict[Vec, GVec],
    a: int,
    b: int,
) -> Gaussian:
    """Symmetrize trilinear_L in the last two fields."""
    return gscale(
        gadd(trilinear_L(x, y, z, a, b), trilinear_L(x, z, y, a, b)),
        Fraction(1, 2),
    )


def one_mode(k: Vec, amplitude: Vec) -> Dict[Vec, GVec]:
    value = tuple(gaussian(component) for component in amplitude)
    return {k: value}


def verify_polarized_law() -> int:
    p = (-1, -1, -1)
    q = (0, 0, 1)
    r = (1, 1, 0)
    x = one_mode(p, (0, -1, 1))
    y = one_mode(q, (0, 1, 0))
    z = one_mode(r, (0, 0, 1))
    checks = 0
    values = []
    for a, b in product(range(3), repeat=2):
        assert trilinear_B(x, y, z, a, b) == trilinear_B(x, z, y, a, b)
        value = gadd(
            gadd(
                trilinear_B(x, y, z, a, b),
                trilinear_B(y, x, z, a, b),
            ),
            trilinear_B(z, x, y, a, b),
        )
        assert value == ZERO, (a, b, value)
        values.append(
            (
                trilinear_B(x, y, z, a, b),
                trilinear_B(y, x, z, a, b),
                trilinear_B(z, x, y, a, b),
            )
        )
        checks += 1
    assert any(any(value != ZERO for value in triple) for triple in values)
    return checks


def verify_nonzero_mean_extension() -> int:
    """Check that a constant background vorticity does not change the mean law."""
    # This field is divergence-free mode by mode, but has a nonzero constant
    # mode, so it is not itself the curl of a periodic velocity.
    background = {
        (0, 0, 0): (gaussian(2), gaussian(-1), gaussian(3)),
        (1, 1, 0): (gaussian(1), gaussian(-1), gaussian(0)),
        (-1, -1, 0): (gaussian(1), gaussian(-1), gaussian(0)),
        (1, 0, 2): (gaussian(2), gaussian(0), gaussian(-1)),
        (-1, 0, -2): (gaussian(2), gaussian(0), gaussian(-1)),
        (0, 1, 1): (gaussian(1), gaussian(0), gaussian(0)),
        (0, -1, -1): (gaussian(1), gaussian(0), gaussian(0)),
    }
    M = M_fields(background)
    checks = 0
    for a, b in product(range(3), repeat=2):
        assert M[a][b].get((0, 0, 0), ZERO) == ZERO, (
            a,
            b,
            M[a][b].get((0, 0, 0), ZERO),
        )
        checks += 1
    return checks


def evaluate_point(field: Dict[Vec, GVec], point: Vec) -> GVec:
    phases = (ONE, IMAGINARY_UNIT, (Fraction(-1), Fraction(0)), (Fraction(0), Fraction(-1)))
    result = (ZERO, ZERO, ZERO)
    for k, value in field.items():
        phase = phases[sum(k[i] * point[i] for i in range(3)) % 4]
        result = gvadd(result, gvscale(value, phase))
    return result


def evaluate_gradient(field: Dict[Vec, GVec], point: Vec) -> Tuple[Tuple[Gaussian, ...], ...]:
    phases = (ONE, IMAGINARY_UNIT, (Fraction(-1), Fraction(0)), (Fraction(0), Fraction(-1)))
    result = [[ZERO for _ in range(3)] for _ in range(3)]
    for k, value in field.items():
        phase = phases[sum(k[i] * point[i] for i in range(3)) % 4]
        for i in range(3):
            for b in range(3):
                result[i][b] = gadd(
                    result[i][b],
                    gmul(value[i], gmul(gscale(IMAGINARY_UNIT, k[b]), phase)),
                )
    return tuple(tuple(row) for row in result)


def pointwise_witness() -> Tuple[Tuple[Gaussian, Gaussian, Gaussian], ...]:
    p = (-1, -1, -1)
    q = (0, 0, 1)
    r = (1, 1, 0)
    velocity = exact_triad_modes(
        p,
        q,
        r,
        (0, -1, 1),
        (0, 1, 0),
        (0, 0, -1),
        (ONE, ONE, IMAGINARY_UNIT),
    )
    w = curl_field(velocity)
    point = (0, 1, 0)
    W = evaluate_point(w, point)
    gradient = evaluate_gradient(w, point)
    V = tuple(
        sum_gaussians(gmul(gradient[i][j], W[j]) for j in range(3))
        for i in range(3)
    )
    matrix = []
    for a, b in product(range(3), repeat=2):
        ea = [ZERO, ZERO, ZERO]
        ea[a] = ONE
        eb = [ZERO, ZERO, ZERO]
        eb[b] = ONE
        first = _cross_constant(V, tuple(gradient[i][b] for i in range(3)))[a]
        second = _cross_constant(V, tuple(gradient[i][a] for i in range(3)))[b]
        matrix.append(gadd(first, second))
    result = tuple(tuple(matrix[3 * a + b] for b in range(3)) for a in range(3))
    expected = (
        ((ZERO), (ZERO), gaussian(8)),
        ((ZERO), (ZERO), gaussian(8)),
        (gaussian(8), gaussian(8), gaussian(16)),
    )
    assert result == expected, result
    return result


def main() -> None:
    p = (-1, -1, -1)
    q = (0, 0, 1)
    r = (1, 1, 0)
    samples = [
        exact_triad_modes(
            p,
            q,
            r,
            (0, -1, 1),
            (0, 1, 0),
            (0, 0, -1),
            (ONE, ONE, IMAGINARY_UNIT),
        ),
        exact_triad_modes(
            p,
            q,
            r,
            (1, 0, -1),
            (1, 0, 0),
            (1, -1, 0),
            (IMAGINARY_UNIT, ONE, ONE),
        ),
    ]
    comparisons = sum(compare_from_F(sample) for sample in samples)
    polarized = verify_polarized_law()
    mean_checks = verify_nonzero_mean_extension()
    witness = pointwise_witness()
    print(
        "Vorticity-only compatibility-action identity: PASS "
        f"({comparisons} exact coefficient comparisons)"
    )
    print(
        "Polarized law: PASS "
        f"({polarized} exact tensor-component checks; last-two-field symmetrization)"
    )
    print(f"Nonzero-mean extension: PASS ({mean_checks} exact mean-mode checks)")
    print(f"Nonzero pointwise witness M_ab: {witness}")


if __name__ == "__main__":
    main()
