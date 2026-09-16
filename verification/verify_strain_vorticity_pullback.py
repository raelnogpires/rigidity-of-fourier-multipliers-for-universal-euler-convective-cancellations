#!/usr/bin/env python3
"""Exact semantic regression checks for Corollaries C and E.

Uses rational Gaussian arithmetic, no floating-point tolerances. Finite
examples are regression tests, not a substitute for the universal proof.
The gradient contraction and convective contraction are evaluated separately.
"""
from fractions import Fraction
from itertools import product

from explore_full_multiplier import (
    ZERO, ONE, IMAGINARY_UNIT, exact_triad_modes, gadd, gsub, gmul, gdot,
)
from verify_tensorial_miller_identity import (
    gint, gvadd, gvscale, matrix_vector, omega, strain_matrix,
    sum_gaussians, symmetric_basis,
)

ZERO_MATRIX = tuple((Fraction(0),) * 3 for _ in range(3))
IDENTITY = tuple(tuple(Fraction(i == j) for j in range(3)) for i in range(3))


def norm_sq(k):
    return sum(x*x for x in k)


def inverse_curl(k, v):
    assert norm_sq(k) != 0
    return gvscale(omega(k, v), Fraction(1, norm_sq(k)))


def generator(A, B, k, v):
    return gvadd(matrix_vector(A, v), gvadd(
        matrix_vector(B, omega(k, v)), omega(k, matrix_vector(B, v))))


def completion(B, k, v):
    # Differential operator, evaluated independently of its explicit symbol.
    return gvadd(gvscale(matrix_vector(B, v), norm_sq(k)),
                 omega(k, matrix_vector(B, omega(k, v))))


def b_of_h(H):
    tr = sum(H[i][i] for i in range(3))
    return tuple(tuple(tr / 2 * (i == j) - H[i][j] for j in range(3))
                 for i in range(3))


def h_of_b(B):
    tr = sum(B[i][i] for i in range(3))
    return tuple(tuple(tr * (i == j) - B[i][j] for j in range(3))
                 for i in range(3))


def explicit_symbol(H, k, v):
    kg = tuple(gint(x) for x in k)
    Hk = matrix_vector(H, kg)
    return gvadd(gvscale(v, gdot(kg, Hk)), gvscale(kg, gmul(gint(-1), gdot(Hk, v))))


def resonances(modes):
    for p, q, r in product(modes, repeat=3):
        if all(p[i] + q[i] + r[i] == 0 for i in range(3)):
            yield p, q, r


def strain_cubic(T, modes):
    # Direct sym-grad(Tu) : omega tensor omega.
    curls = {k: omega(k, v) for k, v in modes.items()}
    strains = {k: strain_matrix(k, T(k, v)) for k, v in modes.items()}
    return sum_gaussians(
        gmul(strains[p][i][j], gmul(curls[q][i], curls[r][j]))
        for p, q, r in resonances(modes) for i, j in product(range(3), repeat=2))


def euler_cubic(R, modes):
    # Rw : (w.grad)w, evaluated independently of strain_matrix.
    return sum_gaussians(
        gmul(IMAGINARY_UNIT, gmul(gdot(modes[q], r), gdot(R(p, modes[p]), modes[r])))
        for p, q, r in resonances(modes))


def main():
    matrices = list(symmetric_basis())
    basis = [tuple(gint(i == j) for i in range(3)) for j in range(3)]
    symbol_checks = 0
    for H in matrices:
        B = b_of_h(H)
        assert h_of_b(B) == H
        assert b_of_h(h_of_b(H)) == H
        for k in product(range(-2, 3), repeat=3):
            if k == (0, 0, 0):
                continue
            for v in basis:
                # Full-space composition: no transversality premise.
                actual = generator(ZERO_MATRIX, B, k, omega(k, v))
                assert actual == explicit_symbol(H, k, v)
                transverse = omega(k, v)
                assert completion(B, k, transverse) == explicit_symbol(H, k, transverse)
                assert inverse_curl(k, omega(k, transverse)) == transverse
                assert omega(k, inverse_curl(k, transverse)) == transverse
                symbol_checks += 1
    assert symbol_checks == 2232

    modes = exact_triad_modes((1, 0, 0), (0, 1, 0), (1, 1, 0),
        (0, 1, 1), (1, 0, 0), (1, -1, 1), (ONE, ONE, IMAGINARY_UNIT))
    assert all(gdot(v, k) == ZERO for k, v in modes.items())
    stretching = strain_cubic(lambda k, v: v, modes)
    assert stretching == gint(-2), stretching
    # For the old <Tu, S(u)omega> definition, T=2curl gives twice stretching.
    assert gmul(gint(2), stretching) == gint(-4)
    assert strain_cubic(lambda k, v: gvscale(v, norm_sq(k)), modes) == ZERO

    field_checks = 0
    nonzero_defects = 0
    for phases in product((ONE, IMAGINARY_UNIT), repeat=3):
        field = exact_triad_modes((1, 0, 0), (0, 1, 0), (1, 1, 0),
            (0, 1, 1), (1, 0, 0), (1, -1, 1), phases)
        curls = {k: omega(k, v) for k, v in field.items()}
        # Arbitrary, noncancelling multiplier checks the bridge's sign and normalization.
        arbitrary = lambda k, v: gvscale(matrix_vector(matrices[1], v), norm_sq(k) + 1)
        assert strain_cubic(arbitrary, field) == gmul(gint(-1), euler_cubic(
            lambda k, v: arbitrary(k, inverse_curl(k, v)), curls))
        for M in matrices:
            for A, B in ((M, ZERO_MATRIX), (ZERO_MATRIX, M)):
                T = lambda k, v: generator(A, B, k, omega(k, v))
                assert strain_cubic(T, field) == ZERO
                assert strain_cubic(T, field) == gmul(gint(-1), euler_cubic(
                    lambda k, v: T(k, inverse_curl(k, v)), curls))
                field_checks += 1
            H = M
            B = b_of_h(H)
            scalar = lambda k, v: gvscale(v, gdot(tuple(gint(x) for x in k),
                                                 matrix_vector(H, tuple(gint(x) for x in k))))
            # grad Phi = -k(k.Bu), so sym-grad(grad Phi) is the Hessian term.
            grad_phi = lambda k, v: gvscale(tuple(gint(x) for x in k),
                                           gmul(gint(-1), gdot(matrix_vector(B, v), k)))
            defect = strain_cubic(scalar, field)
            assert defect == strain_cubic(grad_phi, field)
            assert strain_cubic(lambda k, v: completion(B, k, v), field) == ZERO
            nonzero_defects += defect != ZERO
    assert nonzero_defects > 0, 'The anisotropic defect must not be erased by projection.'
    print(f'PASS {symbol_checks} exact symbol/inverse checks; {field_checks} generator field checks')
    print(f'PASS curl pullback and Hessian defect; {nonzero_defects} nonzero anisotropic examples')
    print('PASS negative control: integral omega.S.omega = -2; Miller Laplacian integral = 0')


if __name__ == '__main__':
    main()
