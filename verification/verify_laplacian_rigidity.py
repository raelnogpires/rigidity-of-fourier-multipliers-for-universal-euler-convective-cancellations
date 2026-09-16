#!/usr/bin/env python3
"""Exact checks for research-note-laplacian-rigidity.md.

No external packages are required.  Fourier integrals use normalized Haar
measure on (R / 2 pi Z)^3, so integration extracts the zero Fourier mode.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import gcd
from random import Random
from typing import Callable, Dict, Iterable, Sequence, Tuple

Vec = Tuple[int, int, int]
CVec = Tuple[complex, complex, complex]
Symbol = Callable[[Vec], float]


def add(a: Vec, b: Vec) -> Vec:
    return tuple(a[i] + b[i] for i in range(3))  # type: ignore[return-value]


def neg(a: Vec) -> Vec:
    return tuple(-x for x in a)  # type: ignore[return-value]


def dot(a: Sequence[complex], b: Sequence[complex]) -> complex:
    return sum(a[i] * b[i] for i in range(3))


def cross(a: Sequence[complex], b: Sequence[complex]) -> CVec:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def norm2(k: Vec) -> int:
    return int(dot(k, k).real)


def transverse_basis(k: Vec) -> Tuple[Vec, Vec]:
    candidates = [cross(k, e) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    result = []
    for candidate in candidates:
        v = tuple(int(x.real) for x in candidate)
        if v == (0, 0, 0):
            continue
        if result and cross(result[0], v) == (0, 0, 0):
            continue
        result.append(v)
        if len(result) == 2:
            return result[0], result[1]
    raise ValueError(f"could not construct a transverse basis for {k}")


def triad_coefficient(
    p: Vec, q: Vec, r: Vec, a: Vec, b: Vec, c: Vec
) -> Tuple[int, int, int]:
    def one(k: Vec, ell: Vec, m: Vec, x: Vec, y: Vec, z: Vec) -> int:
        value = (
            dot(k, cross(ell, y)) * dot(x, cross(m, z))
            + dot(k, cross(m, z)) * dot(x, cross(ell, y))
        )
        return int(value.real)

    return (
        one(p, q, r, a, b, c),
        one(q, r, p, b, c, a),
        one(r, p, q, c, a, b),
    )


def matrix_symbol_row(k: Vec) -> Tuple[int, int, int, int, int, int]:
    x, y, z = k
    return (x * x, y * y, z * z, 2 * x * y, 2 * x * z, 2 * y * z)


def anisotropic_constraint(
    p: Vec, q: Vec, r: Vec, a: Vec, b: Vec, c: Vec
) -> Tuple[int, ...]:
    coeffs = triad_coefficient(p, q, r, a, b, c)
    symbols = (matrix_symbol_row(p), matrix_symbol_row(q), matrix_symbol_row(r))
    row = tuple(sum(coeffs[i] * symbols[i][j] for i in range(3)) for j in range(6))
    nonzero = [abs(x) for x in row if x]
    divisor = nonzero[0]
    for value in nonzero[1:]:
        a0, b0 = divisor, value
        while b0:
            a0, b0 = b0, a0 % b0
        divisor = a0
    return tuple(x // divisor for x in row)


def quadratic_symbol(k: Vec, coefficients: Sequence[int]) -> int:
    return sum(x * y for x, y in zip(matrix_symbol_row(k), coefficients))


def strain(k: Vec, amplitude: CVec) -> Tuple[Tuple[complex, ...], ...]:
    return tuple(
        tuple(0.5j * (k[i] * amplitude[j] + k[j] * amplitude[i]) for j in range(3))
        for i in range(3)
    )


def vorticity(k: Vec, amplitude: CVec) -> CVec:
    return tuple(1j * x for x in cross(k, amplitude))  # type: ignore[return-value]


def contraction(matrix: Sequence[Sequence[complex]], a: CVec, b: CVec) -> complex:
    return sum(matrix[i][j] * a[i] * b[j] for i in range(3) for j in range(3))


def fourier_cubic(
    modes: Dict[Vec, CVec], multiplier: Callable[[int], float]
) -> complex:
    return fourier_cubic_symbol(modes, lambda k: multiplier(norm2(k)))


def fourier_cubic_symbol(modes: Dict[Vec, CVec], symbol: Symbol) -> complex:
    total = 0j
    for p, q, r in product(modes, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        total += symbol(p) * contraction(
            strain(p, modes[p]), vorticity(q, modes[q]), vorticity(r, modes[r])
        )
    return total


def helical_multiplier_cubic(
    modes: Dict[Vec, CVec], scalar_symbol: Symbol, curl_symbol: Symbol
) -> complex:
    """Compute <sym grad(Tu), omega tensor omega> for T=a(D)+b(D)curl."""
    total = 0j
    for p, q, r in product(modes, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        omega_p = vorticity(p, modes[p])
        transformed = tuple(
            scalar_symbol(p) * modes[p][i] + curl_symbol(p) * omega_p[i]
            for i in range(3)
        )
        total += contraction(
            strain(p, transformed), vorticity(q, modes[q]), vorticity(r, modes[r])
        )
    return total


def euler_transport_cubic(modes: Dict[Vec, CVec], symbol: Symbol) -> complex:
    """Compute <Nw, (w dot grad)w> for a divergence-free Fourier field w."""
    total = 0j
    for p, q, r in product(modes, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        differentiated = tuple(1j * dot(modes[q], r) * x for x in modes[r])
        total += symbol(p) * dot(modes[p], differentiated)
    return total


def euler_cubic_with_test(
    test_modes: Dict[Vec, CVec], velocity_modes: Dict[Vec, CVec]
) -> complex:
    """Compute <test, (w dot grad)w> in Fourier variables."""
    total = 0j
    for p, q, r in product(velocity_modes, repeat=3):
        if p not in test_modes or add(add(p, q), r) != (0, 0, 0):
            continue
        differentiated = tuple(
            1j * dot(velocity_modes[q], r) * x for x in velocity_modes[r]
        )
        total += dot(test_modes[p], differentiated)
    return total


def mode_commutator(modes: Dict[Vec, CVec], symbol: Symbol) -> complex:
    """Evaluate the right side of the general mode identity (2.2)."""
    omega_modes = {k: vorticity(k, amplitude) for k, amplitude in modes.items()}
    total = 0j
    for k, ell in product(modes, repeat=2):
        omega_mode = omega_modes.get(neg(add(k, ell)))
        if omega_mode is None:
            continue
        coefficient = 0.5 * (
            symbol(ell) * norm2(k) - symbol(k) * norm2(ell)
        )
        total += coefficient * dot(modes[k], cross(modes[ell], omega_mode))
    return total


def shell_commutator(
    modes: Dict[Vec, CVec], multiplier: Callable[[int], float]
) -> complex:
    """Evaluate the right side of equation (2.1) directly in Fourier space."""
    shells: Dict[int, Dict[Vec, CVec]] = {}
    for k, amplitude in modes.items():
        shells.setdefault(norm2(k), {})[k] = amplitude
    omega_modes = {k: vorticity(k, amplitude) for k, amplitude in modes.items()}

    total = 0j
    eigenvalues = sorted(shells)
    for i, lam in enumerate(eigenvalues):
        for mu in eigenvalues[i + 1 :]:
            integral = 0j
            for k, uk in shells[lam].items():
                for ell, uell in shells[mu].items():
                    omega_mode = omega_modes.get(neg(add(k, ell)))
                    if omega_mode is not None:
                        integral += dot(uk, cross(uell, omega_mode))
            coefficient = lam * mu * (
                multiplier(mu) / mu - multiplier(lam) / lam
            )
            total += coefficient * integral
    return total


def triad_modes(
    p: Vec,
    q: Vec,
    r: Vec,
    a: Vec,
    b: Vec,
    c: Vec,
    phases: Tuple[complex, complex, complex] = (1j, 1, 1),
) -> Dict[Vec, CVec]:
    modes: Dict[Vec, CVec] = {
        p: tuple(phases[0] * x for x in a),
        q: tuple(phases[1] * x for x in b),
        r: tuple(phases[2] * x for x in c),
    }
    for k in (p, q, r):
        modes[neg(k)] = tuple(x.conjugate() for x in modes[k])
    return modes


def euler_triad_coefficient(
    p: Vec, q: Vec, r: Vec, a: Vec, b: Vec, c: Vec
) -> Tuple[int, int, int]:
    def one(k: Vec, ell: Vec, m: Vec, x: Vec, y: Vec, z: Vec) -> int:
        del k
        value = dot(x, z) * dot(y, m) + dot(x, y) * dot(z, ell)
        return int(value.real)

    return (
        one(p, q, r, a, b, c),
        one(q, r, p, b, c, a),
        one(r, p, q, c, a, b),
    )


def constructive_rigidity_witness(symbol: Symbol, p: Vec, q: Vec) -> Dict[Vec, CVec]:
    """Construct a triad detecting unequal symbol ratios at p and q."""
    z_complex = cross(p, q)
    z = tuple(int(x.real) for x in z_complex)
    if z == (0, 0, 0):
        raise ValueError("p and q must be non-collinear")
    if symbol(p) * norm2(q) == symbol(q) * norm2(p):
        raise ValueError("the symbol ratios at p and q must differ")
    r = neg(add(p, q))
    jp = tuple(int(x.real) for x in cross(z, p))
    jq = tuple(int(x.real) for x in cross(z, q))
    jr = tuple(int(x.real) for x in cross(z, r))
    candidates = ((jp, z, z), (z, jq, z), (z, z, jr))
    for a, b, c in candidates:
        coefficients = triad_coefficient(p, q, r, a, b, c)
        defect = sum(
            value * symbol(k)
            for value, k in zip(coefficients, (p, q, r))
        )
        if defect:
            return triad_modes(p, q, r, a, b, c)
    raise AssertionError("triad spanning lemma failed to find a witness")


def constructive_complex_scalar_witness(
    symbol: Symbol, p: Vec, q: Vec
) -> Dict[Vec, CVec]:
    """Detect a non-Laplacian reality-compatible complex scalar symbol.

    For a real-preserving symbol, the all-real and one-i phase choices isolate
    the imaginary and real parts of the same triad coefficient.  Trying both
    phase parities makes the witness valid even when the defect is purely odd
    (for example ``symbol(k) = 1j*k[0]``).
    """
    z_complex = cross(p, q)
    z = tuple(int(x.real) for x in z_complex)
    if z == (0, 0, 0):
        raise ValueError("p and q must be non-collinear")
    r = neg(add(p, q))
    jp = tuple(int(x.real) for x in cross(z, p))
    jq = tuple(int(x.real) for x in cross(z, q))
    jr = tuple(int(x.real) for x in cross(z, r))
    candidates = ((jp, z, z), (z, jq, z), (z, z, jr))
    phases = (
        (1, 1, 1),
        (1j, 1, 1),
        (1, 1j, 1),
        (1, 1, 1j),
        (1j, 1j, 1),
        (1j, 1, 1j),
        (1, 1j, 1j),
        (1j, 1j, 1j),
    )
    for a, b, c in candidates:
        coefficients = triad_coefficient(p, q, r, a, b, c)
        weighted = sum(
            value * symbol(k) for value, k in zip(coefficients, (p, q, r))
        )
        if weighted == 0:
            continue
        for phase in phases:
            modes = triad_modes(p, q, r, a, b, c, phase)
            defect = fourier_cubic_symbol(modes, symbol)
            if abs(defect) > 1e-9:
                return modes
    raise AssertionError("complex scalar triad spanning lemma failed")


def constructive_transport_witness(symbol: Symbol, p: Vec, q: Vec) -> Dict[Vec, CVec]:
    """Construct a triad detecting unequal scalar Euler-energy weights."""
    z_complex = cross(p, q)
    z = tuple(int(x.real) for x in z_complex)
    if z == (0, 0, 0):
        raise ValueError("p and q must be non-collinear")
    if symbol(p) == symbol(q):
        raise ValueError("the symbol values at p and q must differ")
    r = neg(add(p, q))
    jp = tuple(int(x.real) for x in cross(z, p))
    jq = tuple(int(x.real) for x in cross(z, q))
    jr = tuple(int(x.real) for x in cross(z, r))
    candidates = ((jp, z, z), (z, jq, z), (z, z, jr))
    for a, b, c in candidates:
        coefficients = euler_triad_coefficient(p, q, r, a, b, c)
        defect = sum(
            value * symbol(k)
            for value, k in zip(coefficients, (p, q, r))
        )
        if defect:
            return triad_modes(p, q, r, a, b, c)
    raise AssertionError("Euler triad spanning lemma failed to find a witness")


def inverse_curl(modes: Dict[Vec, CVec]) -> Dict[Vec, CVec]:
    """Return u with curl(u)=w for a mean-zero divergence-free field w."""
    return {
        k: tuple(x / norm2(k) for x in vorticity(k, amplitude))
        for k, amplitude in modes.items()
    }


def explicit_modes(n: int) -> Dict[Vec, CVec]:
    p, q, r = (-n, -1, -1), (0, 0, 1), (n, 1, 0)
    a, b, c = (0, -1, 1), (-1, 0, 0), (1, -n, 0)
    return triad_modes(p, q, r, a, b, c)


def deterministic_multishell_modes() -> Dict[Vec, CVec]:
    """A reproducible real, divergence-free field spanning several shells."""
    generator = Random(20260904)
    modes: Dict[Vec, CVec] = {}
    for k in product((-1, 0, 1), repeat=3):
        if k == (0, 0, 0) or k in modes or neg(k) in modes:
            continue
        raw = tuple(
            complex(generator.randint(-3, 3), generator.randint(-3, 3))
            for _ in range(3)
        )
        projection = dot(k, raw) / norm2(k)
        amplitude = tuple(raw[i] - projection * k[i] for i in range(3))
        modes[k] = amplitude  # type: ignore[assignment]
        modes[neg(k)] = tuple(x.conjugate() for x in amplitude)  # type: ignore[assignment]
    return modes


def rank(rows: Iterable[Sequence[int]]) -> int:
    matrix = [[Fraction(x) for x in row] for row in rows]
    if not matrix:
        return 0
    pivot_row = 0
    for column in range(len(matrix[0])):
        pivot = next(
            (i for i in range(pivot_row, len(matrix)) if matrix[i][column]), None
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        scale = matrix[pivot_row][column]
        matrix[pivot_row] = [x / scale for x in matrix[pivot_row]]
        for i in range(len(matrix)):
            if i == pivot_row:
                continue
            scale = matrix[i][column]
            matrix[i] = [
                matrix[i][j] - scale * matrix[pivot_row][j]
                for j in range(len(matrix[0]))
            ]
        pivot_row += 1
    return pivot_row


def square_determinant(rows: Sequence[Sequence[int]]) -> Fraction:
    """Exact determinant of a square integer matrix."""
    matrix = [[Fraction(x) for x in row] for row in rows]
    size = len(matrix)
    assert all(len(row) == size for row in matrix)
    result = Fraction(1)
    for column in range(size):
        pivot = next(
            (i for i in range(column, size) if matrix[i][column]),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            result = -result
        pivot_value = matrix[column][column]
        result *= pivot_value
        for i in range(column + 1, size):
            factor = matrix[i][column] / pivot_value
            for j in range(column + 1, size):
                matrix[i][j] -= factor * matrix[column][j]
    return result


def primitive_integer_row(row: Sequence[int]) -> list[int]:
    """Divide a nonzero integer row by its positive content."""
    content = 0
    for value in row:
        content = gcd(content, abs(value))
    assert content
    return [value // content for value in row]


def add_independent_rational_row(
    basis: Dict[int, list[Fraction]], source: Sequence[int]
) -> bool:
    """Add one exact row to a row-echelon basis, if it increases rank."""
    row = [Fraction(value) for value in source]
    for pivot in sorted(basis):
        if not row[pivot]:
            continue
        factor = row[pivot]
        row = [x - factor * y for x, y in zip(row, basis[pivot])]
    pivot = next((i for i, value in enumerate(row) if value), None)
    if pivot is None:
        return False
    scale = row[pivot]
    basis[pivot] = [value / scale for value in row]
    return True


def complex_scalar_observation_row(
    modes: Tuple[Vec, Vec, Vec],
    coefficients: Tuple[int, int, int],
    theta: complex,
    representatives: Sequence[Vec],
) -> list[int]:
    """Real observation row for a reality-compatible complex scalar symbol."""
    row: list[int] = []
    for representative in representatives:
        for imaginary in (False, True):
            weighted = 0j
            for mode, coefficient in zip(modes, coefficients):
                if mode == representative:
                    value = 1j if imaginary else 1
                elif mode == neg(representative):
                    value = -1j if imaginary else 1
                else:
                    value = 0
                weighted += coefficient * value
            observation = 2 * (-1j * theta * weighted).real
            assert abs(observation - round(observation)) < 1e-9
            row.append(round(observation))
    return row


def select_complex_scalar_seed_rows(
    box: int = 1,
) -> Tuple[list[Vec], int, list[list[int]]]:
    """Select an exact codimension-one row basis on a finite cube."""
    vectors = [
        k
        for k in product(range(-box, box + 1), repeat=3)
        if k != (0, 0, 0)
    ]
    representatives = sorted({unoriented(k) for k in vectors})
    phases = tuple(product((1, 1j), repeat=3))
    basis: Dict[int, list[Fraction]] = {}
    selected: list[list[int]] = []
    checked = 0
    expected_rank = 2 * len(representatives) - 1
    energy = []
    for k in representatives:
        energy.extend((norm2(k), 0))

    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors or not (p <= q <= r):
                continue
            if cross(p, q) == (0, 0, 0):
                continue
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                coefficients = triad_coefficient(p, q, r, a, b, c)
                for phase in phases:
                    theta = phase[0] * phase[1] * phase[2]
                    row = complex_scalar_observation_row(
                        (p, q, r), coefficients, theta, representatives
                    )
                    if not any(row):
                        continue
                    checked += 1
                    assert sum(x * y for x, y in zip(row, energy)) == 0
                    if add_independent_rational_row(basis, row):
                        selected.append(row)
                    if len(basis) == expected_rank:
                        return representatives, checked, selected
    raise AssertionError("complex scalar seed failed to reach codimension one")


def check_complex_scalar_seed_certificate(box: int = 1) -> Tuple[int, int, int]:
    """Exact rank certificate after allowing complex reality-compatible symbols."""
    representatives, checked, selected = select_complex_scalar_seed_rows(box)
    return len(representatives), checked, len(selected)


def scalar_step_row(
    p: Vec, q: Vec, r: Vec, representatives: Sequence[Vec]
) -> list[int]:
    """One explicit scalar test whose target coefficient never vanishes."""
    assert add(add(p, q), r) == (0, 0, 0)
    z = cross(q, r)
    assert z != (0, 0, 0)
    # In the notation of Section 3, A=z, B=Jq, C=z produces V_q.
    # Its p/target component is -|q|^2|z|^4 (up to orientation), hence is
    # nonzero for every non-collinear triad.
    j_q = cross(z, q)
    coefficients = triad_coefficient(p, q, r, z, j_q, z)
    row = [0] * len(representatives)
    index = {k: i for i, k in enumerate(representatives)}
    for mode, coefficient in zip((p, q, r), coefficients):
        row[index[unoriented(mode)]] += coefficient
    assert row[index[unoriented(p)]] != 0
    assert sum(
        coefficient * norm2(mode)
        for coefficient, mode in zip(coefficients, (p, q, r))
    ) == 0
    return row


def check_scalar_sparse_certificate(box: int = 2) -> Tuple[int, int, int]:
    """Check the M-1 scalar certificate along the explicit cube ordering."""
    # Imported lazily to avoid a module cycle when the sparse verifier imports
    # this file for its shared Fourier primitives.
    from verify_sparse_certificate import propagation_order

    representatives, steps = propagation_order(box)
    seed_representatives = [
        (0, 0, 1),
        (0, 1, 0),
        (0, 1, 1),
        (1, 0, 0),
        (1, 0, 1),
        (1, 1, 0),
        (1, 1, 1),
    ]
    seed_vectors = seed_representatives + [neg(k) for k in seed_representatives]
    seed_index = {k: i for i, k in enumerate(seed_representatives)}
    seed_basis: Dict[int, list[Fraction]] = {}
    selected_seed_rows: list[list[int]] = []
    seed_rows = 0
    for p in seed_vectors:
        for q in seed_vectors:
            r = neg(add(p, q))
            if r not in seed_vectors or not (p <= q <= r):
                continue
            if cross(p, q) == (0, 0, 0):
                continue
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                coefficients = triad_coefficient(p, q, r, a, b, c)
                row = [0] * len(seed_representatives)
                for mode, coefficient in zip((p, q, r), coefficients):
                    row[seed_index[unoriented(mode)]] += coefficient
                if any(row):
                    seed_rows += 1
                    if add_independent_rational_row(seed_basis, row):
                        selected_seed_rows.append(row)
    assert len(seed_basis) == len(seed_representatives) - 1

    global_index = {k: i for i, k in enumerate(representatives)}
    full_basis: Dict[int, list[Fraction]] = {}
    for seed_row in selected_seed_rows:
        global_row = [0] * len(representatives)
        for mode, coefficient in zip(seed_representatives, seed_row):
            global_row[global_index[mode]] = coefficient
        assert add_independent_rational_row(full_basis, global_row)
    for _target, p, q, r in steps:
        row = scalar_step_row(p, q, r, representatives)
        assert add_independent_rational_row(full_basis, row)
    assert len(full_basis) == len(representatives) - 1
    assert len(steps) == len(representatives) - len(seed_representatives)
    return len(representatives), seed_rows, len(full_basis)


def check_complex_scalar_sparse_certificate(box: int = 2) -> Tuple[int, int, int]:
    """Build the optimal 2M-1 certificate for the full scalar reality class."""
    from verify_sparse_certificate import propagation_order

    representatives, steps = propagation_order(box)
    seed_representatives, seed_candidates, seed_rows = (
        minimal_signed_scalar_seed_rows()
    )
    assert len(seed_representatives) == 6
    assert len(seed_rows) == 11
    known = set(seed_representatives)
    known.update(neg(k) for k in seed_representatives)
    global_index = {mode: index for index, mode in enumerate(representatives)}
    full_basis: Dict[int, list[Fraction]] = {}

    for seed_row in seed_rows:
        row = [0] * (2 * len(representatives))
        for seed_index, mode in enumerate(seed_representatives):
            target = 2 * global_index[mode]
            row[target : target + 2] = seed_row[2 * seed_index : 2 * seed_index + 2]
        assert add_independent_rational_row(full_basis, row)

    propagated = 0
    all_steps = list(minimal_signed_scalar_bootstrap()) + list(steps)
    for target, p, q, r in all_steps:
        if target in known:
            continue
        assert q in known and r in known
        z = tuple(int(value.real) for value in cross(q, r))
        jq = tuple(int(value.real) for value in cross(z, q))
        coefficients = triad_coefficient(p, q, r, z, jq, z)
        target_column = 2 * global_index[target]
        target_block = []
        for theta in (1, 1j):
            row = complex_scalar_observation_row(
                (p, q, r), coefficients, theta, representatives
            )
            target_block.append(row[target_column : target_column + 2])
            assert add_independent_rational_row(full_basis, row)
        assert rank(target_block) == 2
        propagated += 1
        known.update((target, neg(target)))

    dimension = 2 * len(representatives)
    assert len(full_basis) == dimension - 1
    assert len(seed_rows) + 2 * propagated == dimension - 1
    assert propagated == len(representatives) - len(seed_representatives)
    return len(representatives), seed_candidates, len(full_basis)


def unoriented(k: Vec) -> Vec:
    """Choose one representative of the pair {k, -k}."""
    for component in k:
        if component:
            return k if component > 0 else neg(k)
    raise ValueError("the zero mode has no orientation")


def check_finite_network_rigidity(box: int = 1) -> Tuple[int, int, int]:
    """Rank of the explicit triad-witness map for all modes in a finite box."""
    vectors = [k for k in product(range(-box, box + 1), repeat=3) if k != (0, 0, 0)]
    representatives = sorted({unoriented(k) for k in vectors})
    index = {k: i for i, k in enumerate(representatives)}
    rows = []
    triads = 0
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            triads += 1
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                coefficients = triad_coefficient(p, q, r, a, b, c)
                row = [0] * len(representatives)
                for k, coefficient in zip((p, q, r), coefficients):
                    row[index[unoriented(k)]] += coefficient
                assert sum(row[index[k]] * norm2(k) for k in representatives) == 0
                if any(row):
                    rows.append(row)
    return rank(rows), len(representatives), triads


def complex_scalar_network_certificate(
    vectors: Iterable[Vec], triads: Iterable[Tuple[Vec, Vec, Vec]]
) -> Tuple[int, int, int, int]:
    """Check the exact ``2M-C`` rank law on a signed triad network.

    ``C`` counts connected components of the signed hypergraph after closing
    the supplied triads under total negation.  The two total phase choices
    realify every complex triad constraint, so the returned rank is the rank
    of the actual real six-mode field evaluations, not a formal complex row
    count.
    """
    signed = set(vectors)
    assert signed and all(neg(k) in signed for k in signed)
    assert (0, 0, 0) not in signed
    representatives = sorted({unoriented(k) for k in signed})
    index = {k: i for i, k in enumerate(representatives)}

    # Normalize ordering and explicitly close the network under reality.  A
    # real six-mode field on tau automatically supplies the conjugate relation
    # on -tau, but putting both hyperedges in the graph makes that orientation
    # fact visible and auditable.
    normalized: set[Tuple[Vec, Vec, Vec]] = set()
    for triad in triads:
        assert len(triad) == 3
        assert add(add(triad[0], triad[1]), triad[2]) == (0, 0, 0)
        assert all(k in signed for k in triad)
        assert cross(triad[0], triad[1]) != (0, 0, 0)
        for sign in (1, -1):
            signed_triad = tuple(
                sorted(
                    (k if sign == 1 else neg(k) for k in triad)
                )
            )
            normalized.add(signed_triad)  # type: ignore[arg-type]
    assert normalized

    parent = {k: k for k in signed}

    def find(k: Vec) -> Vec:
        while parent[k] != k:
            parent[k] = parent[parent[k]]
            k = parent[k]
        return k

    def union(a: Vec, b: Vec) -> None:
        root_a, root_b = find(a), find(b)
        if root_a != root_b:
            parent[root_b] = root_a

    rows: list[list[int]] = []
    for p, q, r in sorted(normalized):
        union(p, q)
        union(p, r)
        for a, b, c in product(
            transverse_basis(p), transverse_basis(q), transverse_basis(r)
        ):
            coefficients = triad_coefficient(p, q, r, a, b, c)
            for theta in (1, 1j):
                row = complex_scalar_observation_row(
                    (p, q, r), coefficients, theta, representatives
                )
                if not any(row):
                    continue
                energy = []
                for k in representatives:
                    energy.extend((norm2(k), 0))
                assert sum(x * y for x, y in zip(row, energy)) == 0
                rows.append(row)

    components = len({find(k) for k in signed})
    actual_rank = rank(rows)
    expected_rank = 2 * len(representatives) - components
    assert actual_rank == expected_rank
    return len(representatives), components, actual_rank, len(rows)


def collect_complex_scalar_network_rows(
    vectors: Iterable[Vec], triads: Iterable[Tuple[Vec, Vec, Vec]]
) -> Tuple[list[Vec], list[list[int]]]:
    """Return all actual phase-separated rows on a signed triad network."""
    signed = set(vectors)
    assert signed and all(neg(k) in signed for k in signed)
    representatives = sorted({unoriented(k) for k in signed})
    normalized: set[Tuple[Vec, Vec, Vec]] = set()
    for triad in triads:
        p, q, r = triad
        assert add(add(p, q), r) == (0, 0, 0)
        assert cross(p, q) != (0, 0, 0)
        assert all(k in signed for k in triad)
        normalized.add(tuple(sorted(triad)))  # type: ignore[arg-type]
        normalized.add(tuple(sorted((neg(p), neg(q), neg(r)))))  # type: ignore[arg-type]

    energy = []
    for k in representatives:
        energy.extend((norm2(k), 0))
    rows: list[list[int]] = []
    for p, q, r in sorted(normalized):
        for a, b, c in product(
            transverse_basis(p), transverse_basis(q), transverse_basis(r)
        ):
            coefficients = triad_coefficient(p, q, r, a, b, c)
            for theta in (1, 1j):
                row = complex_scalar_observation_row(
                    (p, q, r), coefficients, theta, representatives
                )
                if any(row):
                    assert sum(x * y for x, y in zip(row, energy)) == 0
                    rows.append(row)
    return representatives, rows


def minimal_signed_scalar_seed_rows() -> Tuple[list[Vec], int, list[list[int]]]:
    """Select eleven rows on the minimal rank-three signed-connected seed."""
    e1, e2, e3 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    representatives = sorted(
        (
            e1,
            e2,
            e3,
            add(e2, neg(e3)),
            add(e2, e3),
            add(e1, e3),
        )
    )
    vectors = representatives + [neg(k) for k in representatives]
    triads = (
        (neg(add(e1, e3)), e3, e1),
        (neg(add(e2, e3)), e3, e2),
        (neg(e2), e3, add(e2, neg(e3))),
    )
    local_representatives, rows = collect_complex_scalar_network_rows(
        vectors, triads
    )
    assert local_representatives == representatives
    basis: Dict[int, list[Fraction]] = {}
    selected: list[list[int]] = []
    for row in rows:
        if add_independent_rational_row(basis, row):
            selected.append(row)
    assert len(selected) == 11
    return representatives, len(rows), selected


def minimal_signed_scalar_bootstrap() -> Tuple[Tuple[Vec, Vec, Vec, Vec], ...]:
    """Seven unequal-length steps from the six-mode seed to the unit cube."""
    e1, e2, e3 = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    body = add(add(e1, e2), e3)
    decompositions = (
        (body, e1, add(e2, e3)),
        (add(e1, e2), body, neg(e3)),
        (add(add(e1, e2), neg(e3)), e1, add(e2, neg(e3))),
        (add(e1, neg(e3)), add(add(e1, e2), neg(e3)), neg(e2)),
        (add(add(e1, neg(e2)), e3), e1, neg(add(e2, neg(e3)))),
        (add(e1, neg(e2)), add(add(e1, neg(e2)), e3), neg(e3)),
        (add(add(e1, neg(e2)), neg(e3)), add(e1, neg(e2)), neg(e3)),
    )
    return tuple(
        (unoriented(target), neg(target), q, r)
        for target, q, r in decompositions
    )


def check_minimal_signed_scalar_seeds() -> Tuple[int, int, int, int]:
    """Verify the four-mode absolute and six-mode rank-three minima."""
    e1, e2, e3 = (1, 0, 0), (0, 1, 0), (0, 0, 1)

    lambda4 = (e1, e2, add(e1, e2), add(e1, neg(e2)))
    triad_e = (neg(add(e1, e2)), e2, e1)
    triad_f = (neg(e1), e2, add(e1, neg(e2)))
    network4 = complex_scalar_network_certificate(
        lambda4 + tuple(neg(k) for k in lambda4),
        (triad_e, triad_f),
    )
    assert network4[:3] == (4, 1, 7)

    representatives4 = sorted(lambda4)

    def actual_row(
        triad: Tuple[Vec, Vec, Vec],
        a: Vec,
        b: Vec,
        c: Vec,
        theta: complex,
    ) -> list[int]:
        coefficients = triad_coefficient(
            triad[0], triad[1], triad[2], a, b, c
        )
        return primitive_integer_row(
            complex_scalar_observation_row(
                triad, coefficients, theta, representatives4
            )
        )

    rows4 = [
        actual_row(triad_e, (0, 0, 1), (0, 0, -1), (0, -1, 0), 1),
        actual_row(triad_e, (0, 0, 1), (0, 0, -1), (0, -1, 0), 1j),
        actual_row(triad_e, (-1, 1, 0), (0, 0, -1), (0, 0, 1), 1),
        actual_row(triad_e, (-1, 1, 0), (0, 0, -1), (0, 0, 1), 1j),
        actual_row(triad_f, (0, 0, -1), (0, 0, -1), (-1, -1, 0), 1),
        actual_row(triad_f, (0, 0, -1), (1, 0, 0), (0, 0, 1), 1),
        actual_row(triad_f, (0, 0, -1), (1, 0, 0), (0, 0, 1), 1j),
    ]
    expected4 = [
        [0, 1, 0, 0, 0, 1, 0, 1],
        [1, 0, 0, 0, 1, 0, -1, 0],
        [0, -1, 0, 0, 0, 1, 0, 0],
        [-1, 0, 0, 0, 1, 0, 0, 0],
        [0, -1, 0, 0, 0, -1, 0, 0],
        [0, 1, 0, -1, 0, -1, 0, 0],
        [1, 0, -1, 0, 1, 0, 0, 0],
    ]
    assert rows4 == expected4
    assert rank(rows4) == 7
    assert square_determinant(
        [[entry for j, entry in enumerate(row) if j != 2] for row in rows4]
    ) == -4
    laplacian4 = [1, 0, 2, 0, 1, 0, 2, 0]
    assert all(sum(x * y for x, y in zip(row, laplacian4)) == 0 for row in rows4)

    representatives6, candidates6, selected6 = minimal_signed_scalar_seed_rows()
    vectors6 = representatives6 + [neg(k) for k in representatives6]
    triads6 = (
        (neg(add(e1, e3)), e3, e1),
        (neg(add(e2, e3)), e3, e2),
        (neg(e2), e3, add(e2, neg(e3))),
    )
    network6 = complex_scalar_network_certificate(vectors6, triads6)
    assert network6[:3] == (6, 1, 11)

    known = set(vectors6)
    bootstrap = minimal_signed_scalar_bootstrap()
    for target, _p, q, r in bootstrap:
        assert q in known and r in known and target not in known
        assert add(q, r) == target
        assert cross(q, r) != (0, 0, 0)
        assert norm2(q) != norm2(r)
        known.update((target, neg(target)))
    unit_cube = {
        k for k in product((-1, 0, 1), repeat=3) if k != (0, 0, 0)
    }
    assert unit_cube <= known
    return network4[2], len(selected6), candidates6, len(bootstrap)


def check_complex_scalar_network_rank_law() -> Tuple[int, int, int, int]:
    """Exercise both signed connectivity and the orientation counterexample."""
    vectors = [
        k
        for k in product((-1, 0, 1), repeat=3)
        if k != (0, 0, 0)
    ]
    all_triads = []
    signed = set(vectors)
    for p in sorted(signed):
        for q in sorted(signed):
            r = neg(add(p, q))
            if r in signed and p <= q <= r and cross(p, q) != (0, 0, 0):
                all_triads.append((p, q, r))
    connected = complex_scalar_network_certificate(vectors, all_triads)
    assert connected[:3] == (13, 1, 25)

    p, q, r = (1, 0, 0), (0, 1, 0), (-1, -1, 0)
    one_triad = complex_scalar_network_certificate(
        [p, q, r, neg(p), neg(q), neg(r)], [(p, q, r)]
    )
    # The underlying unoriented hypergraph is connected, but its two signed
    # components carry conjugate complex Laplacian ratios independently.
    assert one_triad[:3] == (3, 2, 4)
    return connected


def check_laplacian_triads(box: int = 2) -> Tuple[int, int]:
    vectors = [k for k in product(range(-box, box + 1), repeat=3) if k != (0, 0, 0)]
    checked = 0
    spanning = 0
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors:
                continue
            # One ordering is enough.
            if not (p <= q <= r):
                continue
            coefficient_rows = []
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                coeffs = triad_coefficient(p, q, r, a, b, c)
                assert sum(x * y for x, y in zip(coeffs, map(norm2, (p, q, r)))) == 0
                coefficient_rows.append(coeffs)
                checked += 1
            if cross(p, q) != (0, 0, 0):
                assert rank(coefficient_rows) == 2
                spanning += 1
    return checked, spanning


def check_euler_transport_triads(box: int = 2) -> Tuple[int, int]:
    vectors = [k for k in product(range(-box, box + 1), repeat=3) if k != (0, 0, 0)]
    checked = 0
    spanning = 0
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors or not (p <= q <= r):
                continue
            coefficient_rows = []
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                coefficients = euler_triad_coefficient(p, q, r, a, b, c)
                assert sum(coefficients) == 0
                coefficient_rows.append(coefficients)
                checked += 1
            if cross(p, q) != (0, 0, 0):
                assert rank(coefficient_rows) == 2
                spanning += 1
    return checked, spanning


def check_polynomial_helical_kernel(max_power: int = 3) -> Tuple[int, int]:
    """Finite rank test for a(-Delta)I+b(-Delta)curl, powers 0..max_power."""
    rows = []
    triads = (
        ((1, 0, 0), (0, 1, 0), (-1, -1, 0)),
        ((1, 1, 0), (0, 1, 1), (-1, -2, -1)),
        ((2, 0, 0), (0, 1, 0), (-2, -1, 0)),
    )
    for p, q, r in triads:
        for a, b, c in product(
            transverse_basis(p), transverse_basis(q), transverse_basis(r)
        ):
            for phases in ((1j, 1, 1), (1, 1, 1)):
                modes = triad_modes(p, q, r, a, b, c, phases)
                row = []
                for power in range(max_power + 1):
                    value = helical_multiplier_cubic(
                        modes, lambda k, j=power: norm2(k) ** j, lambda _k: 0
                    )
                    assert abs(value.imag) < 1e-8
                    row.append(round(value.real))
                for power in range(max_power + 1):
                    value = helical_multiplier_cubic(
                        modes, lambda _k: 0, lambda k, j=power: norm2(k) ** j
                    )
                    assert abs(value.imag) < 1e-8
                    row.append(round(value.real))
                if any(row):
                    rows.append(row)
    dimension = 2 * (max_power + 1)
    return rank(rows), dimension


def main() -> None:
    checked, spanning = check_laplacian_triads()
    print(
        f"Laplacian identity: PASS ({checked} polarizations; "
        f"{spanning} non-collinear triads span rank 2)"
    )

    network = check_complex_scalar_network_rank_law()
    print(
        "Signed complex-scalar network law: PASS "
        f"({network[0]} modes; connected C=1 rank {network[2]}; "
        "one-triad orientation split C=2 rank 4)"
    )

    minimal = check_minimal_signed_scalar_seeds()
    print(
        "Minimal signed scalar seeds: PASS "
        f"(four-mode rank {minimal[0]}; six-mode rank {minimal[1]} "
        f"from {minimal[2]} rows; {minimal[3]} unit-cube bootstrap steps)"
    )

    network_rank, network_dimension, network_triads = check_finite_network_rigidity()
    assert network_rank == network_dimension - 1
    print(
        "Finite stability network: PASS "
        f"({network_triads} triads; rank {network_rank}; one-dimensional kernel)"
    )

    multishell = deterministic_multishell_modes()
    for multiplier in (
        lambda eigenvalue: eigenvalue,
        lambda eigenvalue: eigenvalue**2 + 3 * eigenvalue + 2,
        lambda eigenvalue: eigenvalue**3 - 2 * eigenvalue,
    ):
        direct = fourier_cubic(multishell, multiplier)
        reduced = shell_commutator(multishell, multiplier)
        assert abs(direct - reduced) < 1e-8
    print("Spectral commutator identity: PASS (direct multishell convolution)")

    nonradial_symbols = (
        (lambda k: 2 * k[0] ** 2 + 3 * k[1] ** 2 + 5 * k[2] ** 2, (1, 0, 0), (0, 1, 0)),
        (lambda k: norm2(k) ** 2, (1, 0, 0), (1, 1, 0)),
        (lambda k: norm2(k) + k[0] ** 2 * k[1] ** 2 + 7, (1, 0, 0), (1, 1, 0)),
    )
    for symbol, p, q in nonradial_symbols:
        witness_modes = constructive_rigidity_witness(symbol, p, q)
        direct = fourier_cubic_symbol(witness_modes, symbol)
        reduced = mode_commutator(witness_modes, symbol)
        assert abs(direct) > 1e-9
        assert abs(direct - reduced) < 1e-8
    print("Universal multiplier rigidity: PASS (constructive non-radial witnesses)")

    complex_scalar_symbols = (
        (lambda k: 1j * k[0], (1, 0, 0), (0, 1, 0)),
        (lambda k: norm2(k) + 1j * k[0], (1, 0, 0), (1, 1, 0)),
        (
            lambda k: 2 * k[0] ** 2 + 3 * k[1] ** 2 + 5 * k[2] ** 2
            + 1j * (k[0] + 2 * k[1] ** 3),
            (1, 0, 0),
            (1, 1, 0),
        ),
    )
    for symbol, p, q in complex_scalar_symbols:
        for k in (p, q, neg(add(p, q))):
            assert symbol(neg(k)) == symbol(k).conjugate()
        witness_modes = constructive_complex_scalar_witness(symbol, p, q)
        assert abs(fourier_cubic_symbol(witness_modes, symbol)) > 1e-9
    print(
        "Complex scalar rigidity: PASS "
        "(reality-compatible odd and anisotropic symbols detected)"
    )
    scalar_modes, scalar_rows, scalar_rank = check_complex_scalar_seed_certificate()
    assert scalar_rank == 2 * scalar_modes - 1
    print(
        "Complex scalar seed certificate: PASS "
        f"({scalar_modes} unoriented modes; {scalar_rows} tested rows; "
        f"rank {scalar_rank}/{2 * scalar_modes})"
    )
    scalar_modes, scalar_seed_rows, scalar_rank = check_scalar_sparse_certificate()
    assert scalar_rank == scalar_modes - 1
    print(
        "Optimal scalar sparse certificate: PASS "
        f"({scalar_modes} unoriented modes; 6 selected from "
        f"{scalar_seed_rows} seed candidates; "
        f"rank {scalar_rank}/{scalar_modes})"
    )
    complex_modes, complex_seed_rows, complex_rank = (
        check_complex_scalar_sparse_certificate()
    )
    assert complex_rank == 2 * complex_modes - 1
    print(
        "Optimal complex-scalar sparse certificate: PASS "
        f"({complex_modes} unoriented modes; 11 selected from "
        f"{complex_seed_rows} minimal six-mode seed candidates; "
        f"rank {complex_rank}/{2 * complex_modes})"
    )

    euler_checked, euler_spanning = check_euler_transport_triads()
    constant = lambda _k: 1
    assert abs(euler_transport_cubic(multishell, constant)) < 1e-8
    bad_transport_symbols = (
        (lambda k: norm2(k), (1, 0, 0), (1, 1, 0)),
        (lambda k: k[0] ** 2 + 3 * k[1] ** 2 + 2, (1, 0, 0), (0, 1, 0)),
    )
    for symbol, p, q in bad_transport_symbols:
        w_modes = constructive_transport_witness(symbol, p, q)
        transport = euler_transport_cubic(w_modes, symbol)
        assert abs(transport) > 1e-9
        u_modes = inverse_curl(w_modes)
        helical_defect = helical_multiplier_cubic(u_modes, lambda _k: 0, symbol)
        assert abs(helical_defect + transport) < 1e-8
    print(
        "Euler transport rigidity: PASS "
        f"({euler_checked} polarizations; {euler_spanning} rank-2 triads; "
        "constructive nonconstant witnesses)"
    )

    for c, d in ((1, 0), (0, 1), (2, -1), (3, 2)):
        defect = helical_multiplier_cubic(
            multishell, lambda k, value=c: value * norm2(k), lambda _k, value=d: value
        )
        assert abs(defect) < 1e-8
    print("Helical two-generator family: PASS (span{-Delta, curl})")

    a_symbol = lambda k: norm2(k) ** 2 + 2 * k[0] * k[1]
    b_symbol = lambda k: 3 + k[2] ** 2
    w_modes = {k: vorticity(k, amplitude) for k, amplitude in multishell.items()}
    transformed_modes = {
        k: tuple(
            a_symbol(k) * multishell[k][i] + b_symbol(k) * w_modes[k][i]
            for i in range(3)
        )
        for k in multishell
    }
    direct_pullback = helical_multiplier_cubic(multishell, a_symbol, b_symbol)
    euler_pullback = -euler_cubic_with_test(transformed_modes, w_modes)
    assert abs(direct_pullback - euler_pullback) < 1e-8
    print("Euler pullback equivalence: PASS (general non-radial helical symbol)")

    helical_rank, helical_dimension = check_polynomial_helical_kernel()
    assert helical_rank == helical_dimension - 2
    print(
        "Helical polynomial classification: PASS "
        f"(rank {helical_rank}; kernel span{{-Delta, curl}})"
    )

    witnesses = [
        ((-1, -1, 0), (0, 1, 0), (1, 0, 0), (0, 0, 1), (0, 0, -1), (0, -1, 0)),
        ((-1, 0, -1), (0, 0, 1), (1, 0, 0), (0, -1, 0), (0, 1, 0), (0, 0, 1)),
        ((0, -1, -1), (0, 0, 1), (0, 1, 0), (1, 0, 0), (0, 1, 0), (1, 0, 0)),
        ((-1, -1, 0), (0, 1, 0), (1, 0, 0), (-1, 1, 0), (0, 0, -1), (0, 0, 1)),
        ((-1, 0, -1), (0, 0, 1), (1, 0, 0), (1, 0, -1), (0, 1, 0), (0, -1, 0)),
    ]
    rows = [anisotropic_constraint(*witness) for witness in witnesses]
    expected = [
        (0, 0, 0, -1, 0, 0),
        (0, 0, 0, 0, 1, 0),
        (0, 0, 0, 0, 0, -1),
        (1, -1, 0, 0, 0, 0),
        (-1, 0, 1, 0, 0, 0),
    ]
    assert rows == expected
    assert rank(rows) == 5
    assert all(sum(row[i] for i in range(3)) == 0 for row in rows)
    test_matrix = (2, -3, 5, 7, -11, 13)
    for witness in witnesses:
        p, q, r, a, b, c = witness
        coefficients = triad_coefficient(*witness)
        reduced = 2 * sum(
            coefficients[i] * quadratic_symbol(k, test_matrix)
            for i, k in enumerate((p, q, r))
        )
        # fourier_cubic accepts radial multipliers.  Evaluate the same full
        # convolution here with the anisotropic symbol on the S mode.
        direct = 0j
        modes = triad_modes(*witness)
        for kp, kq, kr in product(modes, repeat=3):
            if add(add(kp, kq), kr) == (0, 0, 0):
                direct += quadratic_symbol(kp, test_matrix) * contraction(
                    strain(kp, modes[kp]),
                    vorticity(kq, modes[kq]),
                    vorticity(kr, modes[kr]),
                )
        assert abs(direct.imag) < 1e-9
        assert abs(direct.real - reduced) < 1e-9
    print("Anisotropic rigidity witnesses: PASS (rank 5; nullspace span{I})")

    for n in (2, 3, 5):
        shell = n * n + 1
        modes = explicit_modes(n)
        for alpha in (0, 1, 2, 3):
            actual = fourier_cubic(modes, lambda eigenvalue, a=alpha: eigenvalue**a)
            commutator = shell_commutator(
                modes, lambda eigenvalue, a=alpha: eigenvalue**a
            )
            predicted = 4 * (shell**alpha - shell)
            assert abs(actual.imag) < 1e-9
            assert abs(actual.real - predicted) < 1e-9
            assert abs(commutator - actual) < 1e-9
        print(
            f"Fractional witness n={n}: PASS "
            f"(alpha=0,1,2,3; cancelling exponent alpha=1)"
        )

    print("All exact structural checks passed.")


if __name__ == "__main__":
    main()
