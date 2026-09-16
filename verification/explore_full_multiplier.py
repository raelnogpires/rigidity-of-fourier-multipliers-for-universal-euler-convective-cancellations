#!/usr/bin/env python3
"""Explore quadratic Euler invariants for fully general Fourier multipliers.

This is a finite-dimensional exact-rank experiment.  At each unoriented mode,
the symbol is an arbitrary Hermitian operator on the two-dimensional
divergence-free plane (four real parameters).  Cubic Euler cancellation is
imposed on every non-collinear triad in a finite lattice box.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Dict, List, Sequence, Tuple

from verify_laplacian_rigidity import (
    Vec,
    add,
    cross,
    dot,
    neg,
    norm2,
    transverse_basis,
    unoriented,
)

Gaussian = Tuple[Fraction, Fraction]
GVec = Tuple[Gaussian, Gaussian, Gaussian]
ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))
IMAGINARY_UNIT = (Fraction(0), Fraction(1))


def gaussian(value: int | Fraction) -> Gaussian:
    return Fraction(value), Fraction(0)


def gadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] + b[0], a[1] + b[1]


def gsub(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] - b[0], a[1] - b[1]


def gmul(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def gdivide(a: Gaussian, denominator: int) -> Gaussian:
    return a[0] / denominator, a[1] / denominator


def gconjugate(a: Gaussian) -> Gaussian:
    return a[0], -a[1]


def gdot(a: Sequence[Gaussian], b: Sequence[int] | Sequence[Gaussian]) -> Gaussian:
    result = ZERO
    for left, right in zip(a, b):
        right_gaussian = right if isinstance(right, tuple) else gaussian(right)
        result = gadd(result, gmul(left, right_gaussian))
    return result


def exact_triad_modes(
    p: Vec,
    q: Vec,
    r: Vec,
    a: Vec,
    b: Vec,
    c: Vec,
    phases: Tuple[Gaussian, Gaussian, Gaussian],
) -> Dict[Vec, GVec]:
    modes: Dict[Vec, GVec] = {}
    for k, polarization, phase in zip((p, q, r), (a, b, c), phases):
        amplitude = tuple(gmul(phase, gaussian(x)) for x in polarization)
        modes[k] = amplitude  # type: ignore[assignment]
        modes[neg(k)] = tuple(gconjugate(x) for x in amplitude)  # type: ignore[assignment]
    return modes


def orthogonal_frame(k: Vec) -> Tuple[Vec, Vec]:
    first = transverse_basis(k)[0]
    second_complex = cross(k, first)
    second = tuple(int(x.real) for x in second_complex)
    assert dot(first, second) == 0
    return first, second  # type: ignore[return-value]


def coordinates(vector: Sequence[Gaussian], frame: Tuple[Vec, Vec]) -> Tuple[Gaussian, Gaussian]:
    return tuple(gdivide(gdot(vector, e), norm2(e)) for e in frame)  # type: ignore[return-value]


def invariant_row(
    modes: Dict[Vec, GVec], representatives: Sequence[Vec]
) -> List[Fraction]:
    """Coefficients of <Rw,(w dot grad)w> for general Hermitian R(k)."""
    index = {k: i for i, k in enumerate(representatives)}
    row = [ZERO] * (4 * len(representatives))
    for p, q, r in product(modes, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        representative = unoriented(p)
        base = 4 * index[representative]
        frame = orthogonal_frame(representative)
        x1, x2 = coordinates(modes[p], frame)
        derivative = gmul(IMAGINARY_UNIT, gdot(modes[q], r))
        nonlinear = tuple(gmul(derivative, component) for component in modes[r])
        y1, y2 = coordinates(nonlinear, frame)
        orientation = 1 if p == representative else -1
        row[base] = gadd(row[base], gmul(y1, x1))
        row[base + 1] = gadd(row[base + 1], gmul(y2, x2))
        row[base + 2] = gadd(
            row[base + 2], gadd(gmul(y1, x2), gmul(y2, x1))
        )
        skew = gmul(IMAGINARY_UNIT, gsub(gmul(y1, x2), gmul(y2, x1)))
        if orientation < 0:
            skew = (-skew[0], -skew[1])
        row[base + 3] = gadd(row[base + 3], skew)

    assert all(value[1] == 0 for value in row)
    return [value[0] for value in row]


def energy_vector(representatives: Sequence[Vec]) -> List[int]:
    result = []
    for k in representatives:
        e1, e2 = orthogonal_frame(k)
        result.extend((norm2(e1), norm2(e2), 0, 0))
    return result


def helicity_vector(representatives: Sequence[Vec]) -> List[int]:
    result = []
    for k in representatives:
        e1, _e2 = orthogonal_frame(k)
        # e1 dot (i k cross e2) = -i |k|^2 |e1|^2.
        result.extend((0, 0, 0, -norm2(k) * norm2(e1)))
    return result


def add_independent_row(
    basis: Dict[int, List[Fraction]], source: Sequence[Fraction]
) -> bool:
    """Incremental exact row reduction; return whether rank increases."""
    row = list(source)
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


def analyze_vectors(vectors: Sequence[Vec]) -> Tuple[int, int, int, int]:
    representatives = sorted({unoriented(k) for k in vectors})
    energy = energy_vector(representatives)
    helicity = helicity_vector(representatives)
    basis: Dict[int, List[Fraction]] = {}
    equation_count = 0
    triads = 0
    phases = tuple(product((ONE, IMAGINARY_UNIT), repeat=3))
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            triads += 1
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                for phase in phases:
                    row = invariant_row(
                        exact_triad_modes(p, q, r, a, b, c, phase), representatives
                    )
                    if any(row):
                        equation_count += 1
                        assert sum(x * y for x, y in zip(row, energy)) == 0
                        assert sum(x * y for x, y in zip(row, helicity)) == 0
                        add_independent_row(basis, row)

    dimension = 4 * len(representatives)
    return len(basis), dimension, triads, equation_count


def analyze(box: int = 1) -> Tuple[int, int, int, int]:
    vectors = [k for k in product(range(-box, box + 1), repeat=3) if k != (0, 0, 0)]
    return analyze_vectors(vectors)


def generator_box(generators: Tuple[Vec, Vec, Vec]) -> List[Vec]:
    vectors = []
    for coefficients in product((-1, 0, 1), repeat=3):
        vector = tuple(
            sum(coefficients[j] * generators[j][i] for j in range(3))
            for i in range(3)
        )
        if vector != (0, 0, 0):
            vectors.append(vector)  # type: ignore[arg-type]
    assert len(set(vectors)) == 26
    return vectors


def main() -> None:
    generator_sets = (
        ((1, 0, 0), (0, 1, 0), (0, 0, 1)),
        ((2, 1, 0), (0, 1, 1), (1, 0, 2)),
        ((3, -1, 1), (1, 2, 0), (0, 1, 2)),
    )
    for generators in generator_sets:
        matrix_rank, dimension, triads, equations = analyze_vectors(
            generator_box(generators)
        )
        assert matrix_rank == dimension - 2
        print(
            f"generators={generators}: {dimension} variables, {triads} triads, "
            f"{equations} equations, rank {matrix_rank}, "
            f"nullity {dimension - matrix_rank}"
        )


if __name__ == "__main__":
    main()
