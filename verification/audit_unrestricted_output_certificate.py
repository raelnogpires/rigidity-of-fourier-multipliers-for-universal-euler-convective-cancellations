#!/usr/bin/env python3
"""Independent convolution-first audit of the unrestricted-output theorem.

This file intentionally imports none of the project's Fourier row builders or
row reducers.  It verifies the 13-mode, 156-parameter seed certificate for
symbols R(k): k^perp_C -> C^3 and checks the explicit 12-dimensional kernel.
All arithmetic is integer or rational, and rank is computed over two primes.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from itertools import product
from typing import Dict, Iterable, List, Sequence, Tuple

Vec = Tuple[int, int, int]
Gaussian = Tuple[Fraction, Fraction]
GVec = Tuple[Gaussian, Gaussian, Gaussian]
Matrix = Tuple[Tuple[int, int, int], Tuple[int, int, int], Tuple[int, int, int]]

ZERO: Gaussian = (Fraction(0), Fraction(0))
ONE: Gaussian = (Fraction(1), Fraction(0))
IMAGINARY_UNIT: Gaussian = (Fraction(0), Fraction(1))
PRIMES = (1_000_003, 1_000_000_007)


def cadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] + b[0], a[1] + b[1]


def cmul(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def cconjugate(a: Gaussian) -> Gaussian:
    return a[0], -a[1]


def cint(value: int) -> Gaussian:
    return Fraction(value), Fraction(0)


def vadd(a: Vec, b: Vec) -> Vec:
    return tuple(a[i] + b[i] for i in range(3))  # type: ignore[return-value]


def vneg(a: Vec) -> Vec:
    return tuple(-x for x in a)  # type: ignore[return-value]


def cross(a: Sequence[int], b: Sequence[int]) -> Vec:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def idot(a: Sequence[int], b: Sequence[int]) -> int:
    return sum(a[i] * b[i] for i in range(3))


def gdot(a: Sequence[Gaussian], b: Sequence[int]) -> Gaussian:
    result = ZERO
    for value, integer in zip(a, b):
        result = cadd(result, cmul(value, cint(integer)))
    return result


def representative(k: Vec) -> Vec:
    for value in k:
        if value:
            return k if value > 0 else vneg(k)
    raise ValueError("zero mode has no representative")


def transverse_basis(k: Vec) -> Tuple[Vec, Vec]:
    candidates = [cross(k, e) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    result: List[Vec] = []
    for candidate in candidates:
        if candidate == (0, 0, 0):
            continue
        if result and cross(result[0], candidate) == (0, 0, 0):
            continue
        result.append(candidate)
        if len(result) == 2:
            return result[0], result[1]
    raise ValueError(k)


def frame(k: Vec) -> Tuple[Vec, Vec]:
    first = transverse_basis(k)[0]
    second = cross(k, first)
    assert idot(first, second) == 0
    return first, second


def coordinates(vector: Sequence[Gaussian], basis: Tuple[Vec, Vec]) -> Tuple[Gaussian, Gaussian]:
    return tuple(
        (lambda value, denominator: (value[0] / denominator, value[1] / denominator))(
            gdot(vector, element), idot(element, element)
        )
        for element in basis
    )  # type: ignore[return-value]


def seed_vectors() -> List[Vec]:
    return [
        (x, y, z)
        for x, y, z in product(range(-1, 2), repeat=3)
        if (x, y, z) != (0, 0, 0)
    ]


def seed_representatives() -> List[Vec]:
    return sorted({representative(k) for k in seed_vectors()})


def real_triad_field(
    p: Vec,
    q: Vec,
    r: Vec,
    a: Vec,
    b: Vec,
    c: Vec,
    phases: Tuple[Gaussian, Gaussian, Gaussian],
) -> Dict[Vec, GVec]:
    result: Dict[Vec, GVec] = {}
    for k, polarization, phase in zip((p, q, r), (a, b, c), phases):
        amplitude = tuple(cmul(phase, cint(x)) for x in polarization)
        result[k] = amplitude  # type: ignore[assignment]
        result[vneg(k)] = tuple(cconjugate(x) for x in amplitude)  # type: ignore[assignment]
    return result


def convolution_row(modes: Dict[Vec, GVec], representatives: Sequence[Vec]) -> List[Fraction]:
    """Build (w dot grad)w by recipient mode before pairing with Rw."""
    nonlinear: Dict[Vec, GVec] = {}
    for q, amplitude_q in modes.items():
        for r, amplitude_r in modes.items():
            target = vadd(q, r)
            factor = cmul(IMAGINARY_UNIT, gdot(amplitude_q, r))
            term = tuple(cmul(factor, value) for value in amplitude_r)
            previous = nonlinear.get(target, (ZERO, ZERO, ZERO))
            nonlinear[target] = tuple(
                cadd(previous[i], term[i]) for i in range(3)
            )  # type: ignore[assignment]

    index = {k: i for i, k in enumerate(representatives)}
    row = [Fraction(0)] * (12 * len(representatives))
    for k, amplitude in modes.items():
        recipient = nonlinear.get(vneg(k))
        if recipient is None:
            continue
        mode = representative(k)
        orientation = 1 if k == mode else -1
        x = coordinates(amplitude, frame(mode))
        start = 12 * index[mode]
        for output_index in range(3):
            for input_index in range(2):
                coefficient = cmul(recipient[output_index], x[input_index])
                matrix_index = 2 * output_index + input_index
                row[start + 2 * matrix_index] += coefficient[0]
                row[start + 2 * matrix_index + 1] -= orientation * coefficient[1]
    return row


def enumerate_rows() -> List[List[Fraction]]:
    vectors = seed_vectors()
    vector_set = set(vectors)
    representatives = seed_representatives()
    phases = ((ONE, ONE, ONE), (IMAGINARY_UNIT, ONE, ONE))
    rows: List[List[Fraction]] = []
    for p in vectors:
        for q in vectors:
            r = vneg(vadd(p, q))
            if r not in vector_set or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                for phase in phases:
                    row = convolution_row(
                        real_triad_field(p, q, r, a, b, c, phase), representatives
                    )
                    if any(row):
                        rows.append(row)
    return rows


def reduce_mod(basis: Dict[int, List[int]], source: Sequence[Fraction], prime: int) -> bool:
    row = [
        value.numerator * pow(value.denominator, -1, prime) % prime
        for value in source
    ]
    for pivot in sorted(basis):
        if row[pivot]:
            factor = row[pivot]
            row = [(x - factor * y) % prime for x, y in zip(row, basis[pivot])]
    pivot = next((i for i, value in enumerate(row) if value), None)
    if pivot is None:
        return False
    inverse = pow(row[pivot], -1, prime)
    basis[pivot] = [(value * inverse) % prime for value in row]
    return True


def symmetric_basis() -> List[Matrix]:
    result: List[Matrix] = []
    for i in range(3):
        for j in range(i, 3):
            matrix = [[0, 0, 0] for _ in range(3)]
            matrix[i][j] = matrix[j][i] = 1
            result.append(tuple(tuple(row) for row in matrix))  # type: ignore[arg-type]
    return result


def matvec(matrix: Matrix, vector: Vec) -> Vec:
    return tuple(sum(matrix[i][j] * vector[j] for j in range(3)) for i in range(3))  # type: ignore[return-value]


def kernel_vector(zeroth: Matrix | None, first: Matrix | None) -> List[int]:
    result: List[int] = []
    for k in seed_representatives():
        for output_index in range(3):
            for input_vector in frame(k):
                real = 0 if zeroth is None else matvec(zeroth, input_vector)[output_index]
                if first is None:
                    imaginary = 0
                else:
                    left = matvec(first, cross(k, input_vector))
                    right = cross(k, matvec(first, input_vector))
                    imaginary = left[output_index] + right[output_index]
                result.extend((real, imaginary))
    return result


def rational_rank(rows: Iterable[Sequence[int]]) -> int:
    basis: Dict[int, List[Fraction]] = {}
    for source in rows:
        row = [Fraction(value) for value in source]
        for pivot in sorted(basis):
            if row[pivot]:
                factor = row[pivot]
                row = [x - factor * y for x, y in zip(row, basis[pivot])]
        pivot = next((i for i, value in enumerate(row) if value), None)
        if pivot is None:
            continue
        factor = row[pivot]
        basis[pivot] = [value / factor for value in row]
    return len(basis)


def row_digest(rows: Sequence[Sequence[Fraction]]) -> str:
    payload = "\n".join(
        ",".join(f"{value.numerator}/{value.denominator}" for value in row)
        for row in rows
    )
    return sha256(payload.encode("ascii")).hexdigest()


def main() -> None:
    rows = enumerate_rows()
    expected_digest = "a4fc3b45a6fc94defd38d992dbbe27f4413254b3af307e41d1c7e25839e9c30d"
    candidates = [kernel_vector(matrix, None) for matrix in symmetric_basis()]
    candidates += [kernel_vector(None, matrix) for matrix in symmetric_basis()]
    assert len(rows) == 680
    assert len(rows[0]) == 156
    assert row_digest(rows) == expected_digest
    assert rational_rank(candidates) == 12
    assert all(
        sum(coefficient * parameter for coefficient, parameter in zip(row, candidate)) == 0
        for row in rows
        for candidate in candidates
    )
    denominators = {value.denominator for row in rows for value in row}
    ranks = []
    for prime in PRIMES:
        assert all(denominator % prime for denominator in denominators)
        basis: Dict[int, List[int]] = {}
        for row in rows:
            reduce_mod(basis, row, prime)
        ranks.append(len(basis))
    assert tuple(ranks) == (144, 144)
    print("Independent unrestricted-output audit: PASS")
    print("rows: 680; parameters: 156; modular ranks: 144, 144; nullity: 12")
    print(f"row denominators: {sorted(denominators)}")
    print(f"row SHA-256: {row_digest(rows)}")


if __name__ == "__main__":
    main()
