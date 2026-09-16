#!/usr/bin/env python3
"""Independent replay of the seven-mode unrestricted seed certificate.

This audit deliberately imports none of the project's Fourier row builders or
row reducers.  It groups the nonlinear convolution by recipient wavevector,
then probes every real and imaginary matrix coordinate.  All calculations use
Gaussian rationals represented by pairs of ``Fraction`` objects.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Dict, List, Sequence, Tuple


Vec = Tuple[int, int, int]
Gaussian = Tuple[Fraction, Fraction]
GVec = Tuple[Gaussian, Gaussian, Gaussian]

ZERO: Gaussian = (Fraction(0), Fraction(0))
ONE: Gaussian = (Fraction(1), Fraction(0))
IMAGINARY_UNIT: Gaussian = (Fraction(0), Fraction(1))
PRIMES = (1_000_003, 1_000_000_007)

SEED_REPRESENTATIVES: Tuple[Vec, ...] = tuple(
    sorted(
        (
            (1, 0, 0),
            (0, 1, 0),
            (0, 0, 1),
            (1, 1, 0),
            (1, 0, 1),
            (0, 1, 1),
            (1, 1, 1),
        )
    )
)

EXPECTED_SELECTED_ROWS = (
    0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 40, 41, 64, 65, 72, 73, 80, 81,
    88, 89, 96, 97, 104, 105, 128, 129, 144, 145, 152, 153, 160, 161, 176,
    177, 184, 185, 256, 257, 264, 265, 272, 273, 288, 289, 296, 297, 304,
    305, 376, 377, 384, 385, 393, 400,
)
EXPECTED_COLUMNS = tuple(range(53)) + (55,)
EXPECTED_DETERMINANTS = (190_194, 891_695_525)


def cadd(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] + b[0], a[1] + b[1]


def cmul(a: Gaussian, b: Gaussian) -> Gaussian:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def cconjugate(a: Gaussian) -> Gaussian:
    return a[0], -a[1]


def cint(value: int) -> Gaussian:
    return Fraction(value), Fraction(0)


def vadd(a: Vec, b: Vec) -> Vec:
    return tuple(a[j] + b[j] for j in range(3))  # type: ignore[return-value]


def vneg(a: Vec) -> Vec:
    return tuple(-a[j] for j in range(3))  # type: ignore[return-value]


def vdot(a: Sequence[Gaussian], b: Sequence[int] | Sequence[Gaussian]) -> Gaussian:
    result = ZERO
    for left, right in zip(a, b):
        right_gaussian = right if isinstance(right, tuple) else cint(right)
        result = cadd(result, cmul(left, right_gaussian))
    return result


def cross(a: Vec, b: Vec) -> Vec:
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def dot(a: Vec, b: Vec) -> int:
    return sum(a[j] * b[j] for j in range(3))


def norm2(k: Vec) -> int:
    return dot(k, k)


def transverse_basis(k: Vec) -> Tuple[Vec, Vec]:
    result: List[Vec] = []
    for coordinate in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        candidate = cross(k, coordinate)
        if candidate == (0, 0, 0):
            continue
        if result and cross(result[0], candidate) == (0, 0, 0):
            continue
        result.append(candidate)
        if len(result) == 2:
            return result[0], result[1]
    raise ValueError(k)


def representative(k: Vec) -> Vec:
    for component in k:
        if component:
            return k if component > 0 else vneg(k)
    raise ValueError("the zero mode has no representative")


def frame(k: Vec) -> Tuple[Vec, Vec]:
    first = transverse_basis(k)[0]
    return first, cross(k, first)


def coordinates(vector: Sequence[Gaussian], basis: Tuple[Vec, Vec]) -> Tuple[Gaussian, Gaussian]:
    return tuple(
        (vdot(vector, element)[0] / norm2(element),
         vdot(vector, element)[1] / norm2(element))
        for element in basis
    )  # type: ignore[return-value]


def seed_vectors() -> List[Vec]:
    return sorted(
        set(SEED_REPRESENTATIVES)
        | {vneg(k) for k in SEED_REPRESENTATIVES}
    )


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


def independent_convolution_row(
    modes: Dict[Vec, GVec], representatives: Sequence[Vec]
) -> List[Fraction]:
    """Group N[t] first, then pair N[-k] with each recipient amplitude."""
    nonlinear: Dict[Vec, GVec] = {}
    for q, amplitude_q in modes.items():
        for r, amplitude_r in modes.items():
            target = vadd(q, r)
            factor = cmul(IMAGINARY_UNIT, vdot(amplitude_q, r))
            term = tuple(cmul(factor, x) for x in amplitude_r)
            old = nonlinear.get(target, (ZERO, ZERO, ZERO))
            nonlinear[target] = tuple(
                cadd(old[j], term[j]) for j in range(3)
            )  # type: ignore[assignment]

    index = {k: i for i, k in enumerate(representatives)}
    row = [Fraction(0)] * (8 * len(representatives))
    for k, amplitude in modes.items():
        recipient = nonlinear.get(vneg(k))
        if recipient is None:
            continue
        mode = representative(k)
        orientation = 1 if mode == k else -1
        x = coordinates(amplitude, frame(mode))
        y = coordinates(recipient, frame(mode))
        start = 8 * index[mode]
        for matrix_index, (i, j) in enumerate(((0, 0), (0, 1), (1, 0), (1, 1))):
            coefficient = cmul(y[i], x[j])
            row[start + 2 * matrix_index] += coefficient[0]
            row[start + 2 * matrix_index + 1] -= orientation * coefficient[1]
    return row


def enumerate_rows() -> List[List[Fraction]]:
    vectors = seed_vectors()
    vector_set = set(vectors)
    phases = tuple(product((ONE, IMAGINARY_UNIT), repeat=3))
    rows: List[List[Fraction]] = []
    for p in vectors:
        for q in vectors:
            r = vneg(vadd(p, q))
            if (
                r not in vector_set
                or not (p <= q <= r)
                or cross(p, q) == (0, 0, 0)
            ):
                continue
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                for phase in phases:
                    row = independent_convolution_row(
                        real_triad_field(p, q, r, a, b, c, phase),
                        SEED_REPRESENTATIVES,
                    )
                    if any(row):
                        rows.append(row)
    return rows


def add_basis(basis: Dict[int, List[Fraction]], source: Sequence[Fraction]) -> bool:
    row = list(source)
    for pivot in sorted(basis):
        if row[pivot]:
            factor = row[pivot]
            row = [x - factor * y for x, y in zip(row, basis[pivot])]
    pivot = next((j for j, value in enumerate(row) if value), None)
    if pivot is None:
        return False
    factor = row[pivot]
    basis[pivot] = [value / factor for value in row]
    return True


def determinant_mod(
    rows: Sequence[Sequence[Fraction]], columns: Sequence[int], prime: int
) -> int:
    matrix = [
        [
            row[column].numerator
            * pow(row[column].denominator, -1, prime)
            % prime
            for column in columns
        ]
        for row in rows
    ]
    determinant = 1
    for column in range(len(matrix)):
        pivot = next(
            (row for row in range(column, len(matrix)) if matrix[row][column]),
            None,
        )
        if pivot is None:
            return 0
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            determinant = -determinant
        pivot_value = matrix[column][column]
        determinant = determinant * pivot_value % prime
        inverse = pow(pivot_value, -1, prime)
        matrix[column] = [value * inverse % prime for value in matrix[column]]
        for row in range(column + 1, len(matrix)):
            if matrix[row][column]:
                factor = matrix[row][column]
                matrix[row] = [
                    (x - factor * y) % prime
                    for x, y in zip(matrix[row], matrix[column])
                ]
    return determinant % prime


def kernel_vectors() -> Tuple[List[int], List[int]]:
    energy: List[int] = []
    helicity: List[int] = []
    for k in SEED_REPRESENTATIVES:
        first, second = frame(k)
        energy.extend((norm2(first), 0, 0, 0, 0, 0, norm2(second), 0))
        scale = norm2(k) * norm2(first)
        helicity.extend((0, 0, 0, -scale, 0, scale, 0, 0))
    return energy, helicity


def main() -> None:
    rows = enumerate_rows()
    basis: Dict[int, List[Fraction]] = {}
    selected: List[int] = []
    for index, row in enumerate(rows):
        if add_basis(basis, row):
            selected.append(index)

    columns = tuple(sorted(basis))
    determinants = tuple(
        determinant_mod([rows[index] for index in selected], columns, prime)
        for prime in PRIMES
    )
    denominators = {value.denominator for row in rows for value in row}
    energy, helicity = kernel_vectors()

    assert len(rows) == 720
    assert len(basis) == 54
    assert tuple(selected) == EXPECTED_SELECTED_ROWS
    assert columns == EXPECTED_COLUMNS
    assert determinants == EXPECTED_DETERMINANTS
    assert denominators == {1, 2, 3, 6}
    assert all(sum(x * y for x, y in zip(row, energy)) == 0 for row in rows)
    assert all(sum(x * y for x, y in zip(row, helicity)) == 0 for row in rows)

    print(
        "Independent unrestricted seed replay: PASS "
        "(720 rows; rank 54/56; exact energy--helicity kernel)"
    )
    print(f"nonzero 54x54 minor determinants modulo {PRIMES}: {determinants}")
    print(f"row denominators: {sorted(denominators)}")


if __name__ == "__main__":
    main()
