#!/usr/bin/env python3
"""Independent SageMath reproduction of the 56->54 and 156->144 seeds.

Run from the conda-forge SageMath environment with

    conda run -n sage python verification/reproduce_seed_certificates_sage.py

Traditional SageMath distributions also support

    sage -python verification/reproduce_seed_certificates_sage.py

The program imports no project verifier.  It reconstructs the Fourier rows
from the convolution, checks the displayed kernel generators, and verifies
the fixed modular minors recorded in the proof.
"""

from __future__ import annotations

from hashlib import sha256
from itertools import product

from sage.all import GF, QQ, matrix


ZERO = (QQ(0), QQ(0))
ONE = (QQ(1), QQ(0))
I = (QQ(0), QQ(1))
PRIMES = (1_000_003, 1_000_000_007)

SOLENOIDAL_ROWS = (
    0, 1, 8, 9, 16, 17, 24, 25, 32, 33, 40, 41, 64, 65, 72, 73, 80, 81,
    88, 89, 96, 97, 104, 105, 128, 129, 144, 145, 152, 153, 160, 161, 176,
    177, 184, 185, 256, 257, 264, 265, 272, 273, 288, 289, 296, 297, 304,
    305, 376, 377, 384, 385, 393, 400,
)
SOLENOIDAL_COLUMNS = tuple(range(53)) + (55,)
SOLENOIDAL_RESIDUES = (190_194, 891_695_525)

UNRESTRICTED_ROWS = (
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 27, 32, 33, 36, 37, 38, 39, 40, 41, 44, 45, 46, 47,
    64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 80, 81, 82, 83, 84, 85,
    86, 87, 88, 89, 90, 91, 96, 97, 98, 99, 100, 101, 104, 105, 106, 107,
    108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121,
    142, 143, 146, 147, 148, 149, 150, 151, 154, 155, 156, 157, 158, 159,
    160, 161, 163, 206, 207, 208, 209, 212, 213, 220, 221, 222, 223, 224,
    225, 226, 227, 230, 236, 237, 238, 239, 240, 241, 242, 243, 247, 326,
    327, 328, 329, 344, 345, 346, 347, 356, 357, 358, 359, 360, 361, 362,
    363, 434, 435, 436, 437,
)
UNRESTRICTED_COLUMNS = tuple(range(119)) + (
    120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133,
    134, 135, 136, 138, 139, 141, 142, 144, 145, 147, 149,
)
UNRESTRICTED_RESIDUES = (272_144, 290_707_620)
UNRESTRICTED_DIGEST = (
    "a4fc3b45a6fc94defd38d992dbbe27f4413254b3af307e41d1c7e25839e9c30d"
)


def cadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def cmul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def cconjugate(a):
    return a[0], -a[1]


def cint(value):
    return QQ(value), QQ(0)


def vadd(a, b):
    return tuple(a[j] + b[j] for j in range(3))


def vneg(a):
    return tuple(-x for x in a)


def cross(a, b):
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def idot(a, b):
    return sum(a[j] * b[j] for j in range(3))


def gdot(a, b):
    total = ZERO
    for left, right in zip(a, b):
        right_complex = right if isinstance(right, tuple) else cint(right)
        total = cadd(total, cmul(left, right_complex))
    return total


def representative(k):
    for component in k:
        if component:
            return k if component > 0 else vneg(k)
    raise ValueError("the zero mode has no representative")


def transverse_basis(k):
    result = []
    for coordinate in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        candidate = cross(k, coordinate)
        if candidate == (0, 0, 0):
            continue
        if result and cross(result[0], candidate) == (0, 0, 0):
            continue
        result.append(candidate)
        if len(result) == 2:
            return tuple(result)
    raise ValueError("could not construct a transverse basis for %r" % (k,))


def frame(k):
    first = transverse_basis(k)[0]
    second = cross(k, first)
    assert idot(first, second) == 0
    return first, second


def coordinates(value, basis):
    result = []
    for element in basis:
        numerator = gdot(value, element)
        denominator = QQ(idot(element, element))
        result.append((numerator[0] / denominator, numerator[1] / denominator))
    return tuple(result)


def real_triad_field(p, q, r, a, b, c, phases):
    modes = {}
    for k, polarization, phase in zip((p, q, r), (a, b, c), phases):
        amplitude = tuple(cmul(phase, cint(x)) for x in polarization)
        modes[k] = amplitude
        modes[vneg(k)] = tuple(cconjugate(x) for x in amplitude)
    return modes


def nonlinear_convolution(modes):
    nonlinear = {}
    for q, amplitude_q in modes.items():
        for r, amplitude_r in modes.items():
            target = vadd(q, r)
            factor = cmul(I, gdot(amplitude_q, r))
            term = tuple(cmul(factor, component) for component in amplitude_r)
            old = nonlinear.get(target, (ZERO, ZERO, ZERO))
            nonlinear[target] = tuple(cadd(old[j], term[j]) for j in range(3))
    return nonlinear


def convolution_row(modes, representatives, output_dimension):
    """Return real coefficients for complex output_dimension-by-2 blocks."""
    nonlinear = nonlinear_convolution(modes)
    mode_index = {k: j for j, k in enumerate(representatives)}
    width = 4 * output_dimension * len(representatives)
    row = [QQ(0)] * width

    for k, amplitude in modes.items():
        recipient = nonlinear.get(vneg(k))
        if recipient is None:
            continue
        mode = representative(k)
        orientation = 1 if k == mode else -1
        inputs = coordinates(amplitude, frame(mode))
        outputs = (
            coordinates(recipient, frame(mode))
            if output_dimension == 2
            else recipient
        )
        start = 4 * output_dimension * mode_index[mode]
        for output_index in range(output_dimension):
            for input_index in range(2):
                coefficient = cmul(outputs[output_index], inputs[input_index])
                matrix_index = 2 * output_index + input_index
                row[start + 2 * matrix_index] += coefficient[0]
                row[start + 2 * matrix_index + 1] -= orientation * coefficient[1]
    return row


def enumerate_rows(vectors, output_dimension, phases):
    representatives = sorted({representative(k) for k in vectors})
    vector_set = set(vectors)
    rows = []
    triads = 0
    for p in vectors:
        for q in vectors:
            r = vneg(vadd(p, q))
            if (
                r not in vector_set
                or not (p <= q <= r)
                or cross(p, q) == (0, 0, 0)
            ):
                continue
            triads += 1
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                for phase in phases:
                    modes = real_triad_field(p, q, r, a, b, c, phase)
                    row = convolution_row(modes, representatives, output_dimension)
                    if any(row):
                        rows.append(row)
    return representatives, triads, rows


def rational_row_echelon(rows):
    """Deterministic exact reducer used to recover the published minor."""
    basis = {}
    selected = []
    for index, source in enumerate(rows):
        row = list(source)
        for pivot in sorted(basis):
            if row[pivot]:
                factor = row[pivot]
                row = [x - factor * y for x, y in zip(row, basis[pivot])]
        pivot = next((j for j, value in enumerate(row) if value), None)
        if pivot is None:
            continue
        factor = row[pivot]
        basis[pivot] = [value / factor for value in row]
        selected.append(index)
    return tuple(selected), tuple(sorted(basis))


def modular_matrix(rows, prime):
    field = GF(prime)
    converted = [
        [
            field(value.numerator()) / field(value.denominator())
            for value in row
        ]
        for row in rows
    ]
    return matrix(field, converted)


def minor_residues(rows, selected_rows, selected_columns):
    square = [[rows[i][j] for j in selected_columns] for i in selected_rows]
    return tuple(int(modular_matrix(square, prime).determinant()) for prime in PRIMES)


def rational_rank(rows):
    return matrix(QQ, rows).rank()


def annihilates(rows, candidates):
    return all(
        sum(coefficient * parameter for coefficient, parameter in zip(row, candidate))
        == 0
        for row in rows
        for candidate in candidates
    )


def solenoidal_kernel(representatives):
    identity = []
    curl = []
    for k in representatives:
        first, second = frame(k)
        identity.extend((idot(first, first), 0, 0, 0, 0, 0, idot(second, second), 0))
        scale = idot(k, k) * idot(first, first)
        curl.extend((0, 0, 0, -scale, 0, scale, 0, 0))
    return [identity, curl]


def symmetric_basis():
    result = []
    for i in range(3):
        for j in range(i, 3):
            value = [[0, 0, 0] for _ in range(3)]
            value[i][j] = 1
            value[j][i] = 1
            result.append(tuple(tuple(row) for row in value))
    return result


def matvec(value, operand):
    return tuple(sum(value[i][j] * operand[j] for j in range(3)) for i in range(3))


def unrestricted_kernel_vector(representatives, zeroth, first):
    result = []
    for k in representatives:
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


def row_digest(rows):
    payload = "\n".join(
        ",".join("%s/%s" % (value.numerator(), value.denominator()) for value in row)
        for row in rows
    )
    return sha256(payload.encode("ascii")).hexdigest()


def verify_solenoidal_seed():
    representatives = sorted(
        {
            (1, 0, 0),
            (0, 1, 0),
            (0, 0, 1),
            (1, 1, 0),
            (1, 0, 1),
            (0, 1, 1),
            (1, 1, 1),
        }
    )
    vectors = sorted(set(representatives) | {vneg(k) for k in representatives})
    phases = tuple(product((ONE, I), repeat=3))
    actual_representatives, triads, rows = enumerate_rows(vectors, 2, phases)
    assert actual_representatives == representatives
    assert len(rows) == 720 and all(len(row) == 56 for row in rows)
    assert {int(value.denominator()) for row in rows for value in row} == {1, 2, 3, 6}

    kernel = solenoidal_kernel(representatives)
    assert rational_rank(kernel) == 2
    assert annihilates(rows, kernel)

    selected, columns = rational_row_echelon(rows)
    assert selected == SOLENOIDAL_ROWS
    assert columns == SOLENOIDAL_COLUMNS
    assert len(selected) == 54
    assert rational_rank(rows) == 54
    modular_ranks = tuple(modular_matrix(rows, prime).rank() for prime in PRIMES)
    assert modular_ranks == (54, 54)
    residues = minor_residues(rows, SOLENOIDAL_ROWS, SOLENOIDAL_COLUMNS)
    assert residues == SOLENOIDAL_RESIDUES

    print(
        "PASS 56->54: %d triads, 720 rows, rank 54, nullity 2; "
        "kernel <I,C_k>; minor residues %s" % (triads, residues)
    )


def verify_unrestricted_seed():
    vectors = [
        (x, y, z)
        for x, y, z in product(range(-1, 2), repeat=3)
        if (x, y, z) != (0, 0, 0)
    ]
    phases = ((ONE, ONE, ONE), (I, ONE, ONE))
    representatives, triads, rows = enumerate_rows(vectors, 3, phases)
    assert len(representatives) == 13
    assert triads == 44
    assert len(rows) == 680 and all(len(row) == 156 for row in rows)
    assert {int(value.denominator()) for row in rows for value in row} == {1}
    digest = row_digest(rows)
    assert digest == UNRESTRICTED_DIGEST

    matrices = symmetric_basis()
    kernel = [
        unrestricted_kernel_vector(representatives, value, None)
        for value in matrices
    ] + [
        unrestricted_kernel_vector(representatives, None, value)
        for value in matrices
    ]
    assert rational_rank(kernel) == 12
    assert annihilates(rows, kernel)

    modular_ranks = tuple(modular_matrix(rows, prime).rank() for prime in PRIMES)
    assert modular_ranks == (144, 144)
    assert len(UNRESTRICTED_ROWS) == len(UNRESTRICTED_COLUMNS) == 144
    residues = minor_residues(rows, UNRESTRICTED_ROWS, UNRESTRICTED_COLUMNS)
    assert residues == UNRESTRICTED_RESIDUES

    # The nonzero minor gives rank >= 144 over QQ.  The twelve independent
    # displayed kernel vectors give rank <= 156 - 12 = 144.
    print(
        "PASS 156->144: 13 modes, %d triads, 680 rows, rank 144, nullity 12; "
        "kernel <A+B C_k+C_k B>; minor residues %s" % (triads, residues)
    )
    print("row SHA-256: %s" % digest)


def main():
    verify_solenoidal_seed()
    verify_unrestricted_seed()
    print("All SageMath seed certificates reproduced exactly.")


if __name__ == "__main__":
    main()
