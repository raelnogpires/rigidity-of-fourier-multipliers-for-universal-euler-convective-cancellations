#!/usr/bin/env python3
"""Verify the unrestricted-output Euler multiplier rigidity theorem.

The existing verifier assumes R(k): k^perp -> k^perp.  Here the codomain is
all of C^3.  Each unoriented mode therefore has a general complex 3-by-2
matrix (twelve real parameters), subject only to the reality condition.
"""

from __future__ import annotations

from fractions import Fraction
from hashlib import sha256
from itertools import product
from typing import Dict, Iterable, List, Sequence, Tuple

from explore_full_multiplier import (
    Gaussian,
    GVec,
    IMAGINARY_UNIT,
    ONE,
    ZERO,
    add_independent_row,
    coordinates,
    exact_triad_modes,
    gadd,
    gdot,
    gmul,
    orthogonal_frame,
)
from verify_full_multiplier_rigidity import (
    BOOLEAN_SEED_REPRESENTATIVES,
    boolean_seed_vectors,
    nonzero_vectors,
)
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
from verify_general_multiplier_rigidity import (
    add_independent_row_mod,
    determinant_mod,
    exact_rank,
)
import verify_tensorial_miller_identity as tensor
import verify_adaptive_miller_metric as adaptive

PHASE_REPRESENTATIVES = (
    (ONE, ONE, ONE),
    (IMAGINARY_UNIT, ONE, ONE),
)

CERTIFICATE_PRIMES = (1_000_003, 1_000_000_007)
EXPECTED_MINOR_DETERMINANTS = (272_144, 290_707_620)
EXPECTED_ROW_DIGEST = "a4fc3b45a6fc94defd38d992dbbe27f4413254b3af307e41d1c7e25839e9c30d"
EXPECTED_PRESSURE_CHANNEL_DIGEST = "6dc1558341229de31a154e4c5c1fb25e1a1d01d1ac42ec741e6ca71535ee3124"
PRESSURE_CHANNEL_MINOR_ROWS = (0, 1, 2, 3, 4, 5, 7, 8, 16, 17)
PRESSURE_CHANNEL_MINOR_COLUMNS = (0, 1, 2, 3, 4, 6, 7, 8, 9, 10)
EXPECTED_PRESSURE_CHANNEL_MINOR = Fraction(287_712)
ADJOINT_PRESSURE_MINOR_ROWS = (0, 1, 2, 3, 4, 5, 6, 7, 16, 17)
ADJOINT_PRESSURE_MINOR_COLUMNS = (0, 7, 1, 6, 2, 8, 4, 10, 3, 9)
EXPECTED_ADJOINT_PRESSURE_MINOR = Fraction(-2_916)
EXPECTED_JOINT_PRESSURE_DIGEST = "1a800ab11a48d5f5c785cded933a7a0b906e5c83b8697f4197afc00d35c7d8c6"
JOINT_PRESSURE_MINOR_ROWS = (0, 1, 2, 3, 4, 5, 6, 7, 9, 16, 17)
JOINT_PRESSURE_MINOR_COLUMNS = (0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11)
EXPECTED_JOINT_PRESSURE_MINOR = Fraction(-7_965)
CERTIFICATE_ROW_INDICES = (
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
CERTIFICATE_PIVOT_COLUMNS = tuple(range(119)) + (
    120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133,
    134, 135, 136, 138, 139, 141, 142, 144, 145, 147, 149,
)


def unrestricted_output_row(
    modes: Dict[Vec, GVec], representatives: Sequence[Vec]
) -> List[Fraction]:
    """Coefficients of <Rw,(w dot grad)w> for R(k): k^perp -> C^3."""
    index = {k: i for i, k in enumerate(representatives)}
    row: List[Gaussian] = [ZERO] * (12 * len(representatives))
    for p, q, r in product(modes, repeat=3):
        if add(add(p, q), r) != (0, 0, 0):
            continue
        representative = unoriented(p)
        base = 12 * index[representative]
        x = coordinates(modes[p], orthogonal_frame(representative))
        derivative = gmul(IMAGINARY_UNIT, gdot(modes[q], r))
        nonlinear = tuple(gmul(derivative, component) for component in modes[r])
        orientation = 1 if p == representative else -1
        for output_index in range(3):
            for input_index in range(2):
                coefficient = gmul(nonlinear[output_index], x[input_index])
                matrix_index = 2 * output_index + input_index
                real_column = base + 2 * matrix_index
                imaginary_column = real_column + 1
                row[real_column] = gadd(row[real_column], coefficient)
                imaginary_coefficient = gmul(IMAGINARY_UNIT, coefficient)
                if orientation < 0:
                    imaginary_coefficient = (
                        -imaginary_coefficient[0],
                        -imaginary_coefficient[1],
                    )
                row[imaginary_column] = gadd(
                    row[imaginary_column], imaginary_coefficient
                )
    assert all(value[1] == 0 for value in row)
    return [value[0] for value in row]


def triad_rows(
    p: Vec, q: Vec, r: Vec, representatives: Sequence[Vec]
) -> Iterable[List[Fraction]]:
    for a, b, c in product(
        transverse_basis(p), transverse_basis(q), transverse_basis(r)
    ):
        for phase in PHASE_REPRESENTATIVES:
            row = unrestricted_output_row(
                exact_triad_modes(p, q, r, a, b, c, phase), representatives
            )
            if any(row):
                yield row


def enumerate_rows(vectors: Sequence[Vec]) -> Iterable[List[Fraction]]:
    representatives = sorted({unoriented(k) for k in vectors})
    vector_set = set(vectors)
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vector_set or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            for row in triad_rows(p, q, r, representatives):
                yield row


def count_triads(vectors: Sequence[Vec]) -> int:
    vector_set = set(vectors)
    return sum(
        1
        for p in vectors
        for q in vectors
        if (r := neg(add(p, q))) in vector_set
        and p <= q <= r
        and cross(p, q) != (0, 0, 0)
    )


def analyze_vectors(
    vectors: Sequence[Vec], *, modular_prime: int | None = None
) -> tuple[int, int, int, int]:
    representatives = sorted({unoriented(k) for k in vectors})
    basis = {}
    row_count = 0
    for row in enumerate_rows(vectors):
        row_count += 1
        if modular_prime is None:
            add_independent_row(basis, row)
        else:
            add_independent_row_mod(basis, row, modular_prime)
    return len(representatives), count_triads(vectors), row_count, len(basis)


def row_digest(rows: Sequence[Sequence[Fraction]]) -> str:
    payload = "\n".join(
        ",".join(f"{value.numerator}/{value.denominator}" for value in row)
        for row in rows
    )
    return sha256(payload.encode("ascii")).hexdigest()


def symmetric_matrix_basis() -> List[Tuple[Tuple[int, int, int], ...]]:
    result = []
    for i in range(3):
        for j in range(i, 3):
            matrix = [[0, 0, 0] for _ in range(3)]
            matrix[i][j] = 1
            matrix[j][i] = 1
            result.append(tuple(tuple(row) for row in matrix))
    return result


def matvec(matrix: Sequence[Sequence[int]], vector: Sequence[int]) -> Tuple[int, int, int]:
    return tuple(sum(matrix[i][j] * vector[j] for j in range(3)) for i in range(3))  # type: ignore[return-value]


def verify_adjoint_helical_collapse() -> int:
    """Check the exact plane anticommutator and its sharper coercive cone."""
    matrices = symmetric_matrix_basis() + [
        ((2, 1, -1), (1, -3, 2), (-1, 2, 4))
    ]
    checks = 0
    for k in nonzero_vectors(2):
        radius_squared = norm2(k)
        for a_matrix in matrices:
            trace_a = sum(a_matrix[i][i] for i in range(3))
            a_k = matvec(a_matrix, k)
            plane_trace = Fraction(trace_a) - Fraction(
                dot(k, a_k).real, radius_squared
            )
            for vector in transverse_basis(k):
                k_cross_v = cross(k, vector)
                a_k_cross_v = matvec(a_matrix, k_cross_v)
                k_cross_a_v = cross(k, matvec(a_matrix, vector))
                unprojected = tuple(
                    Fraction(a_k_cross_v[i].real)
                    + Fraction(k_cross_a_v[i].real)
                    for i in range(3)
                )
                longitudinal = Fraction(
                    dot(k, unprojected).real, radius_squared
                )
                projected = tuple(
                    unprojected[i] - longitudinal * k[i]
                    for i in range(3)
                )
                expected = tuple(
                    plane_trace * Fraction(k_cross_v[i].real)
                    for i in range(3)
                )
                assert projected == expected
                checks += 1

    # A=diag(2,-2,0), H=(3/2)I lies outside the former norm ball
    # lambda_min(H)>||A||, but the trace-reversed LMI has margin 1/2.
    a_matrix = ((2, 0, 0), (0, -2, 0), (0, 0, 0))
    trace_a = sum(a_matrix[i][i] for i in range(3))
    trace_reversal = tuple(
        tuple(
            Fraction(trace_a * (i == j) - a_matrix[i][j])
            for j in range(3)
        )
        for i in range(3)
    )
    h_diagonal = (Fraction(3, 2),) * 3
    assert Fraction(3, 2) <= Fraction(2)  # the former norm criterion fails
    for sign in (-1, 1):
        lmi_diagonal = tuple(
            h_diagonal[i] + sign * trace_reversal[i][i] / 2
            for i in range(3)
        )
        assert min(lmi_diagonal) == Fraction(1, 2)
    return checks


def candidate_vector(
    representatives: Sequence[Vec],
    zeroth: Sequence[Sequence[int]] | None,
    first: Sequence[Sequence[int]] | None,
) -> List[int]:
    """Coordinates of A + B C_k + C_k B for symmetric A,B."""
    result: List[int] = []
    for k in representatives:
        for output_index in range(3):
            for frame_vector in orthogonal_frame(k):
                real_part = 0 if zeroth is None else matvec(zeroth, frame_vector)[output_index]
                if first is None:
                    imaginary_part = 0
                else:
                    first_cross = matvec(first, tuple(int(x.real) for x in cross(k, frame_vector)))
                    second_cross = cross(k, matvec(first, frame_vector))
                    imaginary_part = first_cross[output_index] + int(second_cross[output_index].real)
                result.extend((real_part, imaginary_part))
    return result


def verify_unit_box_certificate() -> tuple[
    int, int, int, Tuple[int, int], Tuple[int, int]
]:
    vectors = nonzero_vectors(1)
    representatives = sorted({unoriented(k) for k in vectors})
    candidates = [
        candidate_vector(representatives, matrix, None)
        for matrix in symmetric_matrix_basis()
    ] + [
        candidate_vector(representatives, None, matrix)
        for matrix in symmetric_matrix_basis()
    ]
    candidate_basis: Dict[int, List[Fraction]] = {}
    for candidate in candidates:
        add_independent_row(candidate_basis, candidate)
    assert len(candidate_basis) == 12

    primes = CERTIFICATE_PRIMES
    modular_bases = ({}, {})
    row_count = 0
    denominators = set()
    all_rows = list(enumerate_rows(vectors))
    assert row_digest(all_rows) == EXPECTED_ROW_DIGEST
    for row in all_rows:
        row_count += 1
        denominators.update(value.denominator for value in row)
        assert all(sum(x * y for x, y in zip(row, candidate)) == 0 for candidate in candidates)
        for basis, prime in zip(modular_bases, primes):
            add_independent_row_mod(basis, row, prime)
    ranks = (len(modular_bases[0]), len(modular_bases[1]))
    assert ranks == (144, 144)
    assert all(denominator % prime for denominator in denominators for prime in primes)
    assert len(CERTIFICATE_ROW_INDICES) == len(CERTIFICATE_PIVOT_COLUMNS) == 144
    selected_rows = [all_rows[index] for index in CERTIFICATE_ROW_INDICES]
    determinants = tuple(
        determinant_mod(selected_rows, CERTIFICATE_PIVOT_COLUMNS, prime)
        for prime in primes
    )
    assert determinants == EXPECTED_MINOR_DETERMINANTS
    return len(representatives), row_count, len(candidate_basis), ranks, determinants


def direct_target_rows(p: Vec, q: Vec, r: Vec) -> List[List[Fraction]]:
    """Rows on one unrestricted 3-by-2 target block, with the parents zero."""
    assert add(add(p, q), r) == (0, 0, 0)
    rows: List[List[Fraction]] = []
    target_frame = orthogonal_frame(p)
    for input_index, a in enumerate(target_frame):
        for b, c in product(transverse_basis(q), transverse_basis(r)):
            nonlinear = tuple(
                int(dot(b, r).real) * c[i] + int(dot(c, q).real) * b[i]
                for i in range(3)
            )
            for imaginary_phase in (False, True):
                row = [Fraction(0)] * 12
                for output_index, coefficient in enumerate(nonlinear):
                    matrix_index = 2 * output_index + input_index
                    column = 2 * matrix_index + int(imaginary_phase)
                    row[column] = -coefficient if imaginary_phase else coefficient
                if any(row):
                    rows.append(row)
    return rows


def verify_raw_local_ranks(radius: int = 1) -> int:
    """Check the rank-eight raw lemma and its image-line kernel."""
    vectors = nonzero_vectors(radius)
    vector_set = set(vectors)
    checks = 0
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vector_set or q > r or cross(p, q) == (0, 0, 0):
                continue
            rows = direct_target_rows(p, q, r)
            assert exact_rank(rows) == 8
            difference = subtract(r, q)
            line_kernel = []
            for input_index in range(2):
                for imaginary_part in range(2):
                    candidate = [0] * 12
                    for output_index in range(3):
                        matrix_index = 2 * output_index + input_index
                        candidate[2 * matrix_index + imaginary_part] = difference[output_index]
                    line_kernel.append(candidate)
            kernel_basis: Dict[int, List[Fraction]] = {}
            for candidate in line_kernel:
                add_independent_row(kernel_basis, candidate)
            assert len(kernel_basis) == 4
            assert all(
                sum(x * y for x, y in zip(row, candidate)) == 0
                for row in rows
                for candidate in line_kernel
            )
            checks += 1
    return checks


def subtract(a: Vec, b: Vec) -> Vec:
    return tuple(a[i] - b[i] for i in range(3))  # type: ignore[return-value]


def axis_vector(index: int, sign: int = 1) -> Vec:
    return tuple(sign if j == index else 0 for j in range(3))  # type: ignore[return-value]


def l1(k: Vec) -> int:
    return sum(abs(x) for x in k)


def is_axis(k: Vec) -> bool:
    return sum(x != 0 for x in k) == 1


def two_triad_propagation(radius: int = 10) -> tuple[int, int]:
    """Replay a two-parent-pair ordering and check every 12-parameter block."""
    all_vectors = nonzero_vectors(radius)
    representatives = sorted({unoriented(k) for k in all_vectors}, key=lambda k: (l1(k), k))
    known = set(nonzero_vectors(1))
    steps = 0
    for shell in range(2, 3 * radius + 1):
        shell_targets = [k for k in representatives if l1(k) == shell and k not in known]
        for k in [target for target in shell_targets if not is_axis(target)]:
            indices = [i for i, value in enumerate(k) if value]
            i, j = indices[:2]
            s_i = axis_vector(i, 1 if k[i] > 0 else -1)
            s_j = axis_vector(j, 1 if k[j] > 0 else -1)
            pairs = ((subtract(k, s_i), s_i), (subtract(k, s_j), s_j))
            assert all(a in known and b in known for a, b in pairs)
            differences = [subtract(b, a) for a, b in pairs]
            assert cross(differences[0], differences[1]) != (0, 0, 0)
            rows = []
            for a, b in pairs:
                rows.extend(direct_target_rows(neg(k), a, b))
            assert exact_rank(rows) == 12
            known.update((k, neg(k)))
            steps += 1

        for k in [target for target in shell_targets if is_axis(target)]:
            i = next(index for index, value in enumerate(k) if value)
            s_i = axis_vector(i, 1 if k[i] > 0 else -1)
            transverse_indices = [index for index in range(3) if index != i]
            pairs = []
            for j in transverse_indices:
                e_j = axis_vector(j)
                a = add(tuple((shell - 1) * x for x in s_i), e_j)  # type: ignore[arg-type]
                b = subtract(s_i, e_j)
                pairs.append((a, b))
            assert all(a in known and b in known for a, b in pairs)
            differences = [subtract(b, a) for a, b in pairs]
            assert cross(differences[0], differences[1]) != (0, 0, 0)
            rows = []
            for a, b in pairs:
                rows.extend(direct_target_rows(neg(k), a, b))
            assert exact_rank(rows) == 12
            known.update((k, neg(k)))
            steps += 1

    assert set(all_vectors).issubset(known)
    return steps, len(all_vectors)


def verify_pressure_completion(radius: int = 3) -> int:
    """Check |k|^2 B + C_k B C_k = L_H + longitudinal correction."""
    checks = 0
    for matrix in symmetric_matrix_basis():
        trace = sum(matrix[i][i] for i in range(3))
        h_matrix = tuple(
            tuple((trace if i == j else 0) - matrix[i][j] for j in range(3))
            for i in range(3)
        )
        h_trace = sum(h_matrix[i][i] for i in range(3))
        recovered = tuple(
            tuple((h_trace // 2 if i == j else 0) - h_matrix[i][j] for j in range(3))
            for i in range(3)
        )
        assert recovered == matrix
        for k in nonzero_vectors(radius):
            for v in transverse_basis(k):
                k_cross_v = tuple(int(x.real) for x in cross(k, v))
                curl_b_curl = tuple(
                    -int(x.real) for x in cross(k, matvec(matrix, k_cross_v))
                )
                left = tuple(
                    norm2(k) * matvec(matrix, v)[i] + curl_b_curl[i]
                    for i in range(3)
                )
                symbol = sum(k[i] * matvec(h_matrix, k)[i] for i in range(3))
                longitudinal_scale = sum(k[i] * matvec(matrix, v)[i] for i in range(3))
                right = tuple(symbol * v[i] + k[i] * longitudinal_scale for i in range(3))
                assert left == right
                checks += 1
    return checks


def _gint(value: int | Fraction) -> Gaussian:
    return Fraction(value), Fraction(0)


def _add_scalar_fields(
    left: Dict[Vec, Gaussian],
    right: Dict[Vec, Gaussian],
    left_scale: int | Fraction = 1,
    right_scale: int | Fraction = 1,
) -> Dict[Vec, Gaussian]:
    result: Dict[Vec, Gaussian] = {}
    for mode in set(left) | set(right):
        value = gadd(
            gmul(_gint(left_scale), left.get(mode, ZERO)),
            gmul(_gint(right_scale), right.get(mode, ZERO)),
        )
        if value != ZERO:
            result[mode] = value
    return result


def _scalar_convolution(
    left: Dict[Vec, GVec], right: Dict[Vec, GVec]
) -> Dict[Vec, Gaussian]:
    result: Dict[Vec, Gaussian] = {}
    for q, left_value in left.items():
        for r, right_value in right.items():
            value = gdot(left_value, right_value)
            tensor.add_scalar_mode(result, add(q, r), value)
    return result


def _matrix_frobenius_convolution(
    left: Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]],
    right: Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]],
) -> Dict[Vec, Gaussian]:
    result: Dict[Vec, Gaussian] = {}
    for q, left_value in left.items():
        for r, right_value in right.items():
            value = tensor.sum_gaussians(
                gmul(left_value[i][j], right_value[i][j])
                for i in range(3)
                for j in range(3)
            )
            tensor.add_scalar_mode(result, add(q, r), value)
    return result


def _dyad_convolution(
    vector: Dict[Vec, GVec],
) -> Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]]:
    components: Dict[Tuple[int, int], Dict[Vec, Gaussian]] = {}
    for i in range(3):
        for j in range(3):
            component: Dict[Vec, Gaussian] = {}
            for q, left_value in vector.items():
                for r, right_value in vector.items():
                    tensor.add_scalar_mode(
                        component,
                        add(q, r),
                        gmul(left_value[i], right_value[j]),
                    )
            components[i, j] = component
    modes = set().union(*(set(component) for component in components.values()))
    return {
        mode: tuple(
            tuple(components[i, j].get(mode, ZERO) for j in range(3))
            for i in range(3)
        )
        for mode in modes
    }


def _integral_scalar_product(
    left: Dict[Vec, Gaussian], right: Dict[Vec, Gaussian]
) -> Gaussian:
    return tensor.sum_gaussians(
        gmul(value, right.get(neg(mode), ZERO))
        for mode, value in left.items()
    )


def _integral_matrix_product(
    left: Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]],
    right: Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]],
) -> Gaussian:
    result = ZERO
    for mode, left_value in left.items():
        right_value = right.get(neg(mode))
        if right_value is None:
            continue
        result = gadd(
            result,
            tensor.sum_gaussians(
                gmul(left_value[i][j], right_value[i][j])
                for i in range(3)
                for j in range(3)
            ),
        )
    return result


def _divergence_field(vector: Dict[Vec, GVec]) -> Dict[Vec, Gaussian]:
    return {
        mode: gmul(IMAGINARY_UNIT, gdot(value, mode))
        for mode, value in vector.items()
    }


def _raw_completed_field(
    field: Dict[Vec, GVec],
    zeroth: Sequence[Sequence[Fraction]],
    h_matrix: Sequence[Sequence[Fraction]],
) -> Dict[Vec, GVec]:
    trace = sum(h_matrix[i][i] for i in range(3))
    b_matrix = tuple(
        tuple(
            (trace / 2 if i == j else Fraction(0)) - h_matrix[i][j]
            for j in range(3)
        )
        for i in range(3)
    )
    vorticity = {
        mode: tensor.omega(mode, value) for mode, value in field.items()
    }
    result: Dict[Vec, GVec] = {}
    for mode, value in field.items():
        scalar_symbol = sum(
            h_matrix[i][j] * mode[i] * mode[j]
            for i in range(3)
            for j in range(3)
        )
        first = tensor.matrix_vector(zeroth, vorticity[mode])
        second = tensor.gvscale(value, scalar_symbol)
        b_value = tensor.matrix_vector(b_matrix, value)
        longitudinal_scalar = gdot(b_value, mode)
        third = tuple(
            gmul(longitudinal_scalar, _gint(mode[i])) for i in range(3)
        )
        result[mode] = tuple(
            gadd(first[i], gadd(second[i], third[i])) for i in range(3)
        )
    return result


def _zero_matrix() -> Tuple[Tuple[Fraction, Fraction, Fraction], ...]:
    return tuple(
        tuple(Fraction(0) for _ in range(3))
        for _ in range(3)
    )


def _adjoint_closed_field(
    field: Dict[Vec, GVec],
    a_matrix: Sequence[Sequence[Fraction]],
    h_matrix: Sequence[Sequence[Fraction]],
) -> Dict[Vec, GVec]:
    """Fourier field for 1/2(A curl + curl A)u + T_{B_H}u."""
    h_part = _raw_completed_field(field, _zero_matrix(), h_matrix)
    result: Dict[Vec, GVec] = {}
    half = _gint(Fraction(1, 2))
    for mode, value in field.items():
        vorticity = tensor.omega(mode, value)
        a_vorticity = tensor.matrix_vector(a_matrix, vorticity)
        a_value = tensor.matrix_vector(a_matrix, value)
        curl_a_value = tensor.omega(mode, a_value)
        result[mode] = tuple(
            gadd(
                gmul(half, gadd(a_vorticity[i], curl_a_value[i])),
                h_part[mode][i],
            )
            for i in range(3)
        )
    return result


def _gamma_functional(
    field: Dict[Vec, GVec],
    a_matrix: Sequence[Sequence[Fraction]],
) -> Fraction:
    """Return Gamma_u(A)=int omega_i omega_j d_i[curl(Au)]_j."""
    vorticity = {
        mode: tensor.omega(mode, value) for mode, value in field.items()
    }
    curl_a_field = {
        mode: tensor.omega(
            mode, tensor.matrix_vector(a_matrix, value)
        )
        for mode, value in field.items()
    }
    dyad = _dyad_convolution(vorticity)
    total = ZERO
    for i in range(3):
        for j in range(3):
            derivative = {
                mode: gmul(
                    gmul(IMAGINARY_UNIT, _gint(mode[i])),
                    value[j],
                )
                for mode, value in curl_a_field.items()
            }
            dyad_component = {
                mode: value[i][j] for mode, value in dyad.items()
            }
            total = gadd(
                total,
                _integral_scalar_product(dyad_component, derivative),
            )
    assert total[1] == 0
    return total[0]


def _gamma_tensor(
    field: Dict[Vec, GVec],
) -> Tuple[Tuple[Fraction, Fraction, Fraction], ...]:
    """Symmetric coefficient tensor with Gamma_u(A)=A:Gamma_u^sharp."""
    result = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for a in range(3):
        for b in range(a, 3):
            matrix = [[Fraction(0) for _ in range(3)] for _ in range(3)]
            matrix[a][b] += Fraction(1, 2)
            matrix[b][a] += Fraction(1, 2)
            value = _gamma_functional(field, matrix)
            result[a][b] = result[b][a] = value
    return tuple(tuple(row) for row in result)


def _j_rate_tensor(
    field: Dict[Vec, GVec],
) -> Tuple[Tuple[Fraction, Fraction, Fraction], ...]:
    """J=(K+K^T)/4 for K_ab=int S_ia d_i omega_b."""
    vorticity = {
        mode: tensor.omega(mode, value) for mode, value in field.items()
    }
    strains = {
        mode: tensor.strain_matrix(mode, value) for mode, value in field.items()
    }
    k_tensor = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for a in range(3):
        for b in range(3):
            value = ZERO
            for i in range(3):
                derivative = {
                    mode: gmul(
                        gmul(IMAGINARY_UNIT, _gint(mode[i])),
                        omega_value[b],
                    )
                    for mode, omega_value in vorticity.items()
                }
                strain_component = {
                    mode: strains[mode][i][a] for mode in strains
                }
                value = gadd(
                    value,
                    _integral_scalar_product(strain_component, derivative),
                )
            assert value[1] == 0
            k_tensor[a][b] = value[0]
    return tuple(
        tuple(
            (k_tensor[a][b] + k_tensor[b][a]) / 4
            for b in range(3)
        )
        for a in range(3)
    )


def _matrix_inner(
    left: Sequence[Sequence[Fraction]],
    right: Sequence[Sequence[Fraction]],
) -> Fraction:
    return sum(
        left[i][j] * right[i][j]
        for i in range(3)
        for j in range(3)
    )


def _pressure_hessian_and_scalars(
    field: Dict[Vec, GVec],
) -> tuple[
    Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]],
    Dict[Vec, Gaussian],
    Dict[Vec, Gaussian],
]:
    vorticity = {
        mode: tensor.omega(mode, value) for mode, value in field.items()
    }
    strains = {
        mode: tensor.strain_matrix(mode, value) for mode, value in field.items()
    }
    strain_square = _matrix_frobenius_convolution(strains, strains)
    vorticity_square = _scalar_convolution(vorticity, vorticity)
    pressure_laplacian = _add_scalar_fields(
        strain_square,
        vorticity_square,
        left_scale=-1,
        right_scale=Fraction(1, 2),
    )
    hessian: Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]] = {}
    for mode, value in pressure_laplacian.items():
        denominator = norm2(mode)
        if denominator == 0:
            continue
        hessian[mode] = tuple(
            tuple(
                gmul(value, _gint(Fraction(mode[i] * mode[j], denominator)))
                for j in range(3)
            )
            for i in range(3)
        )
    return hessian, strain_square, vorticity_square


def _forcing_field(
    field: Dict[Vec, GVec],
) -> Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]]:
    vorticity = {mode: tensor.omega(mode, value) for mode, value in field.items()}
    hessian, _strain_square, vorticity_square = _pressure_hessian_and_scalars(field)
    dyad = _dyad_convolution(vorticity)
    result: Dict[Vec, Tuple[Tuple[Gaussian, ...], ...]] = {}
    modes = set(dyad) | set(hessian) | set(vorticity_square)
    for mode in modes:
        result[mode] = tuple(
            tuple(
                gadd(
                    hessian.get(mode, ((ZERO,) * 3,) * 3)[i][j],
                    gadd(
                        gmul(_gint(Fraction(1, 4)), dyad.get(mode, ((ZERO,) * 3,) * 3)[i][j]),
                        gmul(
                            _gint(Fraction(-1, 4)),
                            vorticity_square.get(mode, ZERO),
                        )
                        if i == j
                        else ZERO,
                    ),
                )
                for j in range(3)
            )
            for i in range(3)
        )
    return result


def _pressure_channel_row(field: Dict[Vec, GVec]) -> List[Fraction]:
    """One exact row for the universal full-forcing residual."""
    _hessian, strain_square, vorticity_square = _pressure_hessian_and_scalars(field)
    scalar_factor = _add_scalar_fields(
        strain_square,
        vorticity_square,
        left_scale=1,
        right_scale=Fraction(-1, 4),
    )
    zero_matrix = ((Fraction(0),) * 3,) * 3
    row: List[Fraction] = []
    for zeroth, h_matrix in (
        *(
            (
                matrix,
                zero_matrix,
            )
            for matrix in symmetric_matrix_basis()
        ),
        *(
            (
                zero_matrix,
                matrix,
            )
            for matrix in symmetric_matrix_basis()
        ),
    ):
        residual = _integral_scalar_product(
            scalar_factor,
            _divergence_field(_raw_completed_field(field, zeroth, h_matrix)),
        )
        assert residual[1] == 0
        row.append(residual[0])
    return row


def _adaptive_seed_field(phase_shift: int) -> Dict[Vec, GVec]:
    """Rebuild the two deterministic seven-mode fields used in the metric note."""
    representatives = (
        (1, 0, 0),
        (0, 1, 0),
        (0, 0, 1),
        (1, 1, 0),
        (1, 0, 1),
        (0, 1, 1),
        (1, 1, 1),
    )
    phases = (
        ONE,
        IMAGINARY_UNIT,
        (Fraction(1), Fraction(1)),
        (Fraction(2), Fraction(-1)),
    )
    field: Dict[Vec, GVec] = {}
    for index, mode in enumerate(representatives):
        polarization = transverse_basis(mode)[(index + phase_shift) % 2]
        phase = phases[(index + phase_shift) % len(phases)]
        amplitude = tuple(
            gmul(phase, _gint(component)) for component in polarization
        )
        field[mode] = amplitude  # type: ignore[assignment]
        field[neg(mode)] = tuple(
            (component[0], -component[1]) for component in amplitude
        )  # type: ignore[assignment]
    return field


def _strain_gram_tensor(
    field: Dict[Vec, GVec],
) -> Tuple[Tuple[Fraction, Fraction, Fraction], ...]:
    strains = {
        mode: tensor.strain_matrix(mode, value) for mode, value in field.items()
    }
    result = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for mode, strain in strains.items():
        opposite = strains.get(neg(mode))
        assert opposite is not None
        contraction = tensor.sum_gaussians(
            gmul(strain[i][j], opposite[i][j])
            for i in range(3)
            for j in range(3)
        )
        assert contraction[1] == 0
        for a in range(3):
            for b in range(3):
                result[a][b] += mode[a] * mode[b] * contraction[0]
    return tuple(tuple(row) for row in result)


def _dynamic_pressure_tensors(
    field: Dict[Vec, GVec],
) -> tuple[
    Tuple[Tuple[Fraction, Fraction, Fraction], ...],
    Tuple[Tuple[Fraction, Fraction, Fraction], ...],
    Tuple[Tuple[Fraction, Fraction, Fraction], ...],
]:
    """Return J, Pi,Theta for the moving self-adjoint pressure-work law."""
    vorticity = {
        mode: tensor.omega(mode, value) for mode, value in field.items()
    }
    curl_vorticity = {
        mode: tensor.omega(mode, value) for mode, value in vorticity.items()
    }
    strains = {
        mode: tensor.strain_matrix(mode, value) for mode, value in field.items()
    }
    _hessian, strain_square, vorticity_square = _pressure_hessian_and_scalars(field)
    theta = _add_scalar_fields(
        strain_square,
        vorticity_square,
        left_scale=1,
        right_scale=Fraction(-1, 4),
    )

    j_tensor = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    pi_tensor = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    theta_tensor = [[Fraction(0) for _ in range(3)] for _ in range(3)]
    for i in range(3):
        for j in range(3):
            left = tensor.sum_gaussians(
                gmul(
                    curl_vorticity[mode][i],
                    vorticity[neg(mode)][j],
                )
                for mode in curl_vorticity
            )
            right = tensor.sum_gaussians(
                gmul(
                    curl_vorticity[mode][j],
                    vorticity[neg(mode)][i],
                )
                for mode in curl_vorticity
            )
            value = gadd(left, right)
            assert value[1] == 0
            j_tensor[i][j] = value[0] / 8

            derivative_i_omega_j = {
                mode: gmul(
                    gmul(IMAGINARY_UNIT, _gint(mode[i])),
                    value[j],
                )
                for mode, value in vorticity.items()
            }
            derivative_j_omega_i = {
                mode: gmul(
                    gmul(IMAGINARY_UNIT, _gint(mode[j])),
                    value[i],
                )
                for mode, value in vorticity.items()
            }
            pi_value = gadd(
                _integral_scalar_product(theta, derivative_i_omega_j),
                _integral_scalar_product(theta, derivative_j_omega_i),
            )
            assert pi_value[1] == 0
            pi_tensor[i][j] = pi_value[0] / 2

            laplacian_strain_ij = {
                mode: gmul(_gint(-norm2(mode)), value[i][j])
                for mode, value in strains.items()
            }
            theta_value = _integral_scalar_product(theta, laplacian_strain_ij)
            assert theta_value[1] == 0
            theta_tensor[i][j] = theta_value[0]
    return (
        tuple(tuple(row) for row in j_tensor),
        tuple(tuple(row) for row in pi_tensor),
        tuple(tuple(row) for row in theta_tensor),
    )


def _fractional_rank(rows: Sequence[Sequence[Fraction]]) -> int:
    basis: Dict[int, List[Fraction]] = {}
    for source in rows:
        row = list(source)
        for pivot in sorted(basis):
            if row[pivot]:
                factor = row[pivot]
                row = [left - factor * right for left, right in zip(row, basis[pivot])]
        pivot = next((index for index, value in enumerate(row) if value), None)
        if pivot is None:
            continue
        factor = row[pivot]
        basis[pivot] = [value / factor for value in row]
    return len(basis)


def _fractional_determinant(matrix: Sequence[Sequence[Fraction]]) -> Fraction:
    """Exact determinant used for the small full-forcing certificate."""
    rows = [list(row) for row in matrix]
    result = Fraction(1)
    for column in range(len(rows)):
        pivot = next(
            (row for row in range(column, len(rows)) if rows[row][column]),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            rows[column], rows[pivot] = rows[pivot], rows[column]
            result = -result
        pivot_value = rows[column][column]
        result *= pivot_value
        rows[column] = [value / pivot_value for value in rows[column]]
        for row in range(column + 1, len(rows)):
            scale = rows[row][column]
            rows[row] = [
                rows[row][index] - scale * rows[column][index]
                for index in range(len(rows))
            ]
    return result


def verify_dynamic_self_adjoint_pressure_work() -> Tuple[Fraction, Fraction]:
    """Exact seed obstructions for the moving seven-parameter energy class."""
    expected_matrices = (
        (
            (Fraction(35), Fraction(32), Fraction(14)),
            (Fraction(32), Fraction(35), Fraction(14)),
            (Fraction(14), Fraction(14), Fraction(18)),
        ),
        (
            (Fraction(37), Fraction(32), Fraction(34)),
            (Fraction(32), Fraction(42), Fraction(38)),
            (Fraction(34), Fraction(38), Fraction(47)),
        ),
    )
    expected_theta = (
        (
            (Fraction(8), Fraction(7, 2), Fraction(-1, 2)),
            (Fraction(7, 2), Fraction(-8), Fraction(9, 2)),
            (Fraction(-1, 2), Fraction(9, 2), Fraction(0)),
        ),
        (
            (Fraction(2), Fraction(-1, 2), Fraction(-2)),
            (Fraction(-1, 2), Fraction(6), Fraction(-2)),
            (Fraction(-2), Fraction(-2), Fraction(-8)),
        ),
    )
    expected_contractions = (Fraction(336), Fraction(-370))
    observed = []
    for phase_shift in range(2):
        field = _adaptive_seed_field(phase_shift)
        m = _strain_gram_tensor(field)
        j_tensor, pi_tensor, theta_tensor = _dynamic_pressure_tensors(field)
        assert m == expected_matrices[phase_shift]
        assert theta_tensor == expected_theta[phase_shift]
        assert all(
            j_tensor[i][j] == 0 for i in range(3) for j in range(3)
        )
        assert sum(pi_tensor[i][i] for i in range(3)) == 0
        assert sum(theta_tensor[i][i] for i in range(3)) == 0
        forcing = sum(
            m[i][j] * theta_tensor[i][j]
            for i in range(3)
            for j in range(3)
        )
        assert forcing == expected_contractions[phase_shift] != 0

        # Unconstrained H has a minimum Euclidean-speed pressure-work
        # correction.  Here j=0, so Hdot=-2 f M/|M|^2.
        m_norm_squared = sum(
            m[i][j] * m[i][j] for i in range(3) for j in range(3)
        )
        h_dot = tuple(
            tuple(
                -2 * forcing * m[i][j] / m_norm_squared for j in range(3)
            )
            for i in range(3)
        )
        work = Fraction(1, 2) * sum(
            h_dot[i][j] * m[i][j]
            for i in range(3)
            for j in range(3)
        )
        assert work + forcing == 0

        # At H=M, every norm/determinant-preserving Hdot has Hdot:M=0.
        # Since j=0, the nonzero forcing cannot be paid by adot either.
        observed.append(forcing)
    return observed[0], observed[1]


def _pressure_channel_samples() -> List[Dict[Vec, GVec]]:
    vectors = nonzero_vectors(1)
    vector_set = set(vectors)
    samples: List[Dict[Vec, GVec]] = []
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vector_set or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            for polarizations in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                for phase in ((ONE, ONE, ONE), (IMAGINARY_UNIT, ONE, ONE)):
                    samples.append(
                        exact_triad_modes(p, q, r, *polarizations, phase)
                    )
                    if len(samples) == 18:
                        break
                if len(samples) == 18:
                    break
            if len(samples) == 18:
                break
        if len(samples) == 18:
            break
    assert len(samples) == 18
    return samples


def verify_raw_pressure_channel() -> int:
    """Check the full forcing reduction for raw completed representatives."""
    samples = _pressure_channel_samples()

    certificate_rows = [_pressure_channel_row(field) for field in samples]
    assert row_digest(certificate_rows) == EXPECTED_PRESSURE_CHANNEL_DIGEST
    all_real_rows = certificate_rows[::2]
    one_i_rows = certificate_rows[1::2]
    assert all(all(value == 0 for value in row[6:]) for row in all_real_rows)
    assert all(all(value == 0 for value in row[:6]) for row in one_i_rows)
    assert _fractional_rank([row[:6] for row in all_real_rows]) == 5
    assert _fractional_rank([row[6:] for row in one_i_rows]) == 5
    assert _fractional_rank(certificate_rows) == 10
    certificate_minor = [
        [certificate_rows[row][column] for column in PRESSURE_CHANNEL_MINOR_COLUMNS]
        for row in PRESSURE_CHANNEL_MINOR_ROWS
    ]
    assert _fractional_determinant(certificate_minor) == EXPECTED_PRESSURE_CHANNEL_MINOR
    scalar_a = [Fraction(value) for value in (1, 0, 0, 1, 0, 1)] + [Fraction(0)] * 6
    scalar_h = [Fraction(0)] * 6 + [Fraction(value) for value in (1, 0, 0, 1, 0, 1)]
    assert all(
        sum(coefficient * parameter for coefficient, parameter in zip(row, scalar_a)) == 0
        for row in certificate_rows
    )
    assert all(
        sum(coefficient * parameter for coefficient, parameter in zip(row, scalar_h)) == 0
        for row in certificate_rows
    )

    matrices = (
        (
            ((Fraction(1), Fraction(1), Fraction(0)),
             (Fraction(1), Fraction(2), Fraction(1)),
             (Fraction(0), Fraction(1), Fraction(3))),
            ((Fraction(2), Fraction(1), Fraction(0)),
             (Fraction(1), Fraction(3), Fraction(1)),
             (Fraction(0), Fraction(1), Fraction(4))),
        ),
        (
            ((Fraction(1), Fraction(0), Fraction(0)),
             (Fraction(0), Fraction(1), Fraction(0)),
             (Fraction(0), Fraction(0), Fraction(1))),
            ((Fraction(2), Fraction(1), Fraction(0)),
             (Fraction(1), Fraction(3), Fraction(1)),
             (Fraction(0), Fraction(1), Fraction(4))),
        ),
    )
    checks = 0
    for field in samples:
        forcing = _forcing_field(field)
        vorticity = {mode: tensor.omega(mode, value) for mode, value in field.items()}
        dyad = _dyad_convolution(vorticity)
        hessian, strain_square, vorticity_square = _pressure_hessian_and_scalars(field)
        for zeroth, h_matrix in matrices:
            raw = _raw_completed_field(field, zeroth, h_matrix)
            raw_strain = {
                mode: tensor.strain_matrix(mode, value)
                for mode, value in raw.items()
            }
            assert _integral_matrix_product(raw_strain, dyad) == ZERO
            left = _integral_matrix_product(raw_strain, forcing)
            scalar_factor = _add_scalar_fields(
                strain_square,
                vorticity_square,
                left_scale=1,
                right_scale=Fraction(-1, 4),
            )
            right = _integral_scalar_product(
                scalar_factor,
                _divergence_field(raw),
            )
            assert left == (-right[0], -right[1])
            # The pressure-channel identity must use no hidden zero-mode
            assert all(mode != (0, 0, 0) for mode in hessian)
            checks += 1
    return checks


def _adjoint_pressure_row(field: Dict[Vec, GVec]) -> List[Fraction]:
    """Full-forcing row for the adjoint-closed representative."""
    forcing = _forcing_field(field)
    zero = _zero_matrix()
    row: List[Fraction] = []
    for a_matrix in symmetric_matrix_basis():
        closed = _adjoint_closed_field(field, a_matrix, zero)
        strain = {
            mode: tensor.strain_matrix(mode, value)
            for mode, value in closed.items()
        }
        value = _integral_matrix_product(strain, forcing)
        assert value[1] == 0
        row.append(value[0])
    for h_matrix in symmetric_matrix_basis():
        closed = _adjoint_closed_field(field, zero, h_matrix)
        strain = {
            mode: tensor.strain_matrix(mode, value)
            for mode, value in closed.items()
        }
        value = _integral_matrix_product(strain, forcing)
        assert value[1] == 0
        row.append(value[0])
    return row


def verify_adjoint_closed_pressure_work() -> Tuple[int, Fraction, Fraction]:
    """Verify the 12-parameter adjoint-closed pressure-work extension."""
    samples = _pressure_channel_samples()
    basis = symmetric_matrix_basis()
    rows = [_adjoint_pressure_row(field) for field in samples]
    assert len(rows) == 18
    assert all(len(row) == 12 for row in rows)
    assert _fractional_rank(rows) == 10
    minor = [
        [rows[row][column] for column in ADJOINT_PRESSURE_MINOR_COLUMNS]
        for row in ADJOINT_PRESSURE_MINOR_ROWS
    ]
    assert _fractional_determinant(minor) == EXPECTED_ADJOINT_PRESSURE_MINOR

    scalar_a = [Fraction(value) for value in (1, 0, 0, 1, 0, 1)] + [Fraction(0)] * 6
    scalar_h = [Fraction(0)] * 6 + [Fraction(value) for value in (1, 0, 0, 1, 0, 1)]
    assert all(
        sum(coefficient * parameter for coefficient, parameter in zip(row, scalar_a)) == 0
        for row in rows
    )
    assert all(
        sum(coefficient * parameter for coefficient, parameter in zip(row, scalar_h)) == 0
        for row in rows
    )

    # Check the exact Gamma/Pi/Theta reduction and trace identities on every
    # rational cube-triad field used by the existing pressure certificate.
    for field in samples:
        _j_tensor, pi_tensor, theta_tensor = _dynamic_pressure_tensors(field)
        gamma_tensor = _gamma_tensor(field)
        assert gamma_tensor == tuple(
            tuple(gamma_tensor[j][i] for j in range(3))
            for i in range(3)
        )
        assert sum(gamma_tensor[i][i] for i in range(3)) == 0
        assert sum(pi_tensor[i][i] for i in range(3)) == 0
        assert sum(theta_tensor[i][i] for i in range(3)) == 0
        forcing = _forcing_field(field)
        zero = _zero_matrix()
        for a_matrix in basis:
            closed = _adjoint_closed_field(field, a_matrix, zero)
            strain = {
                mode: tensor.strain_matrix(mode, value)
                for mode, value in closed.items()
            }
            left = _integral_matrix_product(strain, forcing)
            expected = (
                _gamma_functional(field, a_matrix) / 8
                - _matrix_inner(a_matrix, pi_tensor) / 2
            )
            assert left == (expected, Fraction(0))
        for h_matrix in basis:
            closed = _adjoint_closed_field(field, zero, h_matrix)
            strain = {
                mode: tensor.strain_matrix(mode, value)
                for mode, value in closed.items()
            }
            left = _integral_matrix_product(strain, forcing)
            expected = -_matrix_inner(h_matrix, theta_tensor)
            assert left == (expected, Fraction(0))

    # The first deterministic state supplies an explicit nonscalar defect.
    defect = _gamma_functional(_adaptive_seed_field(0), basis[0])
    assert defect == Fraction(-12)

    # Verify the corrected J=(K+K^T)/4 normalization and the full local
    # minimum-speed cancellation on an actual exact state.
    field = _adaptive_seed_field(0)
    j_tensor, _pi_tensor, theta_tensor = _dynamic_pressure_tensors(field)
    j_rate = _j_rate_tensor(field)
    assert sum(j_rate[i][i] for i in range(3)) == sum(
        j_tensor[i][i] for i in range(3)
    )
    helical_field = {
        (0, 0, 1): ((Fraction(1), Fraction(0)),
                    (Fraction(0), Fraction(1)),
                    (Fraction(0), Fraction(0))),
        (0, 0, -1): ((Fraction(1), Fraction(0)),
                     (Fraction(0), Fraction(-1)),
                     (Fraction(0), Fraction(0))),
    }
    helical_j = _j_rate_tensor(helical_field)
    assert helical_j == (
        (Fraction(1, 2), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1, 2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    m_tensor = _strain_gram_tensor(field)
    a_matrix = basis[0]
    h_matrix = basis[3]
    gamma = _gamma_functional(field, a_matrix)
    pressure_work = (
        _matrix_inner(a_matrix, _dynamic_pressure_tensors(field)[1]) / 2
        + _matrix_inner(h_matrix, theta_tensor)
        - gamma / 8
    )
    denominator = (
        _matrix_inner(j_rate, j_rate)
        + _matrix_inner(m_tensor, m_tensor) / 4
    )
    assert denominator > 0
    rate_a = tuple(
        tuple(-pressure_work * j_rate[i][j] / denominator for j in range(3))
        for i in range(3)
    )
    rate_h = tuple(
        tuple(-pressure_work * m_tensor[i][j] / (2 * denominator) for j in range(3))
        for i in range(3)
    )
    rate_field = _adjoint_closed_field(field, rate_a, rate_h)
    base_strain = {
        mode: tensor.strain_matrix(mode, value) for mode, value in field.items()
    }
    rate_strain = {
        mode: tensor.strain_matrix(mode, value)
        for mode, value in rate_field.items()
    }
    metric_work = _integral_matrix_product(base_strain, rate_strain)
    assert metric_work[1] == 0
    metric_work_value = metric_work[0] / 2
    assert metric_work_value + pressure_work == 0

    return 10, EXPECTED_ADJOINT_PRESSURE_MINOR, defect


def _joint_pressure_row(field: Dict[Vec, GVec]) -> List[Fraction]:
    """Row for the adaptive-production/adjoint-pressure joint channel."""
    basis = symmetric_matrix_basis()
    strains = adaptive.strain_field(field)
    vorticity = adaptive.curl_field(field)
    q_tensor = adaptive.directional_tensor(strains, vorticity, vorticity)
    production = adaptive.production_tensor(field, strains)
    combined = adaptive.matrix_subtract(
        adaptive.matrix_scale(production, Fraction(2)),
        adaptive.matrix_scale(q_tensor, Fraction(1, 2)),
    )
    _j_tensor, pi_tensor, theta_tensor = _dynamic_pressure_tensors(field)
    gamma_tensor = _gamma_tensor(field)
    hat_pi = adaptive.matrix_subtract(
        adaptive.matrix_scale(pi_tensor, Fraction(1, 2)),
        adaptive.matrix_scale(gamma_tensor, Fraction(1, 8)),
    )
    residual = adaptive.add_rmatrices(
        theta_tensor,
        adaptive.matrix_scale(combined, Fraction(1, 2)),
    )
    return [
        *(_matrix_inner(matrix, hat_pi) for matrix in basis),
        *(_matrix_inner(matrix, residual) for matrix in basis),
    ]


def _matrix_determinant_3x3(
    matrix: Sequence[Sequence[Fraction]],
) -> Fraction:
    """Exact determinant for a 3 by 3 rational matrix."""
    return (
        matrix[0][0] * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1] * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2] * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


def _joint_controller_field() -> Dict[Vec, GVec]:
    """A rational state with both the J and M work directions nonzero."""
    field = _adaptive_seed_field(0)
    field[(0, 0, 2)] = (
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(1)),
        (Fraction(0), Fraction(0)),
    )
    field[(0, 0, -2)] = (
        (Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(-1)),
        (Fraction(0), Fraction(0)),
    )
    return field


def verify_joint_adaptive_adjoint_connection() -> Tuple[int, Fraction, Tuple[Fraction, Fraction]]:
    """Certify the joint minimum-speed connection and its exact obstruction."""
    samples = _pressure_channel_samples()
    for field in samples:
        assert _dynamic_pressure_tensors(field)[0] == _j_rate_tensor(field)
    rows = [_joint_pressure_row(field) for field in samples]
    assert len(rows) == 18
    assert all(len(row) == 12 for row in rows)
    assert row_digest(rows) == EXPECTED_JOINT_PRESSURE_DIGEST
    assert _fractional_rank(rows) == 11
    assert _fractional_rank(rows[::2]) == 5
    assert _fractional_rank(rows[1::2]) == 6
    minor = [
        [rows[row][column] for column in JOINT_PRESSURE_MINOR_COLUMNS]
        for row in JOINT_PRESSURE_MINOR_ROWS
    ]
    assert _fractional_determinant(minor) == EXPECTED_JOINT_PRESSURE_MINOR

    # The scalar curl direction is the exact one-dimensional universal kernel;
    # the second-order metric directions have no universal joint cancellation.
    scalar_a = [Fraction(value) for value in (1, 0, 0, 1, 0, 1)] + [Fraction(0)] * 6
    assert all(
        sum(coefficient * parameter for coefficient, parameter in zip(row, scalar_a)) == 0
        for row in rows
    )
    assert _fractional_rank(rows) == 11

    # Check the two scalar controller equations on a rational state with
    # nonzero J and M.  For g=A:hatPi+H:(Theta+C/2), the minimum-speed rates
    # are Hdot=(H:C)M/|M|^2 and Adot=-g J/|J|^2.
    field = _joint_controller_field()
    strains = adaptive.strain_field(field)
    vorticity = adaptive.curl_field(field)
    m_tensor = adaptive.gram_tensor(strains)
    q_tensor = adaptive.directional_tensor(strains, vorticity, vorticity)
    production = adaptive.production_tensor(field, strains)
    combined = adaptive.matrix_subtract(
        adaptive.matrix_scale(production, Fraction(2)),
        adaptive.matrix_scale(q_tensor, Fraction(1, 2)),
    )
    j_tensor, pi_tensor, theta_tensor = _dynamic_pressure_tensors(field)
    assert j_tensor == _j_rate_tensor(field)
    gamma_tensor = _gamma_tensor(field)
    hat_pi = adaptive.matrix_subtract(
        adaptive.matrix_scale(pi_tensor, Fraction(1, 2)),
        adaptive.matrix_scale(gamma_tensor, Fraction(1, 8)),
    )
    residual = adaptive.add_rmatrices(
        theta_tensor,
        adaptive.matrix_scale(combined, Fraction(1, 2)),
    )
    basis = symmetric_matrix_basis()
    a_matrix = basis[0]
    h_matrix = basis[3]
    h_work = _matrix_inner(h_matrix, combined)
    g_value = _matrix_inner(a_matrix, hat_pi) + _matrix_inner(h_matrix, residual)
    m_norm_squared = _matrix_inner(m_tensor, m_tensor)
    j_norm_squared = _matrix_inner(j_tensor, j_tensor)
    assert m_norm_squared > 0 and j_norm_squared > 0
    h_dot = adaptive.matrix_scale(m_tensor, h_work / m_norm_squared)
    a_dot = adaptive.matrix_scale(j_tensor, -g_value / j_norm_squared)
    assert _matrix_inner(h_dot, m_tensor) == h_work
    assert _matrix_inner(a_dot, j_tensor) == -g_value
    assert (
        _matrix_inner(a_dot, j_tensor)
        + _matrix_inner(h_dot, m_tensor) / 2
        + _matrix_inner(a_matrix, pi_tensor) / 2
        + _matrix_inner(h_matrix, theta_tensor)
        - _gamma_functional(field, a_matrix) / 8
        == 0
    )

    # At the two deterministic seven-mode states, J=0 and H=M.  The adaptive
    # work equation fixes Hdot:M, so the nonzero joint residual is an exact
    # instantaneous obstruction to any A-rate repair.
    expected_joint_residuals = (Fraction(-944), Fraction(305))
    expected_adaptive_work = (Fraction(-2560), Fraction(1350))
    observed = []
    for phase_shift, expected in enumerate(expected_joint_residuals):
        deterministic = _adaptive_seed_field(phase_shift)
        deterministic_strains = adaptive.strain_field(deterministic)
        deterministic_vorticity = adaptive.curl_field(deterministic)
        deterministic_m = adaptive.gram_tensor(deterministic_strains)
        deterministic_q = adaptive.directional_tensor(
            deterministic_strains,
            deterministic_vorticity,
            deterministic_vorticity,
        )
        deterministic_p = adaptive.production_tensor(deterministic, deterministic_strains)
        deterministic_c = adaptive.matrix_subtract(
            adaptive.matrix_scale(deterministic_p, Fraction(2)),
            adaptive.matrix_scale(deterministic_q, Fraction(1, 2)),
        )
        _deterministic_j, _deterministic_pi, deterministic_theta = _dynamic_pressure_tensors(
            deterministic
        )
        assert _deterministic_j == _j_rate_tensor(deterministic)
        deterministic_residual = adaptive.add_rmatrices(
            deterministic_theta,
            adaptive.matrix_scale(deterministic_c, Fraction(1, 2)),
        )
        assert all(
            _deterministic_j[i][j] == 0
            for i in range(3)
            for j in range(3)
        )
        assert _matrix_inner(deterministic_m, deterministic_c) == expected_adaptive_work[phase_shift]
        assert _matrix_inner(deterministic_m, deterministic_residual) == expected
        assert deterministic_m[0][0] > 0
        assert (
            deterministic_m[0][0] * deterministic_m[1][1]
            - deterministic_m[0][1] * deterministic_m[1][0]
        ) == (Fraction(201), Fraction(530))[phase_shift]
        assert _matrix_determinant_3x3(deterministic_m) == (
            Fraction(2442),
            Fraction(5618),
        )[phase_shift]
        observed.append(_matrix_inner(deterministic_m, deterministic_residual))

    return 11, EXPECTED_JOINT_PRESSURE_MINOR, (observed[0], observed[1])


def verify_joint_cone_face_gauge() -> Fraction:
    """Check an exact inward gauge at a regular trace-reversed cone face."""
    field = _joint_controller_field()
    strains = adaptive.strain_field(field)
    m_tensor = adaptive.gram_tensor(strains)
    m_norm_squared = _matrix_inner(m_tensor, m_tensor)
    assert m_norm_squared > 0

    # At a boundary face with null vector e_1, this is the Frobenius
    # projection of e_1 e_1^T to the gauge hyperplane Z_H:M=0.
    rank_one = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    gauge = adaptive.matrix_subtract(
        rank_one,
        adaptive.matrix_scale(m_tensor, m_tensor[0][0] / m_norm_squared),
    )
    assert _matrix_inner(gauge, m_tensor) == 0
    face_leverage = gauge[0][0]
    assert face_leverage == 1 - m_tensor[0][0] ** 2 / m_norm_squared
    assert face_leverage > 0

    # Any prescribed adverse boundary velocity can be reversed without
    # changing either scalar work constraint.  Use -7 as an exact witness.
    adverse_velocity = Fraction(-7)
    scale = Fraction(8) / face_leverage
    assert adverse_velocity + scale * face_leverage == 1
    return face_leverage


def verify_joint_two_face_gauge() -> Fraction:
    """Check dual gauges for two distinct regular cone faces."""
    field = _joint_controller_field()
    m_tensor = adaptive.gram_tensor(adaptive.strain_field(field))
    m_norm_squared = _matrix_inner(m_tensor, m_tensor)
    faces = []
    for index in (0, 1):
        rank_one = tuple(
            tuple(Fraction(i == index and j == index) for j in range(3))
            for i in range(3)
        )
        faces.append(
            adaptive.matrix_subtract(
                rank_one,
                adaptive.matrix_scale(
                    m_tensor, m_tensor[index][index] / m_norm_squared
                ),
            )
        )
    gram = tuple(tuple(_matrix_inner(left, right) for right in faces) for left in faces)
    determinant = gram[0][0] * gram[1][1] - gram[0][1] ** 2
    assert determinant > 0
    dual_first = adaptive.matrix_scale(
        adaptive.matrix_subtract(
            adaptive.matrix_scale(faces[0], gram[1][1]),
            adaptive.matrix_scale(faces[1], gram[0][1]),
        ),
        1 / determinant,
    )
    assert _matrix_inner(dual_first, m_tensor) == 0
    assert dual_first[0][0] == 1
    assert dual_first[1][1] == 0
    return determinant


def verify_joint_degenerate_face_gauge() -> Fraction:
    """Check an inward gauge on a two-dimensional cone nullspace."""
    field = _joint_controller_field()
    m_tensor = adaptive.gram_tensor(adaptive.strain_field(field))
    plane = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    complement = (
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    plane_mass = _matrix_inner(plane, m_tensor)
    complement_mass = _matrix_inner(complement, m_tensor)
    assert plane_mass > 0 and complement_mass > 0
    gauge = adaptive.matrix_subtract(
        plane, adaptive.matrix_scale(complement, plane_mass / complement_mass)
    )
    assert _matrix_inner(gauge, m_tensor) == 0
    assert gauge[0][0] == gauge[1][1] == 1
    assert gauge[0][1] == 0
    return plane_mass / complement_mass


def verify_joint_complementary_face_gauge() -> Fraction:
    """Check a coupled A/H gauge at complementary K+/K- degeneracies."""
    field = _joint_controller_field()
    m_tensor = adaptive.gram_tensor(adaptive.strain_field(field))
    j_tensor, _pi_tensor, _theta_tensor = _dynamic_pressure_tensors(field)
    # K_+=diag(0,0,1), K_-=diag(1,1,0), hence H=I/2 and
    # G(A)=diag(-1/2,-1/2,1/2).  The following gauge has Z_H:M=0
    # and Z_A:J=0 on this exact state.
    h_gauge = (
        (Fraction(-5, 7), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-5, 7), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    a_gauge = (
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(2)),
    )
    assert _matrix_inner(h_gauge, m_tensor) == 0
    assert _matrix_inner(a_gauge, j_tensor) == 0
    # G(A)=((tr A)I-A)/2=diag(1,1,0).
    g_a = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    assert h_gauge[0][0] + g_a[0][0] == Fraction(2, 7)
    assert h_gauge[1][1] + g_a[1][1] == Fraction(2, 7)
    assert h_gauge[2][2] - g_a[2][2] == 1
    return Fraction(2, 7)


def verify_joint_complementary_face_transversality() -> Tuple[int, int]:
    """Certify that even the H-gauge controls all four face normals."""
    field = _joint_controller_field()
    m_tensor = adaptive.gram_tensor(adaptive.strain_field(field))
    j_tensor, _pi_tensor, _theta_tensor = _dynamic_pressure_tensors(field)
    m_norm_squared = _matrix_inner(m_tensor, m_tensor)
    j_norm_squared = _matrix_inner(j_tensor, j_tensor)
    h_images = []
    joint_images = []
    for basis in symmetric_matrix_basis():
        h_gauge = adaptive.matrix_subtract(
            basis,
            adaptive.matrix_scale(
                m_tensor, _matrix_inner(basis, m_tensor) / m_norm_squared
            ),
        )
        h_image = [
            h_gauge[0][0], h_gauge[0][1], h_gauge[1][1], h_gauge[2][2]
        ]
        h_images.append(h_image)
        joint_images.append(h_image)
        a_gauge = adaptive.matrix_subtract(
            basis,
            adaptive.matrix_scale(
                j_tensor, _matrix_inner(basis, j_tensor) / j_norm_squared
            ),
        )
        trace_a = sum(a_gauge[i][i] for i in range(3))
        g_a = tuple(
            tuple(
                (Fraction(trace_a) * Fraction(i == j) - a_gauge[i][j]) / 2
                for j in range(3)
            )
            for i in range(3)
        )
        joint_images.append(
            [g_a[0][0], g_a[0][1], g_a[1][1], -g_a[2][2]]
        )
    h_rank = _fractional_rank(h_images)
    joint_rank = _fractional_rank(joint_images)
    assert h_rank == joint_rank == 4
    # This is the geometric source of H-only surjectivity: M is not block
    # diagonal across the complementary null plane and null line.
    assert (m_tensor[0][2], m_tensor[1][2]) == (Fraction(14), Fraction(14))
    return h_rank, joint_rank


def verify_joint_complementary_resonance() -> int:
    """Exhibit the sharp rank-drop in the abstract complementary normal map."""
    m_tensor = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    j_tensor = (
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    images = []
    for basis in symmetric_matrix_basis():
        h_gauge = adaptive.matrix_subtract(
            basis, adaptive.matrix_scale(m_tensor, _matrix_inner(basis, m_tensor) / 3)
        )
        h_image = [h_gauge[0][0], h_gauge[0][1], h_gauge[1][1], h_gauge[2][2]]
        assert h_image[0] + h_image[2] + h_image[3] == 0
        images.append(h_image)
        a_gauge = adaptive.matrix_subtract(
            basis,
            adaptive.matrix_scale(j_tensor, _matrix_inner(basis, j_tensor)),
        )
        trace_a = sum(a_gauge[i][i] for i in range(3))
        g_a = tuple(
            tuple(
                (Fraction(trace_a) * Fraction(i == j) - a_gauge[i][j]) / 2
                for j in range(3)
            )
            for i in range(3)
        )
        a_image = [g_a[0][0], g_a[0][1], g_a[1][1], -g_a[2][2]]
        assert a_image[0] + a_image[2] + a_image[3] == 0
        images.append(a_image)
    assert _fractional_rank(images) == 3
    return _fractional_rank(images)


def verify_joint_complementary_gauge_cost() -> Fraction:
    """Check the exact minimum-norm H-gauge right inverse at a face."""
    field = _joint_controller_field()
    m_tensor = adaptive.gram_tensor(adaptive.strain_field(field))
    # Target normal velocity: B on span(e1,e2) and b on e3.
    b_plane = ((Fraction(1), Fraction(2)), (Fraction(2), Fraction(-1)))
    b_line = Fraction(3)
    plane_block = ((m_tensor[0][0], m_tensor[0][1]), (m_tensor[1][0], m_tensor[1][1]))
    coupling = (m_tensor[0][2], m_tensor[1][2])
    coupling_norm_squared = sum(value * value for value in coupling)
    assert coupling_norm_squared == 392
    contraction = sum(
        b_plane[i][j] * plane_block[i][j] for i in range(2) for j in range(2)
    ) + b_line * m_tensor[2][2]
    assert contraction == 278
    cross = tuple(-contraction * value / (2 * coupling_norm_squared) for value in coupling)
    assert cross == (Fraction(-139, 28), Fraction(-139, 28))
    gauge = (
        (b_plane[0][0], b_plane[0][1], cross[0]),
        (b_plane[1][0], b_plane[1][1], cross[1]),
        (cross[0], cross[1], b_line),
    )
    assert _matrix_inner(gauge, m_tensor) == 0
    squared_norm = _matrix_inner(gauge, gauge)
    expected = (
        sum(b_plane[i][j] ** 2 for i in range(2) for j in range(2))
        + b_line**2
        + contraction**2 / (2 * coupling_norm_squared)
    )
    assert squared_norm == expected == Fraction(23045, 196)
    return squared_norm


def verify_h_gauge_spectral_alignment_resonance() -> int:
    """Show that distinct Gram eigenvalues do not prevent H-gauge resonance."""
    m_tensor = (
        (Fraction(2), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(3), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(5)),
    )
    # The K_+ null plane is span(e1,e2), K_- null line is span(e3).
    assert m_tensor[0][2] == m_tensor[1][2] == 0
    images = []
    for basis in symmetric_matrix_basis():
        h_gauge = adaptive.matrix_subtract(
            basis,
            adaptive.matrix_scale(m_tensor, _matrix_inner(basis, m_tensor) / 38),
        )
        images.append([h_gauge[0][0], h_gauge[0][1], h_gauge[1][1], h_gauge[2][2]])
    # The common annihilator is 2*d11 + 3*d22 + 5*d33.
    assert all(2 * row[0] + 3 * row[2] + 5 * row[3] == 0 for row in images)
    assert _fractional_rank(images) == 3
    return _fractional_rank(images)


def verify_full_joint_aligned_transversality() -> Tuple[int, int, int]:
    """Certify the full complementary-face iff at a spectral H-resonance."""
    m_tensor = (
        (Fraction(2), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(3), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(5)),
    )
    h_images = []
    for basis in symmetric_matrix_basis():
        h_gauge = adaptive.matrix_subtract(
            basis,
            adaptive.matrix_scale(m_tensor, _matrix_inner(basis, m_tensor) / 38),
        )
        h_images.append([h_gauge[0][0], h_gauge[0][1], h_gauge[1][1], h_gauge[2][2]])
    assert _fractional_rank(h_images) == 3

    def joint_images(j_tensor: RMatrix | None) -> List[List[Fraction]]:
        images = list(h_images)
        norm_squared = (
            _matrix_inner(j_tensor, j_tensor) if j_tensor is not None else Fraction(0)
        )
        for basis in symmetric_matrix_basis():
            if j_tensor is None:
                a_gauge = basis
            else:
                a_gauge = adaptive.matrix_subtract(
                    basis,
                    adaptive.matrix_scale(
                        j_tensor, _matrix_inner(basis, j_tensor) / norm_squared
                    ),
                )
            trace_a = sum(a_gauge[i][i] for i in range(3))
            g_a = tuple(
                tuple(
                    (Fraction(trace_a) * Fraction(i == j) - a_gauge[i][j]) / 2
                    for j in range(3)
                )
                for i in range(3)
            )
            images.append([g_a[0][0], g_a[0][1], g_a[1][1], -g_a[2][2]])
        return images

    generic_j = (
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    # For S=diag(2,3,-5), G(S)=diag(-1,-3/2,5/2).
    resonant_j = (
        (Fraction(-1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(-3, 2), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(5, 2)),
    )
    zero_j_rank = _fractional_rank(joint_images(None))
    generic_rank = _fractional_rank(joint_images(generic_j))
    resonant_images = joint_images(resonant_j)
    resonant_rank = _fractional_rank(resonant_images)
    assert zero_j_rank == generic_rank == 4
    assert resonant_rank == 3
    # The unique target-space annihilator is (diag(2,3), 5).
    assert all(
        2 * row[0] + 3 * row[2] + 5 * row[3] == 0
        for row in resonant_images
    )
    return zero_j_rank, generic_rank, resonant_rank


def main() -> None:
    cases = (
        ("Boolean seed", boolean_seed_vectors(), None),
        ("coordinate box radius 1", nonzero_vectors(1), 1_000_003),
    )
    for label, vectors, prime in cases:
        modes, triads, rows, rank = analyze_vectors(vectors, modular_prime=prime)
        dimension = 12 * modes
        print(
            f"Unrestricted-output {label}: {modes} modes, {triads} triads, "
            f"{rows} rows, rank {rank}/{dimension}, nullity {dimension-rank}"
        )
    modes, rows, kernel_dimension, ranks, determinants = verify_unit_box_certificate()
    print(
        "Unit-box 12-generator certificate: PASS "
        f"({modes} modes, {rows} rows, modular ranks {ranks}, "
        f"explicit kernel dimension {kernel_dimension}, minor residues {determinants})"
    )
    local_checks = verify_raw_local_ranks()
    print(
        "Raw one-triad image-line lemma: PASS "
        f"({local_checks} signed target triads at exact rank 8 and kernel dimension 4)"
    )
    steps, reached = two_triad_propagation()
    print(
        "Two-triad unrestricted-output propagation: PASS "
        f"({steps} target blocks at exact rank 12; {reached} signed modes reached)"
    )
    completion_checks = verify_pressure_completion()
    print(
        "Anisotropic pressure-completion identity: PASS "
        f"({completion_checks} exact mode/polarization checks)"
    )
    pressure_channel_checks = verify_raw_pressure_channel()
    print(
        "Raw completed pressure-channel identity: PASS "
        f"({pressure_channel_checks} exact Fourier forcing checks; "
        "18-field rank 10/12 certificate, scalar kernel)"
    )
    dynamic_obstructions = verify_dynamic_self_adjoint_pressure_work()
    print(
        "Dynamic self-adjoint pressure-work law: PASS "
        f"(exact actual-state two-barrier obstructions {dynamic_obstructions})"
    )
    adjoint_closed = verify_adjoint_closed_pressure_work()
    print(
        "Adjoint-closed 12-parameter pressure-work law: PASS "
        f"(rank/minor/defect {adjoint_closed})"
    )
    joint_connection = verify_joint_adaptive_adjoint_connection()
    print(
        "Joint adaptive/adjoint pressure-production connection: PASS "
        f"(rank/minor/obstructions {joint_connection})"
    )
    helical_checks = verify_adjoint_helical_collapse()
    print(
        "Adjoint-closed helical compression: PASS "
        f"({helical_checks} exact plane-anticommutator checks; "
        "strict coercive-cone improvement)"
    )
    cone_leverage = verify_joint_cone_face_gauge()
    print(
        "Joint cone-face gauge: PASS "
        f"(exact inward leverage {cone_leverage})"
    )
    two_face_determinant = verify_joint_two_face_gauge()
    print(
        "Joint two-face gauge: PASS "
        f"(projected-normal Gram determinant {two_face_determinant})"
    )
    degenerate_ratio = verify_joint_degenerate_face_gauge()
    print(
        "Joint degenerate-face gauge: PASS "
        f"(plane/complement mass ratio {degenerate_ratio})"
    )
    complementary_margin = verify_joint_complementary_face_gauge()
    print(
        "Joint complementary-face gauge: PASS "
        f"(simultaneous inward margin {complementary_margin})"
    )
    h_normal_rank, joint_normal_rank = (
        verify_joint_complementary_face_transversality()
    )
    print(
        "Joint complementary-face transversality: PASS "
        f"(H-only/joint normal-map ranks "
        f"{h_normal_rank}/4, {joint_normal_rank}/4)"
    )
    resonance_rank = verify_joint_complementary_resonance()
    print(
        "Joint complementary-face resonance: PASS "
        f"(abstract normal-map rank {resonance_rank}/4)"
    )
    gauge_cost = verify_joint_complementary_gauge_cost()
    print(
        "Joint complementary-face gauge cost: PASS "
        f"(exact squared minimum norm {gauge_cost})"
    )
    spectral_resonance_rank = verify_h_gauge_spectral_alignment_resonance()
    print(
        "H-gauge spectral-alignment resonance: PASS "
        f"(distinct-spectrum H-normal-map rank {spectral_resonance_rank}/4)"
    )
    zero_j_rank, generic_joint_rank, aligned_joint_rank = (
        verify_full_joint_aligned_transversality()
    )
    print(
        "Full joint aligned-face transversality: PASS "
        f"(J=0/generic/resonant ranks {zero_j_rank}/4, "
        f"{generic_joint_rank}/4, {aligned_joint_rank}/4)"
    )


if __name__ == "__main__":
    main()
