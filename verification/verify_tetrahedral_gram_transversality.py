#!/usr/bin/env python3
"""Exact tetrahedral atlas checks for Gram plane--line transversality."""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations, permutations, product


RMatrix = tuple[tuple[Fraction, Fraction, Fraction], ...]
Sign = tuple[int, int, int]
Vector = tuple[int, int, int]

TETRAHEDRAL_SIGNS: tuple[Sign, ...] = (
    (1, 1, 1),
    (1, -1, -1),
    (-1, 1, -1),
    (-1, -1, 1),
)


def matrix_inner(left: RMatrix, right: RMatrix) -> Fraction:
    return sum(left[i][j] * right[i][j] for i in range(3) for j in range(3))


def determinant(matrix: RMatrix) -> Fraction:
    return (
        matrix[0][0]
        * (matrix[1][1] * matrix[2][2] - matrix[1][2] * matrix[2][1])
        - matrix[0][1]
        * (matrix[1][0] * matrix[2][2] - matrix[1][2] * matrix[2][0])
        + matrix[0][2]
        * (matrix[1][0] * matrix[2][1] - matrix[1][1] * matrix[2][0])
    )


def exact_determinant(matrix: list[list[Fraction]]) -> Fraction:
    """Determinant of a square rational matrix by exact elimination."""
    work = [row[:] for row in matrix]
    value = Fraction(1)
    for column in range(len(work)):
        pivot = next(
            (index for index in range(column, len(work)) if work[index][column]),
            None,
        )
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            value = -value
        pivot_value = work[column][column]
        value *= pivot_value
        for index in range(column + 1, len(work)):
            factor = work[index][column] / pivot_value
            for inner_column in range(column + 1, len(work)):
                work[index][inner_column] -= factor * work[column][inner_column]
    return value


def matrix_add(left: RMatrix, right: RMatrix) -> RMatrix:
    return tuple(
        tuple(left[i][j] + right[i][j] for j in range(3)) for i in range(3)
    )


def matrix_scale(matrix: RMatrix, scalar: Fraction) -> RMatrix:
    return tuple(
        tuple(scalar * matrix[i][j] for j in range(3)) for i in range(3)
    )


def matrix_subtract(left: RMatrix, right: RMatrix) -> RMatrix:
    return matrix_add(left, matrix_scale(right, Fraction(-1)))


def flatten(matrix: RMatrix) -> list[Fraction]:
    return [matrix[i][j] for i in range(3) for j in range(3)]


def trace_reverse(matrix: RMatrix) -> RMatrix:
    trace = sum(matrix[i][i] for i in range(3))
    return tuple(
        tuple((trace * Fraction(i == j) - matrix[i][j]) / 2 for j in range(3))
        for i in range(3)
    )


def tetrahedral_projector(sign: Sign) -> RMatrix:
    return tuple(
        tuple(Fraction(sign[i] * sign[j], 3) for j in range(3))
        for i in range(3)
    )


def symmetric_matrix(entries: tuple[int, int, int, int, int, int]) -> RMatrix:
    """Return [[a,d,e],[d,b,f],[e,f,c]] from exact integer entries."""
    a, d, e, b, f, c = (Fraction(value) for value in entries)
    return ((a, d, e), (d, b, f), (e, f, c))


def symmetric_basis() -> tuple[RMatrix, ...]:
    """Standard six-element Frobenius basis of Sym(3)."""
    return tuple(
        tuple(
            tuple(
                Fraction(
                    (row == left and column == right)
                    or (row == right and column == left)
                )
                for column in range(3)
            )
            for row in range(3)
        )
        for left, right in ((0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2))
    )


def exact_rank(rows: list[list[Fraction]]) -> int:
    work = [row[:] for row in rows]
    if not work:
        return 0
    rank = 0
    for column in range(len(work[0])):
        pivot = next(
            (index for index in range(rank, len(work)) if work[index][column]),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        pivot_value = work[rank][column]
        work[rank] = [value / pivot_value for value in work[rank]]
        for index in range(len(work)):
            if index == rank or not work[index][column]:
                continue
            factor = work[index][column]
            work[index] = [
                value - factor * pivot_entry
                for value, pivot_entry in zip(work[index], work[rank])
            ]
        rank += 1
    return rank


def coordinate_joint_normal_rank(
    gram: RMatrix, dual: RMatrix, line_index: int
) -> int:
    """Rank of the full H/A normal map for a coordinate plane--line split."""
    plane = tuple(index for index in range(3) if index != line_index)
    gram_norm_squared = matrix_inner(gram, gram)
    dual_norm_squared = matrix_inner(dual, dual)
    images: list[list[Fraction]] = []

    for basis in symmetric_basis():
        h_gauge = (
            basis
            if not gram_norm_squared
            else matrix_subtract(
                basis,
                matrix_scale(
                    gram, matrix_inner(basis, gram) / gram_norm_squared
                ),
            )
        )
        images.append(
            [
                h_gauge[plane[0]][plane[0]],
                h_gauge[plane[0]][plane[1]],
                h_gauge[plane[1]][plane[1]],
                h_gauge[line_index][line_index],
            ]
        )

    for basis in symmetric_basis():
        a_gauge = (
            basis
            if not dual_norm_squared
            else matrix_subtract(
                basis,
                matrix_scale(
                    dual, matrix_inner(basis, dual) / dual_norm_squared
                ),
            )
        )
        reversed_gauge = trace_reverse(a_gauge)
        images.append(
            [
                reversed_gauge[plane[0]][plane[0]],
                reversed_gauge[plane[0]][plane[1]],
                reversed_gauge[plane[1]][plane[1]],
                -reversed_gauge[line_index][line_index],
            ]
        )
    return exact_rank(images)


def coupling_squared(matrix: RMatrix, sign: Sign) -> Fraction:
    """Squared norm of (I-ff^T)Mf for f=sign/sqrt(3)."""
    return projective_coupling_squared(matrix, sign)


def projective_coupling_squared(matrix: RMatrix, vector: Vector) -> Fraction:
    """Squared coupling for the unit line represented by ``vector``."""
    image = tuple(
        sum(matrix[i][j] * vector[j] for j in range(3)) for i in range(3)
    )
    norm_squared = sum(value * value for value in vector)
    rayleigh_numerator = sum(vector[i] * image[i] for i in range(3))
    return (
        sum(value * value for value in image) / norm_squared
        - rayleigh_numerator**2 / norm_squared**2
    )


def coupling_inner(left: RMatrix, right: RMatrix, sign: Sign) -> Fraction:
    """Polarization of ``coupling_squared`` in its matrix argument."""
    left_image = tuple(
        sum(left[i][j] * sign[j] for j in range(3)) for i in range(3)
    )
    right_image = tuple(
        sum(right[i][j] * sign[j] for j in range(3)) for i in range(3)
    )
    left_rayleigh = sum(sign[i] * left_image[i] for i in range(3))
    right_rayleigh = sum(sign[i] * right_image[i] for i in range(3))
    return (
        sum(left_image[i] * right_image[i] for i in range(3)) / 3
        - left_rayleigh * right_rayleigh / 9
    )


def distance_to_span_squared(matrix: RMatrix, direction: RMatrix) -> Fraction:
    direction_norm_squared = matrix_inner(direction, direction)
    if not direction_norm_squared:
        return matrix_inner(matrix, matrix)
    return (
        matrix_inner(matrix, matrix)
        - matrix_inner(matrix, direction) ** 2 / direction_norm_squared
    )


def polynomial_add(
    left: list[Fraction], right: list[Fraction]
) -> list[Fraction]:
    result = [Fraction(0)] * max(len(left), len(right))
    for index, value in enumerate(left):
        result[index] += value
    for index, value in enumerate(right):
        result[index] += value
    return result


def polynomial_multiply(
    left: list[Fraction], right: list[Fraction]
) -> list[Fraction]:
    result = [Fraction(0)] * (len(left) + len(right) - 1)
    for left_index, left_value in enumerate(left):
        for right_index, right_value in enumerate(right):
            result[left_index + right_index] += left_value * right_value
    return result


def traceless_symmetric_basis() -> tuple[RMatrix, ...]:
    return (
        ((Fraction(1), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(-1), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0))),
        ((Fraction(1), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(1), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(-2))),
        ((Fraction(0), Fraction(1), Fraction(0)),
         (Fraction(1), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0))),
        ((Fraction(0), Fraction(0), Fraction(1)),
         (Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(1), Fraction(0), Fraction(0))),
        ((Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(1)),
         (Fraction(0), Fraction(1), Fraction(0))),
    )


def check_tetrahedral_decomposition() -> int:
    basis = traceless_symmetric_basis()
    checks = 0
    zero = matrix_scale(basis[0], Fraction(0))
    for coefficients in product(range(-2, 3), repeat=len(basis)):
        matrix = zero
        for coefficient, direction in zip(coefficients, basis):
            matrix = matrix_add(matrix, matrix_scale(direction, Fraction(coefficient)))
        diagonal_part = tuple(
            tuple(matrix[i][j] if i == j else Fraction(0) for j in range(3))
            for i in range(3)
        )
        off_diagonal_part = tuple(
            tuple(matrix[i][j] if i != j else Fraction(0) for j in range(3))
            for i in range(3)
        )
        couplings = [
            coupling_squared(matrix, sign) for sign in TETRAHEDRAL_SIGNS
        ]
        assert sum(couplings) == (
            Fraction(4, 3) * matrix_inner(diagonal_part, diagonal_part)
            + Fraction(4, 9) * matrix_inner(off_diagonal_part, off_diagonal_part)
        )
        norm_squared = matrix_inner(matrix, matrix)
        if norm_squared:
            assert max(couplings) >= norm_squared / 9
        else:
            assert couplings == [Fraction(0)] * 4
        checks += 1

    # A pure off-diagonal direction attains the universal 1/9 constant.
    sharp_matrix = basis[2]
    assert max(coupling_squared(sharp_matrix, sign) for sign in TETRAHEDRAL_SIGNS) == (
        matrix_inner(sharp_matrix, sharp_matrix) / 9
    )
    return checks


def check_three_chart_coupling_spectrum() -> tuple[int, int]:
    """Certify the sharp coupling-frame spectrum for every tetrahedral triple."""
    traceless_basis: tuple[RMatrix, ...] = (
        symmetric_matrix((1, 0, 0, 0, 0, -1)),
        symmetric_matrix((0, 0, 0, 1, 0, -1)),
        symmetric_matrix((0, 1, 0, 0, 0, 0)),
        symmetric_matrix((0, 0, 1, 0, 0, 0)),
        symmetric_matrix((0, 0, 0, 0, 1, 0)),
    )
    norm_matrix = [
        [matrix_inner(left, right) for right in traceless_basis]
        for left in traceless_basis
    ]
    expected_characteristic = polynomial_multiply(
        [Fraction(-4), Fraction(9)],
        polynomial_multiply(
            [Fraction(4), Fraction(-23), Fraction(18)],
            [Fraction(4), Fraction(-23), Fraction(18)],
        ),
    )
    expected_characteristic = [
        Fraction(-2, 243) * value for value in expected_characteristic
    ]
    triple_checks = 0
    for indices in combinations(range(4), 3):
        coupling_matrix = [
            [
                sum(
                    coupling_inner(left, right, TETRAHEDRAL_SIGNS[index])
                    for index in indices
                )
                for right in traceless_basis
            ]
            for left in traceless_basis
        ]

        # Compute det(A-tN) directly as a polynomial (coefficients low to high).
        characteristic = [Fraction(0)]
        for ordering in permutations(range(5)):
            inversions = sum(
                ordering[left] > ordering[right]
                for left in range(5)
                for right in range(left + 1, 5)
            )
            term = [Fraction(-1 if inversions % 2 else 1)]
            for row, column in enumerate(ordering):
                term = polynomial_multiply(
                    term,
                    [coupling_matrix[row][column], -norm_matrix[row][column]],
                )
            characteristic = polynomial_add(characteristic, term)
        assert characteristic == expected_characteristic

        # A simple rational consequence of the sharp least eigenvalue
        # (23-sqrt(241))/36 is the coercive estimate A >= N/5.
        shifted = [
            [
                coupling_matrix[row][column]
                - Fraction(1, 5) * norm_matrix[row][column]
                for column in range(5)
            ]
            for row in range(5)
        ]
        assert all(
            exact_determinant([row[:size] for row in shifted[:size]]) > 0
            for size in range(1, 6)
        )
        triple_checks += 1

    projectors = [tetrahedral_projector(sign) for sign in TETRAHEDRAL_SIGNS[:3]]
    projector_gram = [
        [matrix_inner(left, right) for right in projectors] for left in projectors
    ]
    assert all(projector_gram[index][index] == 1 for index in range(3))
    assert all(
        projector_gram[left][right] == Fraction(1, 9)
        for left in range(3)
        for right in range(3)
        if left != right
    )
    assert all(sum(row) == Fraction(11, 9) for row in projector_gram)
    return triple_checks, len(projector_gram)


def check_orthogonal_boundary_collapse() -> int:
    """Exhibit loss of any trace-scale gap for an orthogonal three-chart atlas."""
    rank_one_gram = symmetric_matrix((1, 0, 0, 0, 0, 0))
    limiting_dual = trace_reverse(rank_one_gram)
    assert [
        coordinate_joint_normal_rank(rank_one_gram, limiting_dual, line_index)
        for line_index in range(3)
    ] == [3, 3, 3]

    checks = 0
    coordinate_projectors = tuple(
        symmetric_matrix(
            tuple(1 if entry == diagonal else 0 for entry in range(6))
        )
        for diagonal in (0, 3, 5)
    )
    identity = symmetric_matrix((1, 0, 0, 1, 0, 1))
    for epsilon in (Fraction(1, 2), Fraction(1, 5), Fraction(1, 10)):
        gram = matrix_add(rank_one_gram, matrix_scale(identity, epsilon))
        discriminants = []
        for projector in coordinate_projectors:
            rayleigh = matrix_inner(gram, projector)
            resonance = trace_reverse(
                matrix_subtract(gram, matrix_scale(projector, 2 * rayleigh))
            )
            discriminants.append(
                distance_to_span_squared(resonance, limiting_dual)
            )
        assert discriminants == [epsilon**2, epsilon**2 / 2, epsilon**2 / 2]
        checks += 1
    return checks


def common_eigen_constraint_rank(vectors: tuple[Vector, ...]) -> tuple[int, int]:
    symmetric_basis: tuple[RMatrix, ...] = (
        ((Fraction(1), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0))),
        ((Fraction(0), Fraction(1), Fraction(0)),
         (Fraction(1), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0))),
        ((Fraction(0), Fraction(0), Fraction(1)),
         (Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(1), Fraction(0), Fraction(0))),
        ((Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(1), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0))),
        ((Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(1)),
         (Fraction(0), Fraction(1), Fraction(0))),
        ((Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(0)),
         (Fraction(0), Fraction(0), Fraction(1))),
    )
    rows: list[list[Fraction]] = []
    for vector in vectors:
        for left, right in ((0, 1), (0, 2), (1, 2)):
            row = []
            for matrix in symmetric_basis:
                image = tuple(
                    sum(matrix[i][j] * vector[j] for j in range(3))
                    for i in range(3)
                )
                row.append(vector[left] * image[right] - vector[right] * image[left])
            rows.append(row)
    scalar = (
        Fraction(1), Fraction(0), Fraction(0),
        Fraction(1), Fraction(0), Fraction(1),
    )
    assert all(
        sum(entry * value for entry, value in zip(row, scalar)) == 0
        for row in rows
    )
    return exact_rank(rows), len(rows)


def check_isotropic_kernel() -> int:
    rank, row_count = common_eigen_constraint_rank(TETRAHEDRAL_SIGNS)
    assert rank == 5
    return row_count


def check_isotropic_joint_atlas() -> tuple[int, int, int]:
    identity: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    projectors = [tetrahedral_projector(sign) for sign in TETRAHEDRAL_SIGNS]
    for projector in projectors:
        # At M=I the aligned-face dual resonance tensor is exactly ff^T.
        signed_split = matrix_subtract(
            identity, matrix_scale(projector, Fraction(2))
        )
        assert trace_reverse(signed_split) == projector
        assert matrix_inner(projector, projector) == 1

    pair_checks = 0
    for left in range(len(projectors)):
        for right in range(left):
            # Distinct tetrahedral resonance rays have angle cos^{-1}(1/9)
            # in Sym(3), so a nonzero J can lie on at most one of them.
            assert matrix_inner(projectors[left], projectors[right]) == Fraction(1, 9)
            pair_checks += 1

    # The projector rays form a bounded frame: a dual tensor can be close to
    # at most three of them.  This gives a 2/3 squared-distance escape at
    # every scalar Gram matrix.
    direction_checks = 0
    for entries in product(range(-2, 3), repeat=6):
        dual = symmetric_matrix(entries)
        dual_norm_squared = matrix_inner(dual, dual)
        if not dual_norm_squared:
            continue
        correlations = [matrix_inner(projector, dual) for projector in projectors]
        assert sum(value * value for value in correlations) <= (
            Fraction(4, 3) * dual_norm_squared
        )
        distances = [
            Fraction(1) - value * value / dual_norm_squared
            for value in correlations
        ]
        assert max(distances) >= Fraction(2, 3)
        direction_checks += 1

    # The two mechanisms splice into a global four-chart lower bound on the
    # joint discriminant: max_alpha Delta_alpha >= (tr(M)/3)^2 / 24.
    # These exact SPD samples exercise both the near-isotropic and anisotropic
    # sides of the proof against every small integral dual tensor.
    gram_matrices: tuple[RMatrix, ...] = (
        symmetric_matrix((1, 0, 0, 1, 0, 1)),
        symmetric_matrix((2, 0, 0, 3, 0, 5)),
        symmetric_matrix((4, 1, 1, 3, 0, 2)),
        symmetric_matrix((5, -1, 0, 4, 1, 3)),
    )
    discriminant_checks = 0
    for gram in gram_matrices:
        assert gram[0][0] > 0
        assert gram[0][0] * gram[1][1] - gram[0][1] ** 2 > 0
        assert determinant(gram) > 0
        mean = sum(gram[index][index] for index in range(3)) / 3
        zero_dual_discriminants = []
        for sign, projector in zip(TETRAHEDRAL_SIGNS, projectors):
            rayleigh = matrix_inner(gram, projector)
            resonance = trace_reverse(
                matrix_subtract(gram, matrix_scale(projector, 2 * rayleigh))
            )
            zero_dual_discriminants.append(
                coupling_squared(gram, sign) + matrix_inner(resonance, resonance)
            )
        assert max(zero_dual_discriminants) >= mean * mean / 24
        assert max(zero_dual_discriminants[:3]) >= Fraction(9, 400) * mean * mean
        discriminant_checks += 1
        for entries in product(range(-1, 2), repeat=6):
            dual = symmetric_matrix(entries)
            dual_norm_squared = matrix_inner(dual, dual)
            if not dual_norm_squared:
                continue
            discriminants = []
            for sign, projector in zip(TETRAHEDRAL_SIGNS, projectors):
                rayleigh = matrix_inner(gram, projector)
                resonance = trace_reverse(
                    matrix_subtract(gram, matrix_scale(projector, 2 * rayleigh))
                )
                distance_squared = (
                    matrix_inner(resonance, resonance)
                    - matrix_inner(resonance, dual) ** 2 / dual_norm_squared
                )
                discriminants.append(coupling_squared(gram, sign) + distance_squared)
            assert max(discriminants) >= mean * mean / 24
            assert max(discriminants[:3]) >= Fraction(9, 400) * mean * mean
            discriminant_checks += 1
    return pair_checks, direction_checks, discriminant_checks


def check_unique_joint_resonance_axis() -> int:
    # For every symmetric positive-definite Gram matrix, distinct eigenlines
    # have distinct projective resonance tensors R_{M,f}.  These exact samples
    # include simple, repeated, and fully isotropic spectra.
    states: tuple[tuple[RMatrix, tuple[RMatrix, ...]], ...] = (
        (
            symmetric_matrix((2, 0, 0, 3, 0, 5)),
            (
                symmetric_matrix((1, 0, 0, 0, 0, 0)),
                symmetric_matrix((0, 0, 0, 1, 0, 0)),
                symmetric_matrix((0, 0, 0, 0, 0, 1)),
            ),
        ),
        (
            symmetric_matrix((2, 0, 0, 2, 0, 5)),
            (
                symmetric_matrix((1, 0, 0, 0, 0, 0)),
                symmetric_matrix((0, 0, 0, 1, 0, 0)),
                symmetric_matrix((Fraction(1, 2), Fraction(1, 2), 0,
                                  Fraction(1, 2), 0, 0)),
                symmetric_matrix((0, 0, 0, 0, 0, 1)),
            ),
        ),
        (
            symmetric_matrix((1, 0, 0, 1, 0, 1)),
            tuple(tetrahedral_projector(sign) for sign in TETRAHEDRAL_SIGNS),
        ),
    )
    pair_checks = 0
    for gram, eigenprojectors in states:
        resonance_tensors = []
        for projector in eigenprojectors:
            eigenvalue = matrix_inner(gram, projector)
            resonance_tensors.append(
                trace_reverse(
                    matrix_subtract(gram, matrix_scale(projector, 2 * eigenvalue))
                )
            )
        for left in range(len(resonance_tensors)):
            for right in range(left):
                assert exact_rank(
                    [flatten(resonance_tensors[left]), flatten(resonance_tensors[right])]
                ) == 2
                pair_checks += 1
    return pair_checks


def check_minimal_uniform_atlas_cardinality() -> tuple[int, int, int, int]:
    triple = TETRAHEDRAL_SIGNS[:3]
    rank, _ = common_eigen_constraint_rank(triple)
    # Three spanning, pairwise nonorthogonal tetrahedral lines can have a
    # common eigenvalue only at a scalar Gram matrix.
    assert rank == 5

    # The exact three-chart coupling pencil gives the stronger estimate
    # max_i |q_i|^2 >= |S|^2 / 15; retain the component reconstruction as an
    # independent rational check of a weaker bound.
    coupling_bound_checks = 0
    traceless_basis = traceless_symmetric_basis()
    zero = matrix_scale(traceless_basis[0], Fraction(0))
    for coefficients in product(range(-2, 3), repeat=len(traceless_basis)):
        strain = zero
        for coefficient, direction in zip(coefficients, traceless_basis):
            strain = matrix_add(strain, matrix_scale(direction, Fraction(coefficient)))
        cross_components: list[Fraction] = []
        for sign in triple:
            image = tuple(
                sum(strain[i][j] * sign[j] for j in range(3)) for i in range(3)
            )
            cross_components.extend(
                (
                    sign[1] * image[2] - sign[2] * image[1],
                    sign[2] * image[0] - sign[0] * image[2],
                    sign[0] * image[1] - sign[1] * image[0],
                )
            )
        component_bound = max(abs(value) for value in cross_components)
        strain_norm_squared = matrix_inner(strain, strain)
        assert strain_norm_squared <= Fraction(79, 2) * component_bound**2
        assert max(coupling_squared(strain, sign) for sign in triple) >= (
            Fraction(1, 15) * strain_norm_squared
        )
        coupling_bound_checks += 1

    # Conversely every two directions have a common normal line u.  The
    # rank-one boundary Gram uu^T makes both charts resonant with the same
    # dual ray.  Positive-definite perturbations retain zero H coupling and
    # force their joint discriminants to O(epsilon^2).
    left, right = triple[:2]
    normal = (
        left[1] * right[2] - left[2] * right[1],
        left[2] * right[0] - left[0] * right[2],
        left[0] * right[1] - left[1] * right[0],
    )
    normal_norm_squared = sum(value * value for value in normal)
    normal_projector: RMatrix = tuple(
        tuple(Fraction(normal[i] * normal[j], normal_norm_squared) for j in range(3))
        for i in range(3)
    )
    identity: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    boundary_dual = trace_reverse(normal_projector)
    perturbation_checks = 0
    for epsilon in (Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(1, 16)):
        gram = matrix_add(normal_projector, matrix_scale(identity, epsilon))
        for sign in (left, right):
            projector = tetrahedral_projector(sign)
            assert coupling_squared(gram, sign) == 0
            eigenvalue = matrix_inner(gram, projector)
            resonance = trace_reverse(
                matrix_subtract(gram, matrix_scale(projector, 2 * eigenvalue))
            )
            distance_squared = (
                matrix_inner(resonance, resonance)
                - matrix_inner(resonance, boundary_dual) ** 2
                / matrix_inner(boundary_dual, boundary_dual)
            )
            assert distance_squared <= epsilon * epsilon
            perturbation_checks += 1

    # Strict positivity is essential for the two-chart rank theorem itself:
    # on a rank-two boundary Gram matrix two coordinate splittings share the
    # same resonance line and both normal maps have rank three.
    boundary_gram = symmetric_matrix((1, 0, 0, 1, 0, 0))
    boundary_dual_coordinate = symmetric_matrix((Fraction(1, 2), 0, 0, Fraction(-1, 2), 0, 0))
    assert coordinate_joint_normal_rank(boundary_gram, boundary_dual_coordinate, 0) == 3
    assert coordinate_joint_normal_rank(boundary_gram, boundary_dual_coordinate, 1) == 3

    # The first three tetrahedral directions already have the explicit
    # scale-covariant selection bound max Delta >= 9(tr(M)/3)^2 / 400.
    # These exact samples cover the scalar, diagonal, and coupled regimes
    # against every small integral dual tensor, including J=0.
    gram_matrices: tuple[RMatrix, ...] = (
        symmetric_matrix((1, 0, 0, 1, 0, 1)),
        symmetric_matrix((2, 0, 0, 3, 0, 5)),
        symmetric_matrix((4, 1, 1, 3, 0, 2)),
    )
    triple_projectors = [tetrahedral_projector(sign) for sign in triple]
    explicit_bound_checks = 0
    for gram in gram_matrices:
        mean = sum(gram[index][index] for index in range(3)) / 3
        for entries in product(range(-1, 2), repeat=6):
            dual = symmetric_matrix(entries)
            dual_norm_squared = matrix_inner(dual, dual)
            discriminants = []
            for sign, projector in zip(triple, triple_projectors):
                eigenvalue = matrix_inner(gram, projector)
                resonance = trace_reverse(
                    matrix_subtract(gram, matrix_scale(projector, 2 * eigenvalue))
                )
                distance_squared = matrix_inner(resonance, resonance)
                if dual_norm_squared:
                    distance_squared -= (
                        matrix_inner(resonance, dual) ** 2 / dual_norm_squared
                    )
                discriminants.append(coupling_squared(gram, sign) + distance_squared)
            assert max(discriminants) >= Fraction(9, 400) * mean * mean
            explicit_bound_checks += 1
    return rank, coupling_bound_checks, perturbation_checks, explicit_bound_checks


def check_three_chart_admissibility_geometry() -> int:
    # Pairwise nonorthogonality is sufficient but not necessary.  This
    # spanning triple has e1 perpendicular to e2, yet no direction is
    # perpendicular to both of the other two; its common-eigen kernel is
    # still only the scalar matrices.
    admissible: tuple[Vector, ...] = (
        (1, 0, 0),
        (0, 1, 0),
        (1, 1, 1),
    )
    admissible_rank, _ = common_eigen_constraint_rank(admissible)
    assert admissible_rank == 5

    # Failure of spanning gives a rank-one Gram normal to the common plane.
    # The nonorthogonality graph here is connected, isolating span failure.
    coplanar: tuple[Vector, ...] = (
        (1, 0, 0),
        (1, 1, 0),
        (1, -1, 0),
    )
    coplanar_rank, _ = common_eigen_constraint_rank(coplanar)
    assert coplanar_rank == 4
    normal_gram = symmetric_matrix((0, 0, 0, 0, 0, 1))
    limiting_dual = trace_reverse(normal_gram)
    for vector in coplanar:
        norm_squared = sum(value * value for value in vector)
        projector: RMatrix = tuple(
            tuple(Fraction(vector[i] * vector[j], norm_squared) for j in range(3))
            for i in range(3)
        )
        eigenvalue = matrix_inner(normal_gram, projector)
        assert eigenvalue == 0
        assert trace_reverse(
            matrix_subtract(normal_gram, matrix_scale(projector, 2 * eigenvalue))
        ) == limiting_dual

    # A spanning triple can still fail when its nonorthogonality graph is
    # disconnected.  Here e3 is isolated from a connected pair in e3^perp;
    # the common-eigen kernel contains the two-eigenvalue axisymmetric family.
    disconnected: tuple[Vector, ...] = (
        (1, 0, 0),
        (1, 1, 0),
        (0, 0, 1),
    )
    disconnected_rank, _ = common_eigen_constraint_rank(disconnected)
    assert disconnected_rank == 4
    for vector in disconnected:
        norm_squared = sum(value * value for value in vector)
        projector = tuple(
            tuple(Fraction(vector[i] * vector[j], norm_squared) for j in range(3))
            for i in range(3)
        )
        assert projective_coupling_squared(normal_gram, vector) == 0
        eigenvalue = matrix_inner(normal_gram, projector)
        resonance = trace_reverse(
            matrix_subtract(normal_gram, matrix_scale(projector, 2 * eigenvalue))
        )
        assert exact_rank([flatten(resonance), flatten(limiting_dual)]) == 1
    return admissible_rank


def main() -> None:
    decomposition_checks = check_tetrahedral_decomposition()
    print(
        "Tetrahedral Gram coupling decomposition: PASS "
        f"({decomposition_checks} exact traceless matrices; sharp constant 1/9)"
    )
    triple_checks, projector_checks = check_three_chart_coupling_spectrum()
    print(
        "Three-chart tetrahedral frame: PASS "
        f"({triple_checks} coupling pencils; {projector_checks} projector rows)"
    )
    kernel_rows = check_isotropic_kernel()
    print(
        "Tetrahedral atlas isotropic kernel: PASS "
        f"({kernel_rows} rows; rank 5/6)"
    )
    pair_checks, direction_checks, discriminant_checks = check_isotropic_joint_atlas()
    print(
        "Tetrahedral isotropic joint atlas: PASS "
        f"({pair_checks} separated pairs; {direction_checks} dual-frame checks)"
    )
    print(
        "Tetrahedral global joint atlas: PASS "
        f"({discriminant_checks} exact discriminant checks; constants 1/24 and 9/400)"
    )
    unique_pairs = check_unique_joint_resonance_axis()
    print(
        "Unique joint resonance axis: PASS "
        f"({unique_pairs} distinct eigenline-ray pairs)"
    )
    boundary_checks = check_orthogonal_boundary_collapse()
    print(
        "Orthogonal atlas boundary collapse: PASS "
        f"({boundary_checks} positive-definite degenerating states)"
    )
    triple_rank, coupling_bound_checks, pair_degenerations, triple_bound_checks = (
        check_minimal_uniform_atlas_cardinality()
    )
    print(
        "Minimal uniform joint atlas: PASS "
        f"(three-chart common-eigen rank {triple_rank}/6; "
        f"{coupling_bound_checks} exact H-coupling bounds; "
        f"{pair_degenerations} two-chart degenerations; "
        f"{triple_bound_checks} explicit 9/400 checks)"
    )
    admissible_rank = check_three_chart_admissibility_geometry()
    print(
        "Three-chart admissibility geometry: PASS "
        f"(mixed triple common-eigen rank {admissible_rank}/6)"
    )
    print("All exact tetrahedral Gram-transversality checks passed.")


if __name__ == "__main__":
    main()
