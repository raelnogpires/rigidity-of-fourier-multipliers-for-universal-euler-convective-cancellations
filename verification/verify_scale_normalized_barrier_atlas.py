#!/usr/bin/env python3
"""Exact checks for the scale-normalized adaptive metric barrier atlas."""

from __future__ import annotations

from fractions import Fraction


RMatrix = tuple[tuple[Fraction, Fraction, Fraction], ...]


def matrix(entries: tuple[int | Fraction, int | Fraction, int | Fraction,
                          int | Fraction, int | Fraction, int | Fraction]) -> RMatrix:
    a, d, e, b, f, c = (Fraction(value) for value in entries)
    return ((a, d, e), (d, b, f), (e, f, c))


IDENTITY = matrix((1, 0, 0, 1, 0, 1))
J = matrix((1, 0, 0, -1, 0, 0))
L = matrix((1, 0, 0, 1, 0, -2))
CENTERS = (matrix((0, 0, 0, 0, 0, 0)), J, L)


def add(left: RMatrix, right: RMatrix) -> RMatrix:
    return tuple(
        tuple(left[i][j] + right[i][j] for j in range(3)) for i in range(3)
    )


def scale(value: RMatrix, scalar: Fraction) -> RMatrix:
    return tuple(
        tuple(scalar * value[i][j] for j in range(3)) for i in range(3)
    )


def subtract(left: RMatrix, right: RMatrix) -> RMatrix:
    return add(left, scale(right, Fraction(-1)))


def inner(left: RMatrix, right: RMatrix) -> Fraction:
    return sum(left[i][j] * right[i][j] for i in range(3) for j in range(3))


def trace(value: RMatrix) -> Fraction:
    return sum(value[i][i] for i in range(3))


def determinant(value: RMatrix) -> Fraction:
    return (
        value[0][0] * (value[1][1] * value[2][2] - value[1][2] * value[2][1])
        - value[0][1] * (value[1][0] * value[2][2] - value[1][2] * value[2][0])
        + value[0][2] * (value[1][0] * value[2][1] - value[1][1] * value[2][0])
    )


def inverse(value: RMatrix) -> RMatrix:
    det = determinant(value)
    assert det > 0
    cofactors = (
        (value[1][1] * value[2][2] - value[1][2] * value[2][1],
         value[1][2] * value[2][0] - value[1][0] * value[2][2],
         value[1][0] * value[2][1] - value[1][1] * value[2][0]),
        (value[1][2] * value[2][0] - value[1][0] * value[2][2],
         value[0][0] * value[2][2] - value[0][2] * value[2][0],
         value[0][2] * value[1][0] - value[0][0] * value[2][1]),
        (value[1][0] * value[2][1] - value[1][1] * value[2][0],
         value[0][1] * value[2][0] - value[0][0] * value[2][1],
         value[0][0] * value[1][1] - value[0][1] * value[1][0]),
    )
    return scale(cofactors, Fraction(1, 1) / det)


def normalized_shape(metric: RMatrix) -> tuple[Fraction, RMatrix]:
    scale_factor = trace(metric) / 3
    assert scale_factor > 0
    return scale_factor, scale(metric, Fraction(1, 1) / scale_factor)


def shape_gradient(metric: RMatrix, center: RMatrix) -> RMatrix:
    """Gradient in H of psi(H/tau), tau=tr(H)/3."""
    tau, shape = normalized_shape(metric)
    raw = subtract(subtract(shape, center), inverse(shape))
    return scale(
        subtract(raw, scale(IDENTITY, inner(raw, shape) / 3)),
        Fraction(1, 1) / tau,
    )


def work_direction(gram: RMatrix, gradient: RMatrix) -> RMatrix:
    norm_squared = inner(gradient, gradient)
    assert norm_squared > 0
    return subtract(gram, scale(gradient, inner(gram, gradient) / norm_squared))


def level_difference(shape: RMatrix, left: RMatrix, right: RMatrix) -> Fraction:
    """psi_left(shape)-psi_right(shape); the log determinant cancels."""
    return inner(shape, subtract(right, left)) + (
        inner(left, left) - inner(right, right)
    ) / 2


def exact_rank(rows: list[list[Fraction]]) -> int:
    work = [row[:] for row in rows]
    rank = 0
    for column in range(len(work[0])):
        pivot = next(
            (index for index in range(rank, len(work)) if work[index][column]),
            None,
        )
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        divisor = work[rank][column]
        work[rank] = [entry / divisor for entry in work[rank]]
        for index in range(len(work)):
            if index == rank or not work[index][column]:
                continue
            factor = work[index][column]
            work[index] = [
                entry - factor * pivot_entry
                for entry, pivot_entry in zip(work[index], work[rank])
            ]
        rank += 1
    return rank


def flatten(value: RMatrix) -> list[Fraction]:
    return [value[i][j] for i in range(3) for j in range(3)]


def trace_projected(center: RMatrix, shape: RMatrix) -> RMatrix:
    return subtract(center, scale(IDENTITY, inner(center, shape) / 3))


def check_scale_invariance() -> int:
    metric = matrix((2, 1, 0, 3, 1, 5))
    assert determinant(metric) > 0
    factor = Fraction(7)
    checks = 0
    for center in CENTERS:
        gradient = shape_gradient(metric, center)
        scaled_gradient = shape_gradient(scale(metric, factor), center)
        assert scaled_gradient == scale(gradient, Fraction(1, 1) / factor)
        assert inner(gradient, metric) == 0
        checks += 1
    return checks


def check_gradient_differential() -> int:
    """Compare the displayed H-gradient with a direct shape differential."""
    metrics = (
        matrix((2, 1, 0, 3, 1, 5)),
        matrix((4, -1, 1, 3, 0, 2)),
    )
    directions = (
        matrix((1, 2, -1, 0, 1, 3)),
        matrix((-2, 0, 1, 1, -1, 2)),
    )
    checks = 0
    for metric, direction in zip(metrics, directions):
        assert determinant(metric) > 0
        tau, shape = normalized_shape(metric)
        shape_rate = scale(
            subtract(direction, scale(shape, trace(direction) / 3)),
            Fraction(1, 1) / tau,
        )
        shape_inverse = inverse(shape)
        for center in CENTERS:
            direct_derivative = inner(
                subtract(subtract(shape, center), shape_inverse), shape_rate
            )
            assert inner(shape_gradient(metric, center), direction) == direct_derivative
            checks += 1
    return checks


def check_radial_escape_is_removed() -> int:
    gram = IDENTITY
    checks = 0
    for scale_factor in (Fraction(1), Fraction(2), Fraction(5), Fraction(17)):
        metric = scale(IDENTITY, scale_factor)
        gradients = [shape_gradient(metric, center) for center in CENTERS]
        assert gradients[0] == CENTERS[0]
        assert gradients[1] == scale(J, Fraction(-1, 1) / scale_factor)
        assert gradients[2] == scale(L, Fraction(-1, 1) / scale_factor)
        for gradient in gradients[1:]:
            direction = work_direction(gram, gradient)
            assert direction == gram
            assert inner(direction, direction) == 3
            checks += 1
    return checks


def check_difference_frame() -> int:
    shapes = (
        IDENTITY,
        matrix((Fraction(1, 2), 0, 0, 1, 0, Fraction(3, 2))),
        matrix((1, Fraction(1, 4), 0, 1, 0, 1)),
    )
    checks = 0
    for shape in shapes:
        assert trace(shape) == 3 and determinant(shape) > 0
        differences = [trace_projected(center, shape) for center in CENTERS[1:]]
        assert exact_rank([flatten(value) for value in differences]) == 2
        checks += 1
    return checks


def check_global_switch_gap() -> int:
    extreme_shapes = (
        scale(matrix((1, 0, 0, 0, 0, 0)), Fraction(3)),
        scale(matrix((0, 0, 0, 1, 0, 0)), Fraction(3)),
        scale(matrix((0, 0, 0, 0, 0, 1)), Fraction(3)),
    )
    expected = {
        (0, 1): (Fraction(2), Fraction(-4), Fraction(-1)),
        (0, 2): (Fraction(0), Fraction(0), Fraction(-9)),
        (1, 2): (Fraction(-2), Fraction(4), Fraction(-8)),
    }
    checks = 0
    for pair, values in expected.items():
        observed = tuple(
            level_difference(shape, CENTERS[pair[0]], CENTERS[pair[1]])
            for shape in extreme_shapes
        )
        assert observed == values
        assert max(abs(value) for value in observed) <= 9
        checks += 1
    return checks


def check_gram_positive_no_switch() -> int:
    """For physical PSD Gram tensors a nonzero shape gradient is always valid."""
    rank_one_x = matrix((1, 0, 0, 0, 0, 0))
    rank_one_z = matrix((0, 0, 0, 0, 0, 1))
    positive_grams = (IDENTITY, rank_one_x, rank_one_z)
    metrics_and_charts = (
        (IDENTITY, 1),
        (matrix((Fraction(1, 2), 0, 0, 1, 0, Fraction(3, 2))), 0),
    )
    checks = 0
    for metric, chart in metrics_and_charts:
        gradient = shape_gradient(metric, CENTERS[chart])
        assert inner(gradient, gradient) > 0
        assert inner(gradient, metric) == 0
        for gram in positive_grams:
            assert inner(metric, gram) > 0
            direction = work_direction(gram, gradient)
            assert inner(direction, direction) > 0
            checks += 1

    # The two shape gradients cannot vanish together: their difference is the
    # nonzero trace-projected version of J at every trace-three shape.
    for metric, _ in metrics_and_charts:
        _, shape = normalized_shape(metric)
        assert trace_projected(J, shape) != CENTERS[0]
        assert not (
            shape_gradient(metric, CENTERS[0]) == CENTERS[0]
            and shape_gradient(metric, CENTERS[1]) == CENTERS[0]
        )
        checks += 1
    return checks


def main() -> None:
    scale_checks = check_scale_invariance()
    print(f"Scale-normalized barrier gradient: PASS ({scale_checks} centers)")
    differential_checks = check_gradient_differential()
    print(
        "Shape-gradient differential: PASS "
        f"({differential_checks} exact directional derivatives)"
    )
    radial_checks = check_radial_escape_is_removed()
    print(f"Radial large-metric edge: PASS ({radial_checks} exact directions)")
    frame_checks = check_difference_frame()
    print(f"Trace-free center frame: PASS ({frame_checks} exact shapes)")
    switch_checks = check_global_switch_gap()
    print(f"Global normalized switch gap: PASS ({switch_checks} center pairs; sharp bound 9)")
    no_switch_checks = check_gram_positive_no_switch()
    print(f"Gram-positive no-switch atlas: PASS ({no_switch_checks} exact checks)")
    print("All exact scale-normalized barrier-atlas checks passed.")


if __name__ == "__main__":
    main()
