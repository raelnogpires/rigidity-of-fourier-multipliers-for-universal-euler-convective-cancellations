#!/usr/bin/env python3
"""Exact Fourier checks for the tangentially integrated flat-wall flux."""

from __future__ import annotations

from fractions import Fraction


Mode = tuple[int, int]
Gaussian = tuple[Fraction, Fraction]
Fourier = dict[Mode, Gaussian]
Matrix2 = tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]


def complex_add(left: Gaussian, right: Gaussian) -> Gaussian:
    return left[0] + right[0], left[1] + right[1]


def complex_scale(value: Gaussian, scalar: Fraction) -> Gaussian:
    return scalar * value[0], scalar * value[1]


def complex_multiply(left: Gaussian, right: Gaussian) -> Gaussian:
    return left[0] * right[0] - left[1] * right[1], left[0] * right[1] + left[1] * right[0]


def add(*fields: Fourier) -> Fourier:
    result: Fourier = {}
    for field in fields:
        for mode, coefficient in field.items():
            result[mode] = complex_add(result.get(mode, (Fraction(0), Fraction(0))), coefficient)
    return {mode: coefficient for mode, coefficient in result.items() if coefficient != (Fraction(0), Fraction(0))}


def scale(field: Fourier, scalar: Fraction) -> Fourier:
    return {
        mode: complex_scale(coefficient, scalar)
        for mode, coefficient in field.items()
        if complex_scale(coefficient, scalar) != (Fraction(0), Fraction(0))
    }


def multiply(left: Fourier, right: Fourier) -> Fourier:
    result: Fourier = {}
    for left_mode, left_coefficient in left.items():
        for right_mode, right_coefficient in right.items():
            mode = left_mode[0] + right_mode[0], left_mode[1] + right_mode[1]
            term = complex_multiply(left_coefficient, right_coefficient)
            result[mode] = complex_add(result.get(mode, (Fraction(0), Fraction(0))), term)
    return {mode: coefficient for mode, coefficient in result.items() if coefficient != (Fraction(0), Fraction(0))}


def derivative(field: Fourier, axis: int) -> Fourier:
    result: Fourier = {}
    for mode, coefficient in field.items():
        frequency = Fraction(mode[axis])
        # i*k*(a + i*b) = -k*b + i*k*a.
        result[mode] = -frequency * coefficient[1], frequency * coefficient[0]
    return {mode: coefficient for mode, coefficient in result.items() if coefficient != (Fraction(0), Fraction(0))}


def sine(mode: Mode) -> Fourier:
    return {
        mode: (Fraction(0), Fraction(-1, 2)),
        (-mode[0], -mode[1]): (Fraction(0), Fraction(1, 2)),
    }


def dot(left: tuple[Fourier, Fourier], right: tuple[Fourier, Fourier]) -> Fourier:
    return add(multiply(left[0], right[0]), multiply(left[1], right[1]))


def matrix_vector(matrix: Matrix2, vector: tuple[Fourier, Fourier]) -> tuple[Fourier, Fourier]:
    return (
        add(scale(vector[0], matrix[0][0]), scale(vector[1], matrix[0][1])),
        add(scale(vector[0], matrix[1][0]), scale(vector[1], matrix[1][1])),
    )


def wall_flux(wall_vorticity: tuple[Fourier, Fourier], completion: Matrix2) -> Fourier:
    curl = add(derivative(wall_vorticity[1], 0), scale(derivative(wall_vorticity[0], 1), Fraction(-1)))
    directional = (
        add(
            multiply(wall_vorticity[0], derivative(wall_vorticity[0], 0)),
            multiply(wall_vorticity[1], derivative(wall_vorticity[0], 1)),
        ),
        add(
            multiply(wall_vorticity[0], derivative(wall_vorticity[1], 0)),
            multiply(wall_vorticity[1], derivative(wall_vorticity[1], 1)),
        ),
    )
    completed = matrix_vector(completion, wall_vorticity)
    determinant = add(
        multiply(completed[0], directional[1]),
        scale(multiply(completed[1], directional[0]), Fraction(-1)),
    )
    return add(scale(multiply(curl, dot(wall_vorticity, completed)), Fraction(1, 2)), scale(determinant, Fraction(-1)))


def average(field: Fourier) -> Fraction:
    real, imaginary = field.get((0, 0), (Fraction(0), Fraction(0)))
    assert imaginary == 0
    return real


def main() -> None:
    # w = (-s_2,s_1) for the explicit periodic wall shear used below.
    wall_vorticity = add(sine((1, 0)), sine((0, 1))), sine((1, 1))
    curl = add(derivative(wall_vorticity[1], 0), scale(derivative(wall_vorticity[0], 1), Fraction(-1)))
    cubic_scalar = average(multiply(curl, dot(wall_vorticity, wall_vorticity)))
    assert cubic_scalar == Fraction(-1, 2)

    completions: dict[str, Matrix2] = {
        "E11": ((Fraction(1), Fraction(0)), (Fraction(0), Fraction(0))),
        "E12": ((Fraction(0), Fraction(1)), (Fraction(1), Fraction(0))),
        "E22": ((Fraction(0), Fraction(0)), (Fraction(0), Fraction(1))),
        "mixed": ((Fraction(3), Fraction(-2)), (Fraction(-2), Fraction(5))),
    }
    for name, completion in completions.items():
        trace = completion[0][0] + completion[1][1]
        assert average(wall_flux(wall_vorticity, completion)) == -trace * cubic_scalar / 2, name
    print("Integrated flat-wall trace law: PASS (mean curl(w)|w|^2 = -1/2)")

    # f=z(1-z)((z-1/2)^2-1/20) has integral zero and wall slopes 1/5,-1/5.
    profile_integral = Fraction(-1, 5) + Fraction(1, 2) - Fraction(1, 3) + Fraction(1, 10) - Fraction(1, 15)
    assert profile_integral == 0
    lower_scale, upper_scale = Fraction(1, 5), Fraction(-1, 5)
    lower_cubic = lower_scale**3 * cubic_scalar
    upper_cubic = upper_scale**3 * cubic_scalar
    normal_defect_average = (upper_cubic - lower_cubic) / 2
    assert normal_defect_average == Fraction(1, 250)
    print("No-slip channel witness: PASS (normalized normal defect = 1/250)")


if __name__ == "__main__":
    main()
