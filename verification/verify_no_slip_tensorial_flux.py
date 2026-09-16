#!/usr/bin/env python3
"""Exact no-slip counterexample for the tensorial Miller boundary flux."""

from __future__ import annotations

from fractions import Fraction


Exponent = tuple[int, int, int]
Polynomial = dict[Exponent, Fraction]
RMatrix = tuple[tuple[Fraction, Fraction, Fraction], ...]


def add(*polynomials: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] = result.get(exponent, Fraction(0)) + coefficient
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def scale(polynomial: Polynomial, scalar: Fraction) -> Polynomial:
    return {
        exponent: scalar * coefficient
        for exponent, coefficient in polynomial.items()
        if scalar * coefficient
    }


def multiply(left: Polynomial, right: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            exponent = tuple(
                left_exponent[index] + right_exponent[index] for index in range(3)
            )
            result[exponent] = result.get(exponent, Fraction(0)) + (
                left_coefficient * right_coefficient
            )
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def derivative(polynomial: Polynomial, axis: int) -> Polynomial:
    result: Polynomial = {}
    for exponent, coefficient in polynomial.items():
        power = exponent[axis]
        if not power:
            continue
        shifted = list(exponent)
        shifted[axis] -= 1
        result[tuple(shifted)] = coefficient * power
    return result


def integrate_cube(polynomial: Polynomial) -> Fraction:
    return sum(
        coefficient
        / ((exponent[0] + 1) * (exponent[1] + 1) * (exponent[2] + 1))
        for exponent, coefficient in polynomial.items()
    )


def restrict_face(polynomial: Polynomial, axis: int, value: int) -> Polynomial:
    result: Polynomial = {}
    for exponent, coefficient in polynomial.items():
        reduced = list(exponent)
        power = reduced[axis]
        reduced[axis] = 0
        term = coefficient * Fraction(value**power)
        result[tuple(reduced)] = result.get(tuple(reduced), Fraction(0)) + term
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def integrate_face(polynomial: Polynomial, axis: int, value: int) -> Fraction:
    restricted = restrict_face(polynomial, axis, value)
    return sum(
        coefficient
        / ((exponent[(axis + 1) % 3] + 1) * (exponent[(axis + 2) % 3] + 1))
        for exponent, coefficient in restricted.items()
    )


def dot(left: tuple[Polynomial, Polynomial, Polynomial], right: tuple[Polynomial, Polynomial, Polynomial]) -> Polynomial:
    return add(*(multiply(left[index], right[index]) for index in range(3)))


def cross(left: tuple[Polynomial, Polynomial, Polynomial], right: tuple[Polynomial, Polynomial, Polynomial]) -> tuple[Polynomial, Polynomial, Polynomial]:
    return (
        add(multiply(left[1], right[2]), scale(multiply(left[2], right[1]), Fraction(-1))),
        add(multiply(left[2], right[0]), scale(multiply(left[0], right[2]), Fraction(-1))),
        add(multiply(left[0], right[1]), scale(multiply(left[1], right[0]), Fraction(-1))),
    )


def curl(vector: tuple[Polynomial, Polynomial, Polynomial]) -> tuple[Polynomial, Polynomial, Polynomial]:
    return (
        add(derivative(vector[2], 1), scale(derivative(vector[1], 2), Fraction(-1))),
        add(derivative(vector[0], 2), scale(derivative(vector[2], 0), Fraction(-1))),
        add(derivative(vector[1], 0), scale(derivative(vector[0], 1), Fraction(-1))),
    )


def divergence(vector: tuple[Polynomial, Polynomial, Polynomial]) -> Polynomial:
    return add(*(derivative(vector[index], index) for index in range(3)))


def matvec(matrix: RMatrix, vector: tuple[Polynomial, Polynomial, Polynomial]) -> tuple[Polynomial, Polynomial, Polynomial]:
    return tuple(
        add(*(scale(vector[column], matrix[row][column]) for column in range(3)))
        for row in range(3)
    )  # type: ignore[return-value]


def tensor_contraction(matrix: RMatrix, tensor: tuple[tuple[Polynomial, Polynomial, Polynomial], ...]) -> Polynomial:
    return add(
        *(scale(tensor[row][column], matrix[row][column]) for row in range(3) for column in range(3))
    )


def shape_stream_function(weights: tuple[int, int, int]) -> Polynomial:
    factors = (
        {(2, 0, 0): Fraction(1), (3, 0, 0): Fraction(-2), (4, 0, 0): Fraction(1)},
        {(0, 2, 0): Fraction(1), (0, 3, 0): Fraction(-2), (0, 4, 0): Fraction(1)},
        {(0, 0, 2): Fraction(1), (0, 0, 3): Fraction(-2), (0, 0, 4): Fraction(1)},
    )
    asymmetric_factor = {
        (0, 0, 0): Fraction(1),
        (1, 0, 0): Fraction(weights[0]),
        (0, 1, 0): Fraction(weights[1]),
        (0, 0, 1): Fraction(weights[2]),
    }
    return multiply(multiply(multiply(factors[0], factors[1]), factors[2]), asymmetric_factor)


def no_slip_velocity() -> tuple[Polynomial, Polynomial, Polynomial]:
    vertical_potential = shape_stream_function((1, 2, 3))
    horizontal_potential = shape_stream_function((2, -1, 1))
    # curl(0, horizontal_potential, vertical_potential)
    return (
        add(derivative(vertical_potential, 1), scale(derivative(horizontal_potential, 2), Fraction(-1))),
        scale(derivative(vertical_potential, 0), Fraction(-1)),
        derivative(horizontal_potential, 0),
    )


def strain(velocity: tuple[Polynomial, Polynomial, Polynomial]) -> tuple[tuple[Polynomial, Polynomial, Polynomial], ...]:
    return tuple(
        tuple(
            scale(
                add(derivative(velocity[row], column), derivative(velocity[column], row)),
                Fraction(1, 2),
            )
            for column in range(3)
        )
        for row in range(3)
    )


def tensorial_miller_tensor(velocity: tuple[Polynomial, Polynomial, Polynomial]) -> tuple[tuple[Polynomial, Polynomial, Polynomial], ...]:
    strain_tensor = strain(velocity)
    vorticity = curl(velocity)
    result: list[list[Polynomial]] = [[{} for _ in range(3)] for _ in range(3)]
    for left in range(3):
        for right in range(3):
            terms: list[Polynomial] = []
            for row in range(3):
                for column in range(3):
                    hessian_term = add(
                        derivative(derivative(strain_tensor[row][column], left), right),
                        scale(derivative(derivative(strain_tensor[left][right], row), column), Fraction(-1)),
                    )
                    terms.append(multiply(multiply(vorticity[row], vorticity[column]), hessian_term))
            result[left][right] = add(*terms)
    return tuple(tuple(row) for row in result)


def tensorial_flux(velocity: tuple[Polynomial, Polynomial, Polynomial], metric: RMatrix) -> tuple[Polynomial, Polynomial, Polynomial]:
    vorticity = curl(velocity)
    eta = curl(vorticity)
    directional = tuple(
        add(*(multiply(vorticity[axis], derivative(vorticity[index], axis)) for axis in range(3)))
        for index in range(3)
    )
    trace_metric = sum(metric[index][index] for index in range(3))
    completion: RMatrix = tuple(
        tuple((trace_metric * Fraction(row == column)) / 2 - metric[row][column] for column in range(3))
        for row in range(3)
    )
    completed_vorticity = matvec(completion, vorticity)
    first_scalar = dot(vorticity, curl(completed_vorticity))
    second_scalar = dot(vorticity, completed_vorticity)
    first = tuple(multiply(vorticity[index], first_scalar) for index in range(3))
    second = tuple(scale(multiply(eta[index], second_scalar), Fraction(1, 2)) for index in range(3))
    third = cross(completed_vorticity, directional)
    return tuple(
        add(first[index], second[index], scale(third[index], Fraction(-1)))
        for index in range(3)
    )  # type: ignore[return-value]


def outward_flux(vector: tuple[Polynomial, Polynomial, Polynomial]) -> Fraction:
    return sum(
        integrate_face(vector[axis], axis, 1) - integrate_face(vector[axis], axis, 0)
        for axis in range(3)
    )


def no_slip_surface_cubic(velocity: tuple[Polynomial, Polynomial, Polynomial], axis: int, face: int) -> Fraction:
    """Integral of curl_surface(omega)|omega|^2 with the outward orientation."""
    sign = Fraction(1 if face else -1)
    one = {(0, 0, 0): Fraction(1)}
    normal = tuple(scale(one, sign if index == axis else Fraction(0)) for index in range(3))
    wall_shear = tuple(scale(derivative(velocity[index], axis), sign) for index in range(3))
    wall_vorticity = cross(normal, wall_shear)
    surface_curl = dot(normal, curl(wall_vorticity))
    return integrate_face(multiply(surface_curl, dot(wall_vorticity, wall_vorticity)), axis, face)


def flat_wall_flux_z(velocity: tuple[Polynomial, Polynomial, Polynomial], metric: RMatrix) -> Polynomial:
    """J_3 on a z=constant no-slip wall, written through tangential shear."""
    shear = derivative(velocity[0], 2), derivative(velocity[1], 2)
    wall_vorticity = scale(shear[1], Fraction(-1)), shear[0]
    eta_normal = add(derivative(shear[0], 0), derivative(shear[1], 1))
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
    trace_metric = sum(metric[index][index] for index in range(3))
    completion = tuple(
        tuple((trace_metric * Fraction(row == column)) / 2 - metric[row][column] for column in range(3))
        for row in range(3)
    )
    completed = (
        add(scale(wall_vorticity[0], completion[0][0]), scale(wall_vorticity[1], completion[0][1])),
        add(scale(wall_vorticity[0], completion[1][0]), scale(wall_vorticity[1], completion[1][1])),
    )
    quadratic = add(multiply(wall_vorticity[0], completed[0]), multiply(wall_vorticity[1], completed[1]))
    tangential_cross = add(
        multiply(completed[0], directional[1]),
        scale(multiply(completed[1], directional[0]), Fraction(-1)),
    )
    return add(scale(multiply(eta_normal, quadratic), Fraction(1, 2)), scale(tangential_cross, Fraction(-1)))


def main() -> None:
    velocity = no_slip_velocity()
    assert divergence(velocity) == {}
    for component in velocity:
        for axis in range(3):
            assert restrict_face(component, axis, 0) == {}
            assert restrict_face(component, axis, 1) == {}
    print("Polynomial no-slip divergence-free velocity: PASS")

    tensor = tensorial_miller_tensor(velocity)
    tensor_integral = tuple(
        tuple(integrate_cube(tensor[row][column]) for column in range(3))
        for row in range(3)
    )
    assert tensor_integral == (
        (Fraction(-8, 9018009), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    metric: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(0)),
    )
    contracted = tensor_contraction(metric, tensor)
    flux = tensorial_flux(velocity, metric)
    assert add(contracted, divergence(flux)) == {}
    assert integrate_cube(contracted) == -outward_flux(flux)
    assert integrate_cube(contracted) != 0
    wall_formula = flat_wall_flux_z(velocity, metric)
    for face in (0, 1):
        assert restrict_face(flux[2], 2, face) == restrict_face(wall_formula, 2, face)
    print(f"No-slip tensorial boundary flux: PASS (integral F_11 = {integrate_cube(contracted)})")
    print("Flat no-slip wall-shear reduction: PASS (both z faces)")

    # B_H has a nonzero normal--tangential block but B_T=0.  The local wall
    # formula says this entire three-parameter class has zero normal flux.
    wall_null_metric: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(1)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(0), Fraction(0)),
    )
    wall_null_flux = tensorial_flux(velocity, wall_null_metric)
    for face in (0, 1):
        assert restrict_face(wall_null_flux[2], 2, face) == {}
    print("Flat-wall null metric: PASS (zero tangential completion block)")

    identity_metric: RMatrix = (
        (Fraction(1), Fraction(0), Fraction(0)),
        (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)),
    )
    scalar_contracted = tensor_contraction(identity_metric, tensor)
    scalar_flux = tensorial_flux(velocity, identity_metric)
    surface_cubic = sum(no_slip_surface_cubic(velocity, axis, face) for axis in range(3) for face in (0, 1))
    assert integrate_cube(scalar_contracted) == surface_cubic / 2
    assert outward_flux(scalar_flux) == -surface_cubic / 2
    print("Closed no-slip scalar wall law: PASS (all six oriented faces)")
    print("All exact no-slip tensorial-flux checks passed.")


if __name__ == "__main__":
    main()
