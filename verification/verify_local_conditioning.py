#!/usr/bin/env python3
"""Exact checks for the quantitative unequal-triad propagation law.

For p+q+r=0, define the projected Euler interaction

    L_p(B,C) = P_{p-perp}[(B dot r) C + (C dot q) B].

After flattening this bilinear map from q-perp tensor r-perp to p-perp, its
two squared singular values are

    |q x r|^2 (|q|^2 + |r|^2) / (|q|^2 |r|^2),
    |q x r|^2 (|q|^2 - |r|^2)^2 / (|p|^2 |q|^2 |r|^2).

The verifier checks the underlying vector identities on every signed triad in
several lattice boxes, proves mechanically that the explicit sparse ordering
uses blocks bounded below by 1/10 with condition number at most sqrt(15), and
checks an exact family whose condition number diverges despite every member
having unequal input lengths.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence, Tuple

from verify_full_multiplier_rigidity import nonzero_vectors
from verify_laplacian_rigidity import Vec, add, neg, norm2
from verify_sparse_certificate import propagation_order


QVec = Tuple[Fraction, Fraction, Fraction]


def idot(a: Sequence[int | Fraction], b: Sequence[int | Fraction]) -> Fraction:
    return sum((Fraction(x) * Fraction(y) for x, y in zip(a, b)), Fraction(0))


def icross(a: Sequence[int | Fraction], b: Sequence[int | Fraction]) -> QVec:
    return (
        Fraction(a[1]) * Fraction(b[2]) - Fraction(a[2]) * Fraction(b[1]),
        Fraction(a[2]) * Fraction(b[0]) - Fraction(a[0]) * Fraction(b[2]),
        Fraction(a[0]) * Fraction(b[1]) - Fraction(a[1]) * Fraction(b[0]),
    )


def qadd(a: Sequence[int | Fraction], b: Sequence[int | Fraction]) -> QVec:
    return tuple(Fraction(x) + Fraction(y) for x, y in zip(a, b))  # type: ignore[return-value]


def qscale(scale: int | Fraction, vector: Sequence[int | Fraction]) -> QVec:
    return tuple(Fraction(scale) * Fraction(x) for x in vector)  # type: ignore[return-value]


def project(vector: Sequence[int | Fraction], p: Vec) -> QVec:
    coefficient = idot(vector, p) / norm2(p)
    return qadd(vector, qscale(-coefficient, p))


def interaction(
    p: Vec,
    q: Vec,
    r: Vec,
    b: Sequence[int | Fraction],
    c: Sequence[int | Fraction],
) -> QVec:
    raw = qadd(qscale(idot(b, r), c), qscale(idot(c, q), b))
    return project(raw, p)


def equal_vector(a: Sequence[int | Fraction], b: Sequence[int | Fraction]) -> bool:
    return all(Fraction(x) == Fraction(y) for x, y in zip(a, b))


def squared_singular_values(p: Vec, q: Vec, r: Vec) -> Tuple[Fraction, Fraction]:
    z = icross(q, r)
    area2 = idot(z, z)
    p2, q2, r2 = norm2(p), norm2(q), norm2(r)
    normal = area2 * (q2 + r2) / (q2 * r2)
    in_plane = area2 * (q2 - r2) ** 2 / (p2 * q2 * r2)
    return normal, in_plane


def verify_triad(p: Vec, q: Vec, r: Vec) -> Tuple[Fraction, Fraction]:
    assert add(add(p, q), r) == (0, 0, 0)
    z = icross(q, r)
    area2 = idot(z, z)
    assert area2 > 0
    jq, jr, jp = icross(z, q), icross(z, r), icross(z, p)
    delta = norm2(q) - norm2(r)

    assert equal_vector(interaction(p, q, r, z, z), (0, 0, 0))
    assert equal_vector(interaction(p, q, r, z, jr), qscale(-area2, z))
    assert equal_vector(interaction(p, q, r, jq, z), qscale(area2, z))
    assert equal_vector(
        interaction(p, q, r, jq, jr),
        qscale(area2 * delta / norm2(p), jp),
    )

    normal, in_plane = squared_singular_values(p, q, r)
    # Recover the singular values independently from the norms of the three
    # nonzero images after normalizing each tensor-product input.
    image_normal_1 = interaction(p, q, r, z, jr)
    image_normal_2 = interaction(p, q, r, jq, z)
    recovered_normal = (
        idot(image_normal_1, image_normal_1) / (idot(z, z) * idot(jr, jr))
        + idot(image_normal_2, image_normal_2) / (idot(jq, jq) * idot(z, z))
    )
    image_in_plane = interaction(p, q, r, jq, jr)
    recovered_in_plane = idot(image_in_plane, image_in_plane) / (
        idot(jq, jq) * idot(jr, jr)
    )
    assert recovered_normal == normal
    assert recovered_in_plane == in_plane
    assert normal > 0
    assert (in_plane == 0) == (norm2(q) == norm2(r))
    return normal, in_plane


def signed_triads(box: int) -> Iterable[Tuple[Vec, Vec, Vec]]:
    vectors = set(nonzero_vectors(box))
    for p in sorted(vectors):
        for q in sorted(vectors):
            r = neg(add(p, q))
            if r not in vectors:
                continue
            if idot(icross(q, r), icross(q, r)) == 0:
                continue
            yield p, q, r


def verify_boxes() -> int:
    checked = 0
    for box in (1, 2, 3):
        for p, q, r in signed_triads(box):
            verify_triad(p, q, r)
            checked += 1
    return checked


def verify_sparse_conditioning() -> Tuple[int, Fraction, Fraction]:
    checked = 0
    minimum: Fraction | None = None
    maximum_condition_squared = Fraction(0)
    for box in (2, 3, 4, 10):
        _representatives, steps = propagation_order(box)
        for _target, p, q, r in steps:
            normal, in_plane = squared_singular_values(p, q, r)
            local_minimum = min(normal, in_plane)
            condition_squared = max(normal, in_plane) / local_minimum
            minimum = local_minimum if minimum is None else min(minimum, local_minimum)
            maximum_condition_squared = max(
                maximum_condition_squared, condition_squared
            )
            assert local_minimum >= Fraction(1, 10)
            assert condition_squared <= 15
            checked += 1
    assert minimum == Fraction(1, 10)
    assert maximum_condition_squared == 15
    return checked, minimum, maximum_condition_squared


def verify_ill_conditioned_family(limit: int = 100) -> int:
    for n in range(1, limit + 1):
        q = (n, 0, 0)
        r = (0, n, 1)
        p = neg(add(q, r))
        normal, in_plane = verify_triad(p, q, r)
        scale = 2 * n * n + 1
        assert normal == scale
        assert in_plane == Fraction(1, scale)
        # The ratio of singular values is exactly 2n^2+1.
        assert normal / in_plane == scale * scale
    return limit


def main() -> None:
    triads = verify_boxes()
    print(
        "Local singular-value formula: PASS "
        f"({triads} signed non-collinear triads checked exactly)"
    )

    steps, minimum, maximum_condition_squared = verify_sparse_conditioning()
    print(
        "Uniform sparse-step conditioning: PASS "
        f"({steps} propagation blocks; minimum squared singular value {minimum}; "
        f"maximum condition number sqrt({maximum_condition_squared}))"
    )

    family = verify_ill_conditioned_family()
    print(
        "Near-isosceles contrast family: PASS "
        f"(n=1,...,{family}; singular-value ratio exactly 2n^2+1)"
    )
    print("Quantitative local-conditioning checks passed.")


if __name__ == "__main__":
    main()
