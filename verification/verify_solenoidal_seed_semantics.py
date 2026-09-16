#!/usr/bin/env python3
"""Tie Lean's 26x28 Hermitian seed matrix to explicit Euler test fields.

The verifier deterministically reconstructs the first 26 independent rows
from signed Boolean-seed triads, transverse integer polarizations, and real
phase choices.  It then parses ``booleanSeedMatrixZ`` from the Lean source
and checks equality row-by-row up to a nonzero rational scaling.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import gcd, lcm
from pathlib import Path
import re

from explore_full_multiplier import (
    IMAGINARY_UNIT,
    ONE,
    add_independent_row,
    energy_vector,
    exact_triad_modes,
    helicity_vector,
    invariant_row,
)
from verify_laplacian_rigidity import (
    add,
    cross,
    dot,
    neg,
    transverse_basis,
    unoriented,
)


ROOT = Path(__file__).resolve().parents[1]
LEAN_CERTIFICATE = (
    ROOT / "lean/FourierMultiplierRigidity/SolenoidalSeedCertificate.lean"
)
BOOLEAN_REPRESENTATIVES = (
    (0, 0, 1),
    (0, 1, 0),
    (0, 1, 1),
    (1, 0, 0),
    (1, 0, 1),
    (1, 1, 0),
    (1, 1, 1),
)


def primitive_integer_row(row: list[int] | list[Fraction]) -> tuple[int, ...]:
    denominator = 1
    for value in row:
        denominator = lcm(denominator, Fraction(value).denominator)
    integers = [int(Fraction(value) * denominator) for value in row]
    divisor = 0
    for value in integers:
        divisor = gcd(divisor, abs(value))
    assert divisor
    integers = [value // divisor for value in integers]
    first = next(value for value in integers if value)
    if first < 0:
        integers = [-value for value in integers]
    return tuple(integers)


def lean_matrix() -> list[list[int]]:
    source = LEAN_CERTIFICATE.read_text(encoding="utf-8")
    match = re.search(
        r"def booleanSeedMatrixZ\s*:\s*List BZRow\s*:=\s*\[(.*?)\n\]",
        source,
        flags=re.DOTALL,
    )
    assert match, "could not locate booleanSeedMatrixZ in the Lean source"
    rows = [
        [int(value.strip()) for value in body.split(",")]
        for body in re.findall(r"#\[([^\]]+)\]", match.group(1))
    ]
    assert len(rows) == 26
    assert all(len(row) == 28 for row in rows)
    return rows


def reconstructed_rows() -> tuple[list[list[Fraction]], list[tuple[object, ...]]]:
    vectors = sorted(
        list(BOOLEAN_REPRESENTATIVES)
        + [neg(mode) for mode in BOOLEAN_REPRESENTATIVES]
    )
    representatives = sorted({unoriented(mode) for mode in vectors})
    assert tuple(representatives) == BOOLEAN_REPRESENTATIVES

    basis: dict[int, list[Fraction]] = {}
    rows: list[list[Fraction]] = []
    provenance: list[tuple[object, ...]] = []
    phases = tuple(product((ONE, IMAGINARY_UNIT), repeat=3))
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if (
                r not in vectors
                or not (p <= q <= r)
                or cross(p, q) == (0, 0, 0)
            ):
                continue
            for polarizations in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                assert all(
                    dot(mode, polarization) == 0
                    for mode, polarization in zip((p, q, r), polarizations)
                )
                for phase in phases:
                    modes = exact_triad_modes(
                        p, q, r, *polarizations, phase
                    )
                    row = invariant_row(modes, representatives)
                    if any(row) and add_independent_row(basis, row):
                        rows.append(row)
                        provenance.append((p, q, r, polarizations, phase))
    assert len(rows) == 26
    return rows, provenance


def main() -> None:
    certified = lean_matrix()
    reconstructed, provenance = reconstructed_rows()
    for index, (lean_row, physical_row) in enumerate(
        zip(certified, reconstructed, strict=True)
    ):
        assert primitive_integer_row(lean_row) == primitive_integer_row(
            physical_row
        ), f"Lean row {index} does not match its physical test field"

    energy = energy_vector(BOOLEAN_REPRESENTATIVES)
    helicity = helicity_vector(BOOLEAN_REPRESENTATIVES)
    assert all(sum(x * y for x, y in zip(row, energy)) == 0 for row in reconstructed)
    assert all(sum(x * y for x, y in zip(row, helicity)) == 0 for row in reconstructed)
    assert provenance
    print(
        "Hermitian Boolean-seed semantic bridge verified: "
        "26 Lean rows = 26 explicit triad-supported field evaluations; "
        "energy and helicity annihilate every row."
    )


if __name__ == "__main__":
    main()
