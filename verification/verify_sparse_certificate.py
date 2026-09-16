#!/usr/bin/env python3
"""Exact verifier for optimal sparse energy--helicity certificates.

For a coordinate box with M unoriented nonzero Fourier modes, a general
reality-compatible Hermitian symbol has 4M real parameters.  Energy and
helicity span a two-dimensional unavoidable kernel, so at least 4M-2 scalar
tests are needed to certify that no other quadratic Euler invariant exists.

This script constructs exactly 4M-2 actual six-mode trigonometric tests:

* 26 independent tests on a seven-mode Boolean seed;
* four tests for every subsequently added mode, using one non-collinear triad
  whose two known inputs have unequal lengths.

The construction is block triangular in propagation order.  We additionally
assemble the whole rational matrix in the box of radius two and verify its
rank directly, without floating-point arithmetic.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from itertools import product
from typing import Dict, List, Sequence, Set, Tuple

from explore_full_multiplier import (
    IMAGINARY_UNIT,
    ONE,
    add_independent_row,
    energy_vector,
    exact_triad_modes,
    helicity_vector,
    invariant_row,
)
from verify_full_multiplier_rigidity import (
    BOOLEAN_SEED_REPRESENTATIVES,
    PHASES,
    boolean_seed_vectors,
    direct_target_rows,
    exact_rank,
    nonzero_vectors,
)
from verify_laplacian_rigidity import (
    Vec,
    add,
    cross,
    neg,
    norm2,
    transverse_basis,
    unoriented,
)


Step = Tuple[Vec, Vec, Vec, Vec]


def cube_representatives(box: int) -> List[Vec]:
    """Canonical representatives of nonzero modes in [-box, box]^3."""
    return sorted({unoriented(k) for k in nonzero_vectors(box)})


def scaled(scale: int, vector: Vec) -> Vec:
    return tuple(scale * component for component in vector)  # type: ignore[return-value]


def coordinate_vector(index: int) -> Vec:
    return tuple(1 if coordinate == index else 0 for coordinate in range(3))  # type: ignore[return-value]


def triad_support(p: Vec, q: Vec, r: Vec) -> Tuple[Vec, Vec, Vec]:
    """Canonicalize one triad up to permutation and simultaneous sign."""
    forward = tuple(sorted((p, q, r)))
    backward = tuple(sorted((neg(p), neg(q), neg(r))))
    return min(forward, backward)  # type: ignore[return-value]


def propagation_order(box: int) -> Tuple[List[Vec], List[Step]]:
    """Return a one-triad-per-new-mode propagation order for a cube.

    A step is (target representative, p, q, r), where p+q+r=0,
    p represents the target, and q,r were already known with |q| != |r|.
    """
    representatives = cube_representatives(box)
    seed_signed = set(boolean_seed_vectors())
    known: Set[Vec] = set(seed_signed)
    steps: List[Step] = []

    def certify(target: Vec, q: Vec, r: Vec) -> None:
        representative = unoriented(target)
        if representative in known:
            return
        assert q in known and r in known, (target, q, r)
        assert add(q, r) == target
        assert cross(q, r) != (0, 0, 0)
        assert norm2(q) != norm2(r)
        p = neg(target)
        steps.append((representative, p, q, r))
        known.add(representative)
        known.add(neg(representative))

    # Six full-rank steps turn the seven Boolean representatives into the
    # entire 13-representative unit cube.
    e1, e2, e3 = (
        coordinate_vector(0),
        coordinate_vector(1),
        coordinate_vector(2),
    )
    body_1 = add(e1, neg(add(e2, e3)))
    body_2 = add(e2, neg(add(e1, e3)))
    body_3 = add(e3, neg(add(e1, e2)))
    certify(body_1, e1, neg(add(e2, e3)))
    certify(body_2, e2, neg(add(e1, e3)))
    certify(body_3, e3, neg(add(e1, e2)))
    certify(add(e1, neg(e2)), body_1, e3)
    certify(add(e1, neg(e3)), body_1, e2)
    certify(add(e2, neg(e3)), body_2, e1)
    assert set(nonzero_vectors(1)) <= known

    # Build all positive coordinate axes.  The intermediate off-axis mode is
    # also a mode of the target cube and receives its own certificate.
    for i in range(3):
        j = (i + 1) % 3
        ei, ej = coordinate_vector(i), coordinate_vector(j)
        for magnitude in range(2, box + 1):
            previous_axis = scaled(magnitude - 1, ei)
            diagonal = add(ei, ej)
            off_axis = add(scaled(magnitude, ei), ej)
            certify(off_axis, previous_axis, diagonal)
            certify(scaled(magnitude, ei), off_axis, neg(ej))

    # Induct in l1.  Canonical representatives have a positive first nonzero
    # coordinate, but their later coordinates may have either sign.
    ordered = sorted(representatives, key=lambda k: (sum(abs(x) for x in k), k))
    for target in ordered:
        if target in known:
            continue
        assert sum(component != 0 for component in target) >= 2
        index = next(i for i, component in enumerate(target) if component)
        sign = 1 if target[index] > 0 else -1
        unit = scaled(sign, coordinate_vector(index))
        remainder = tuple(target[i] - unit[i] for i in range(3))
        certify(target, remainder, unit)  # type: ignore[arg-type]

    assert set(representatives) <= known
    seed_representatives = list(BOOLEAN_SEED_REPRESENTATIVES)
    assert len(steps) == len(representatives) - len(seed_representatives)
    assert len({triad_support(p, q, r) for _target, p, q, r in steps}) == len(steps)
    return representatives, steps


def embed_blocks(
    row: Sequence[Fraction],
    local_representatives: Sequence[Vec],
    global_representatives: Sequence[Vec],
) -> List[Fraction]:
    """Embed four-parameter mode blocks into a larger coordinate system."""
    global_index = {k: i for i, k in enumerate(global_representatives)}
    result = [Fraction(0)] * (4 * len(global_representatives))
    for local_index, mode in enumerate(local_representatives):
        target = 4 * global_index[mode]
        source = 4 * local_index
        result[target : target + 4] = row[source : source + 4]
    return result


@lru_cache(maxsize=None)
def selected_seed_rows(
    global_representatives: Tuple[Vec, ...],
) -> Tuple[List[List[Fraction]], int, int]:
    """Greedily extract 26 independent tests from the Boolean seed."""
    vectors = boolean_seed_vectors()
    local_representatives = list(BOOLEAN_SEED_REPRESENTATIVES)
    basis: Dict[int, List[Fraction]] = {}
    selected: List[List[Fraction]] = []
    supports: Set[Tuple[Vec, Vec, Vec]] = set()
    available = 0
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            support = triad_support(p, q, r)
            for a, b, c in product(
                transverse_basis(p), transverse_basis(q), transverse_basis(r)
            ):
                for phase in PHASES:
                    modes = exact_triad_modes(p, q, r, a, b, c, phase)
                    local_row = invariant_row(modes, local_representatives)
                    if not any(local_row):
                        continue
                    available += 1
                    if add_independent_row(basis, local_row):
                        selected.append(
                            embed_blocks(
                                local_row,
                                local_representatives,
                                global_representatives,
                            )
                        )
                        supports.add(support)
    assert len(selected) == len(basis) == 26
    return selected, available, len(supports)


def selected_propagation_rows(
    p: Vec,
    q: Vec,
    r: Vec,
    representatives: Sequence[Vec],
) -> List[List[Fraction]]:
    """Select four tests whose target-mode block has exact rank four."""
    target = unoriented(p)
    start = 4 * representatives.index(target)
    local_basis: Dict[int, List[Fraction]] = {}
    selected: List[List[Fraction]] = []
    phases = ((ONE, ONE, ONE), (IMAGINARY_UNIT, ONE, ONE))
    for a, b, c in product(
        transverse_basis(p), transverse_basis(q), transverse_basis(r)
    ):
        for phase in phases:
            modes = exact_triad_modes(p, q, r, a, b, c, phase)
            row = invariant_row(modes, representatives)
            target_block = row[start : start + 4]
            if add_independent_row(local_basis, target_block):
                selected.append(row)
    assert len(selected) == len(local_basis) == 4
    return selected


def sparse_certificate(
    box: int, assemble_global_rank: bool = False
) -> Tuple[int, int, int, int, int, int | None]:
    """Construct the optimal-cardinality certificate in one coordinate box."""
    representatives, steps = propagation_order(box)
    modes = len(representatives)
    dimension = 4 * modes
    lower_bound = dimension - 2
    seed_representatives = list(BOOLEAN_SEED_REPRESENTATIVES)

    # Large boxes need only the exact 4-by-4 diagonal-block checks: the
    # propagation order makes the full matrix block triangular.  Dense global
    # assembly is retained below as an independent check in the small boxes.
    seed_target = representatives if assemble_global_rank else seed_representatives
    seed_rows, seed_available, seed_supports = selected_seed_rows(tuple(seed_target))
    for _target, p, q, r in steps:
        assert exact_rank(direct_target_rows(p, q, r)) == 4

    global_rank: int | None = None
    if assemble_global_rank:
        rows = list(seed_rows)
        for _target, p, q, r in steps:
            rows.extend(selected_propagation_rows(p, q, r, representatives))
        assert len(rows) == lower_bound

        energy = energy_vector(representatives)
        helicity = helicity_vector(representatives)
        for row in rows:
            assert sum(x * y for x, y in zip(row, energy)) == 0
            assert sum(x * y for x, y in zip(row, helicity)) == 0

        global_basis: Dict[int, List[Fraction]] = {}
        for row in rows:
            assert add_independent_row(global_basis, row)
        global_rank = len(global_basis)
        assert global_rank == lower_bound

    tests = 26 + 4 * len(steps)
    assert tests == lower_bound
    return modes, len(steps), tests, seed_available, seed_supports, global_rank


def main() -> None:
    for box in (1, 2, 3, 4, 10):
        result = sparse_certificate(box, assemble_global_rank=box <= 2)
        modes, steps, tests, available, supports, global_rank = result
        expected_modes = 4 * box**3 + 6 * box**2 + 3 * box
        assert modes == expected_modes
        suffix = (
            f"; assembled rational rank {global_rank}"
            if global_rank is not None
            else "; block-triangular rank verified"
        )
        print(
            f"Sparse certificate box {box}: PASS "
            f"({modes} unoriented modes; {steps} propagation triads; "
            f"{tests}=4M-2 selected tests{suffix})"
        )
        if box == 1:
            print(
                "Seed extraction: PASS "
                f"(26 selected from {available} nonzero tests; "
                f"{supports} triad supports used)"
            )

    print("Optimal sparse certificate checks passed.")


if __name__ == "__main__":
    main()
