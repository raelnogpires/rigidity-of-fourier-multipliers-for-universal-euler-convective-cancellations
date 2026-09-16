#!/usr/bin/env python3
"""Exact checks for the global full-multiplier rigidity argument.

The companion research note reduces universal strain--vorticity cancellation
to quadratic Euler invariants.  This verifier checks the two finite pieces of
the completed classification:

1. a seven-mode Boolean seed has a 2-dimensional invariant kernel, generated
   by energy and helicity;
2. on a non-collinear triad p+q+r=0, fixing the symbols at q and r determines
   all four Hermitian parameters at p exactly when |q| != |r|.

It also verifies, in successively larger lattice boxes, the constructive
propagation used in the proof.  All rank calculations use Fraction arithmetic.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Dict, Iterable, List, Sequence, Set, Tuple

from explore_full_multiplier import (
    IMAGINARY_UNIT,
    ONE,
    add_independent_row,
    coordinates,
    energy_vector,
    exact_triad_modes,
    gadd,
    gdot,
    gmul,
    gsub,
    helicity_vector,
    invariant_row,
    orthogonal_frame,
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


PHASES = tuple(product((ONE, IMAGINARY_UNIT), repeat=3))

# One representative from each of the seven nonempty subsets of the coordinate
# directions.  Exact search inside the 13-mode unit cube found this smaller
# seed; the six missing unit-cube representatives are then recovered by the
# unequal-length propagation lemma.
BOOLEAN_SEED_REPRESENTATIVES: Tuple[Vec, ...] = tuple(
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


def boolean_seed_vectors() -> List[Vec]:
    """The 14 signed modes in the seven-mode Boolean seed."""
    return sorted(
        set(BOOLEAN_SEED_REPRESENTATIVES)
        | {neg(k) for k in BOOLEAN_SEED_REPRESENTATIVES}
    )


def nonzero_vectors(box: int) -> List[Vec]:
    return [
        k
        for k in product(range(-box, box + 1), repeat=3)
        if k != (0, 0, 0)
    ]


def triad_rows(
    p: Vec, q: Vec, r: Vec, representatives: Sequence[Vec]
) -> Iterable[List[Fraction]]:
    """Generate every real invariant row supplied by one signed triad."""
    assert add(add(p, q), r) == (0, 0, 0)
    assert cross(p, q) != (0, 0, 0)
    for a, b, c in product(
        transverse_basis(p), transverse_basis(q), transverse_basis(r)
    ):
        for phase in PHASES:
            row = invariant_row(
                exact_triad_modes(p, q, r, a, b, c, phase), representatives
            )
            if any(row):
                yield row


def exact_rank(rows: Iterable[Sequence[Fraction]]) -> int:
    basis: Dict[int, List[Fraction]] = {}
    for row in rows:
        add_independent_row(basis, row)
    return len(basis)


def seed_certificate() -> Tuple[int, int, List[List[Fraction]]]:
    """Return exact rank, dimension and all rational seed equations."""
    vectors = boolean_seed_vectors()
    representatives = list(BOOLEAN_SEED_REPRESENTATIVES)
    energy = energy_vector(representatives)
    helicity = helicity_vector(representatives)
    rows: List[List[Fraction]] = []
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors or not (p <= q <= r) or cross(p, q) == (0, 0, 0):
                continue
            for row in triad_rows(p, q, r, representatives):
                assert sum(x * y for x, y in zip(row, energy)) == 0
                assert sum(x * y for x, y in zip(row, helicity)) == 0
                rows.append(row)
    return exact_rank(rows), 4 * len(representatives), rows


def rank_mod_prime(rows: Sequence[Sequence[Fraction]], prime: int) -> int:
    """Independent echelon reduction after mapping rational rows to F_p."""
    basis: Dict[int, List[int]] = {}
    for rational_row in rows:
        row = [
            (value.numerator % prime) * pow(value.denominator, -1, prime) % prime
            for value in rational_row
        ]
        for pivot in sorted(basis):
            if not row[pivot]:
                continue
            factor = row[pivot]
            row = [
                (entry - factor * basis[pivot][j]) % prime
                for j, entry in enumerate(row)
            ]
        pivot = next((j for j, entry in enumerate(row) if entry), None)
        if pivot is None:
            continue
        inverse = pow(row[pivot], -1, prime)
        basis[pivot] = [(entry * inverse) % prime for entry in row]
    return len(basis)


def direct_target_rows(p: Vec, q: Vec, r: Vec) -> List[List[Fraction]]:
    """Rows in the target block, without evaluating the other two blocks."""
    frame = orthogonal_frame(unoriented(p))
    orientation = 1 if p == unoriented(p) else -1
    rows: List[List[Fraction]] = []
    # Only the product of the three phases matters.  Products 1 and i
    # separately expose the real-symmetric and imaginary-skew parameters.
    phases = ((ONE, ONE, ONE), (IMAGINARY_UNIT, ONE, ONE))
    for a, b, c in product(
        transverse_basis(p), transverse_basis(q), transverse_basis(r)
    ):
        for phase in phases:
            modes = exact_triad_modes(p, q, r, a, b, c, phase)
            x1, x2 = coordinates(modes[p], frame)
            q_factor = gmul(IMAGINARY_UNIT, gdot(modes[q], r))
            r_factor = gmul(IMAGINARY_UNIT, gdot(modes[r], q))
            nonlinear = tuple(
                gadd(gmul(q_factor, modes[r][i]), gmul(r_factor, modes[q][i]))
                for i in range(3)
            )
            y1, y2 = coordinates(nonlinear, frame)
            coefficients = [
                gmul(y1, x1),
                gmul(y2, x2),
                gadd(gmul(y1, x2), gmul(y2, x1)),
                gmul(IMAGINARY_UNIT, gsub(gmul(y1, x2), gmul(y2, x1))),
            ]
            if orientation < 0:
                coefficients[3] = tuple(-v for v in coefficients[3])
            # Add the conjugate negative triad: twice the real part.
            row = [2 * value[0] for value in coefficients]
            if any(row):
                rows.append(row)
    return rows


def target_rank(p: Vec, q: Vec, r: Vec) -> int:
    """Rank seen in the four Hermitian parameters at the target mode p."""
    return exact_rank(direct_target_rows(p, q, r))


def check_direct_target_formula() -> int:
    """Compare the reduced formula with the full Fourier convolution."""
    examples = (
        ((1, 0, 0), (0, 1, 0), (-1, -1, 0)),
        ((1, 1, 0), (0, 0, 1), (-1, -1, -1)),
        ((-2, -1, 0), (0, 1, 1), (2, 0, -1)),
    )
    comparisons = 0
    phases = ((ONE, ONE, ONE), (IMAGINARY_UNIT, ONE, ONE))
    for p, q, r in examples:
        representatives = sorted({unoriented(p), unoriented(q), unoriented(r)})
        start = 4 * representatives.index(unoriented(p))
        reduced_rows = direct_target_rows(p, q, r)
        full_rows: List[List[Fraction]] = []
        for a, b, c in product(
            transverse_basis(p), transverse_basis(q), transverse_basis(r)
        ):
            for phase in phases:
                row = invariant_row(
                    exact_triad_modes(p, q, r, a, b, c, phase), representatives
                )[start : start + 4]
                if any(row):
                    full_rows.append(row)
        assert reduced_rows == full_rows
        comparisons += len(full_rows)
    return comparisons


def check_local_determination(box: int = 1) -> Tuple[int, int]:
    """Exhaustively check the sharp unequal-length condition in a box."""
    vectors = nonzero_vectors(box)
    checked = 0
    full_rank = 0
    for p in vectors:
        for q in vectors:
            r = neg(add(p, q))
            if r not in vectors or cross(p, q) == (0, 0, 0):
                continue
            rank = target_rank(p, q, r)
            # Equal-length inputs generate only the normal direction at p.
            # Hermiticity then kills the corresponding row and column but
            # leaves one real eigenvalue free, hence rank three rather than
            # four.
            expected = 4 if norm2(q) != norm2(r) else 3
            assert rank == expected, (p, q, r, rank, expected)
            checked += 1
            full_rank += rank == 4
    return checked, full_rank


def can_determine(target: Vec, known: Set[Vec]) -> bool:
    """Whether target is determined by two known unequal-length summands."""
    for q in known:
        r = tuple(target[i] - q[i] for i in range(3))
        if r not in known:
            continue
        if cross(q, r) != (0, 0, 0) and norm2(q) != norm2(r):
            return True
    return False


def propagated_box(box: int) -> Tuple[int, int, int]:
    """Close the seed under the local lemma inside a finite target box."""
    targets = set(nonzero_vectors(box))
    # Keep all signed seed modes, even when the target box is larger.
    known = set(boolean_seed_vectors())
    known &= targets
    rounds = 0
    while True:
        additions = {k for k in targets - known if can_determine(k, known)}
        if not additions:
            break
        known |= additions
        rounds += 1
    return len(known), len(targets), rounds


def constructive_propagated_box(box: int) -> Tuple[int, int]:
    """Replay the explicit axis-plus-l1 induction from the written proof."""
    targets = set(nonzero_vectors(box))
    known = set(boolean_seed_vectors())

    def basis(index: int) -> Vec:
        return tuple(1 if coordinate == index else 0 for coordinate in range(3))  # type: ignore[return-value]

    def scaled(scale: int, vector: Vec) -> Vec:
        return tuple(scale * component for component in vector)  # type: ignore[return-value]

    def certify(target: Vec, q: Vec, r: Vec) -> None:
        assert add(q, r) == target
        assert q in known and r in known
        assert cross(q, r) != (0, 0, 0)
        assert norm2(q) != norm2(r)
        known.add(target)
        known.add(neg(target))

    # Bootstrap the rest of the unit cube.  First produce the three missing
    # body diagonals from an axis and the opposite face diagonal; then produce
    # the three missing face diagonals from a body diagonal and an axis.
    e1, e2, e3 = basis(0), basis(1), basis(2)
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

    # First propagate along all coordinate axes.
    for i in range(3):
        j = (i + 1) % 3
        ei, ej = basis(i), basis(j)
        off_axis = add(scaled(2, ei), ej)
        certify(off_axis, ei, add(ei, ej))
        certify(scaled(2, ei), off_axis, neg(ej))
        for n in range(2, box):
            off_axis = add(scaled(n + 1, ei), ej)
            certify(off_axis, scaled(n, ei), add(ei, ej))
            certify(scaled(n + 1, ei), off_axis, neg(ej))

    # Then use the l1 induction for every genuinely multi-axis target.
    for l1_norm in range(3, 3 * box + 1):
        for target in sorted(targets):
            if sum(abs(component) for component in target) != l1_norm:
                continue
            if sum(component != 0 for component in target) < 2:
                continue
            j = next(
                index
                for index, component in enumerate(target)
                if component != 0
            )
            sign = 1 if target[j] > 0 else -1
            step = scaled(sign, basis(j))
            remainder = tuple(target[i] - step[i] for i in range(3))
            certify(target, remainder, step)  # type: ignore[arg-type]

    return len(known & targets), len(targets)


def main() -> None:
    rank, dimension, seed_rows = seed_certificate()
    assert (rank, dimension) == (26, 28)
    modular_ranks = {
        prime: rank_mod_prime(seed_rows, prime)
        for prime in (1_000_003, 1_000_000_007)
    }
    assert set(modular_ranks.values()) == {26}
    print(
        "Seven-mode Boolean seed certificate: PASS "
        f"({len(seed_rows)} exact equations; rational rank {rank}; "
        f"modular ranks {modular_ranks}; nullity {dimension - rank})"
    )

    comparisons = check_direct_target_formula()
    print(f"Reduced target formula: PASS ({comparisons} rows match full convolution)")

    checked, full_rank = check_local_determination()
    print(
        "Local determination lemma: PASS "
        f"({checked} signed target triads; {full_rank} unequal-length full-rank cases)"
    )

    for box in (2, 3, 4):
        reached, total, rounds = propagated_box(box)
        assert reached == total
        print(
            f"Mode propagation box {box}: PASS "
            f"({reached}/{total} nonzero modes reached in {rounds} rounds)"
        )

    reached, total = constructive_propagated_box(10)
    assert reached == total
    print(
        "Explicit lattice induction: PASS "
        f"({reached}/{total} nonzero modes reached in coordinate box 10)"
    )

    print("Global full-multiplier rigidity checks passed.")


if __name__ == "__main__":
    main()
