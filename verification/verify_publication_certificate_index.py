#!/usr/bin/env python3
"""Check that the publication certificate index matches the exact verifiers."""

from __future__ import annotations

import json
from pathlib import Path

from verify_full_multiplier_rigidity import BOOLEAN_SEED_REPRESENTATIVES, nonzero_vectors
from verify_general_multiplier_rigidity import (
    EXPECTED_MINOR_DETERMINANTS as SOLENOIDAL_DETERMINANTS,
    EXPECTED_PIVOT_COLUMNS as SOLENOIDAL_PIVOTS,
    EXPECTED_SELECTED_INDICES as SOLENOIDAL_ROWS,
    SEED_PRIMES,
)
from verify_laplacian_rigidity import unoriented
from verify_unrestricted_output_rigidity import (
    CERTIFICATE_PIVOT_COLUMNS as UNRESTRICTED_PIVOTS,
    CERTIFICATE_PRIMES,
    CERTIFICATE_ROW_INDICES as UNRESTRICTED_ROWS,
    EXPECTED_MINOR_DETERMINANTS as UNRESTRICTED_DETERMINANTS,
    EXPECTED_ROW_DIGEST,
)


REPOSITORY_ROOT = Path(__file__).resolve().parent.parent
# The supplement sits under the manuscript tree in the working repository and
# directly under paper/ in the standalone release repository.
CANDIDATE_INDEX_PATHS = (
    REPOSITORY_ROOT
    / "publishing"
    / "fourier-multiplier-rigidity"
    / "manuscript"
    / "supplement"
    / "certificate-index.json",
    REPOSITORY_ROOT / "paper" / "supplement" / "certificate-index.json",
)


def resolve_index_path() -> Path:
    for candidate in CANDIDATE_INDEX_PATHS:
        if candidate.is_file():
            return candidate
    searched = "\n  ".join(str(path) for path in CANDIDATE_INDEX_PATHS)
    raise FileNotFoundError(
        f"certificate-index.json not found in any known layout:\n  {searched}"
    )


INDEX_PATH = resolve_index_path()


def tuples(values: list[list[int]]) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(value) for value in values)


def main() -> int:
    data = json.loads(INDEX_PATH.read_text(encoding="utf-8"))
    assert data["schema_version"] == 1
    assert data["conventions"]["index_base"] == 0

    solenoidal = data["certificates"]["complex_solenoidal_seed"]
    assert tuples(solenoidal["representatives"]) == BOOLEAN_SEED_REPRESENTATIVES
    assert tuple(solenoidal["selected_row_indices"]) == SOLENOIDAL_ROWS
    assert tuple(solenoidal["pivot_columns"]) == SOLENOIDAL_PIVOTS
    assert tuple(solenoidal["primes"]) == SEED_PRIMES
    assert tuple(solenoidal["determinant_residues"]) == SOLENOIDAL_DETERMINANTS
    assert solenoidal["parameters_per_mode"] == [
        "Re R11", "Im R11", "Re R12", "Im R12",
        "Re R21", "Im R21", "Re R22", "Im R22",
    ]

    unrestricted = data["certificates"]["complex_unrestricted_output_seed"]
    unit_box_representatives = tuple(
        sorted({unoriented(mode) for mode in nonzero_vectors(1)})
    )
    assert tuples(unrestricted["representatives"]) == unit_box_representatives
    assert tuple(unrestricted["selected_row_indices"]) == UNRESTRICTED_ROWS
    assert tuple(unrestricted["pivot_columns"]) == UNRESTRICTED_PIVOTS
    assert tuple(unrestricted["primes"]) == CERTIFICATE_PRIMES
    assert (
        tuple(unrestricted["determinant_residues"])
        == UNRESTRICTED_DETERMINANTS
    )
    assert unrestricted["complete_row_sha256"] == EXPECTED_ROW_DIGEST
    assert unrestricted["parameters_per_mode"] == [
        "Re R11", "Im R11", "Re R12", "Im R12",
        "Re R21", "Im R21", "Re R22", "Im R22",
        "Re R31", "Im R31", "Re R32", "Im R32",
    ]

    print(f"publication certificate index matches exact sources: {INDEX_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
