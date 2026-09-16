#!/usr/bin/env python3
"""Run the exact checks used by the Fourier-multiplier classification.

This is the maintained working-tree entrypoint for the computer-assisted
parts of the theorem.  Each verifier runs in an isolated subprocess so that
module state cannot leak between certificates.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
from time import monotonic


VERIFICATION_DIR = Path(__file__).resolve().parent
REPOSITORY_ROOT = VERIFICATION_DIR.parent
MANIFEST_PATH = VERIFICATION_DIR / "fourier_multiplier_manifest.json"
PROGRAMS = (
    "verify_laplacian_rigidity.py",
    "explore_full_multiplier.py",
    "verify_full_multiplier_rigidity.py",
    "verify_general_multiplier_rigidity.py",
    "audit_general_multiplier_certificate.py",
    "verify_unrestricted_output_rigidity.py",
    "audit_unrestricted_output_certificate.py",
    "verify_minimal_boolean_seed.py",
    "verify_solenoidal_seed_semantics.py",
    "verify_sparse_certificate.py",
    "verify_local_conditioning.py",
    "verify_strain_vorticity_pullback.py",
    "verify_publication_certificate_index.py",
    "verify_lean_source_hygiene.py",
)


def git_revision() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=REPOSITORY_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else "unavailable"


def git_worktree_state() -> str:
    result = subprocess.run(
        ["git", "status", "--short"],
        cwd=REPOSITORY_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        return "unavailable"
    return "clean" if not result.stdout.strip() else "dirty"


def validate_manifest() -> int:
    try:
        manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        print(f"Invalid classification manifest: {error}", file=sys.stderr)
        return 2
    if manifest.get("schema_version") != 1:
        print("Unsupported classification manifest schema.", file=sys.stderr)
        return 2
    if tuple(manifest.get("programs", ())) != PROGRAMS:
        print("Classification manifest program list is out of sync.", file=sys.stderr)
        return 2
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--timeout",
        type=float,
        default=300.0,
        help="per-program timeout in seconds (default: 300)",
    )
    parser.add_argument(
        "--show-output",
        action="store_true",
        help="print successful program output as well as failures",
    )
    args = parser.parse_args()

    manifest_status = validate_manifest()
    if manifest_status:
        return manifest_status

    paths = [VERIFICATION_DIR / name for name in PROGRAMS]
    missing = [path.name for path in paths if not path.is_file()]
    if missing:
        print(
            f"Missing classification verifier(s): {', '.join(missing)}",
            file=sys.stderr,
        )
        return 2

    print(f"Python: {platform.python_version()} ({sys.executable})")
    print(f"Platform: {platform.platform()}")
    print(f"Git revision: {git_revision()}")
    print(f"Working tree: {git_worktree_state()}")
    print(f"Manifest: {MANIFEST_PATH.relative_to(REPOSITORY_ROOT)} (schema 1)")

    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    failed: list[str] = []
    suite_start = monotonic()

    for path in paths:
        started = monotonic()
        try:
            result = subprocess.run(
                [sys.executable, "-B", str(path)],
                cwd=REPOSITORY_ROOT,
                env=environment,
                capture_output=True,
                text=True,
                timeout=args.timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as error:
            elapsed = monotonic() - started
            print(f"FAIL {path.name} (timeout after {elapsed:.3f}s)")
            if error.stdout:
                print(error.stdout)
            if error.stderr:
                print(error.stderr, file=sys.stderr)
            failed.append(path.name)
            continue

        elapsed = monotonic() - started
        if result.returncode == 0:
            print(f"PASS {path.name} ({elapsed:.3f}s)")
            if args.show_output and result.stdout:
                print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
        else:
            print(f"FAIL {path.name} (exit {result.returncode}; {elapsed:.3f}s)")
            if result.stdout:
                print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
            if result.stderr:
                print(
                    result.stderr,
                    end="" if result.stderr.endswith("\n") else "\n",
                    file=sys.stderr,
                )
            failed.append(path.name)

    elapsed = monotonic() - suite_start
    if failed:
        print(
            f"Classification suite failed: {len(failed)}/{len(paths)} "
            f"in {elapsed:.3f}s"
        )
        return 1

    print(
        f"Classification suite passed: {len(paths)}/{len(paths)} "
        f"in {elapsed:.3f}s"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

