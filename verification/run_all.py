#!/usr/bin/env python3
"""Run every active exact-arithmetic verifier in an isolated subprocess."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys
from time import monotonic


VERIFICATION_DIR = Path(__file__).resolve().parent
REPOSITORY_ROOT = VERIFICATION_DIR.parent
PATTERNS = ("audit_*.py", "explore_*.py", "verify_*.py")


def scripts() -> list[Path]:
    return sorted({path for pattern in PATTERNS for path in VERIFICATION_DIR.glob(pattern)})


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

    selected = scripts()
    if not selected:
        print("No verification programs found.", file=sys.stderr)
        return 2

    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    failed: list[str] = []
    suite_start = monotonic()

    for path in selected:
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
                print(result.stderr, end="" if result.stderr.endswith("\n") else "\n", file=sys.stderr)
            failed.append(path.name)

    elapsed = monotonic() - suite_start
    if failed:
        print(f"Suite failed: {len(failed)}/{len(selected)} programs in {elapsed:.3f}s")
        return 1

    print(f"Suite passed: {len(selected)}/{len(selected)} programs in {elapsed:.3f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
