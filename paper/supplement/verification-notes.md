# Verification notes

Human-readable description of the computer-assisted components cited by
[`../manuscript.tex`](../manuscript.tex) §10 and Appendix A. This file
describes the release contents. The immutable Git tag or archival identifier
must be recorded here when this repository snapshot is published.

## What the manuscript relies on

| Manuscript location | Computer-assisted content |
|---|---|
| §6.1, eq. (6.2)–(6.4) | complex solenoidal seed: 720 rows, rank 54 of 56; Hermitian restriction: 592 rows, rank 26 of 28 |
| §6.1 | unit-cube minimality: all 4095 subsets of at most six modes |
| §6.2, eq. (6.6)–(6.9) | unrestricted-output seed: 680 rows, rank 144 of 156; canonical row digest |
| §5.3, eq. (5.10) | local projected ranks 8/4 on all 264 signed unit-box triads |
| §7.1–§7.2 | finite replay of both propagation orders through radius ten |
| §8.1–§8.3 | exact singular-value formulas and the sharp constants 1/10 and √15 |
| §9.1 | curl-pullback identity and the explicit negative control |

[certificate-index.json](certificate-index.json) exports the zero-based
selected row indices, pivot columns, mode order, parameter order, primes and
determinant residues for both nonsingular seed minors. Its entries duplicate
constants asserted by the exact verification programs so that the certificate
can be reconstructed without extracting constants from Python source.

Everything else in the paper is analytic. No floating-point rank decision and
no numerical tolerance enters any certificate: the programs use integers,
Python `Fraction` arithmetic, or exact reductions modulo primes.

## Commands

From the repository root:

```sh
python3 -B verification/run_fourier_multiplier_checks.py   # publication-critical
python3 -B verification/run_all.py                         # complete suite
```

The Lean development is built separately with the repository-local toolchain:

```sh
ELAN_HOME="$PWD/.lean-toolchain-local" .lean-toolchain-local/bin/lake build
lake env lean lean/CheckAxioms.lean
```

## Recorded run

| Field | Value |
|---|---|
| Date | 16 September 2026 |
| Entrypoint | `verification/run_fourier_multiplier_checks.py` |
| Result | 12 of 12 programs passed, 195.5 s |
| Python | 3.11.15 |
| Platform | Linux x86-64, glibc 2.39 |
| Git revision | record the release commit here |
| Working tree | release snapshot |
| Manifest | `verification/fourier_multiplier_manifest.json`, schema 1 |

Programs executed, all passing: `verify_laplacian_rigidity.py`,
`explore_full_multiplier.py`, `verify_full_multiplier_rigidity.py`,
`verify_general_multiplier_rigidity.py`,
`audit_general_multiplier_certificate.py`,
`verify_unrestricted_output_rigidity.py`,
`audit_unrestricted_output_certificate.py`,
`verify_minimal_boolean_seed.py`, `verify_sparse_certificate.py`,
`verify_local_conditioning.py`, `verify_strain_vorticity_pullback.py`,
`verify_lean_source_hygiene.py`.

The two `audit_*` programs import neither the corresponding Fourier row
builders nor the row reducers; they reconstruct the convolution by recipient
wavevector, so their agreement is meaningful implementation independence. Both
are written in Python, so a re-implementation in a second computer-algebra
system would strengthen the evidence further. This is stated in §10.2 of the
manuscript and must not be overclaimed.

The recorded working-tree snapshot above did not include a Lean build. The
complete pull-request workflow subsequently passed the exact suite, `lake
build`, the axiom report, and the manuscript build on 12 September 2026; see
[workflow run 20](https://github.com/raelnogpires/navier-stokes-analysis/actions/runs/34718675068). The manuscript's §10.3 trust boundary remains
controlled by [`../../../../lean/README.md`](../../../../lean/README.md).

## Manuscript build

`manuscript.tex` and `references.bib` compile from a clean directory with a
standard TeX Live installation and no other input files:

```sh
pdflatex manuscript && bibtex manuscript && pdflatex manuscript && pdflatex manuscript
```

Recorded result: 34 pages, no errors, no undefined references or citations.
Package dependencies are `amsmath`, `amssymb`, `amsthm`, `mathtools`,
`geometry` and `hyperref`, all in `texlive-latex-base` and
`texlive-latex-recommended`. There are no figures and no vendor sample files.

## Release checklist

- create and retain an immutable release tag;
- record the release commit or archival identifier in this file;
- verify that the manifest and certificate index match that tag;
- cite the immutable release identifier alongside the paper.
