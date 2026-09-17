# Verification notes

Human-readable description of the computer-assisted components cited by
[`../manuscript.tex`](../manuscript.tex) §10 and Appendix A. This file
describes the contents of release `v1.0.5`, archived on Zenodo under the
concept DOI [10.5281/zenodo.22819121](https://doi.org/10.5281/zenodo.22819121),
which resolves to the most recent release and lists the version DOI of each
individual snapshot.

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
| Date | 17 September 2026 |
| Entrypoint | `verification/run_fourier_multiplier_checks.py` |
| Result | 14 of 14 programs passed, 304.6 s |
| Python | 3.12.3 |
| Platform | Linux x86-64, glibc 2.39 |
| Git revision | the commit tagged `v1.0.5` in this repository |
| Working tree | clean at that tag |
| Manifest | `verification/fourier_multiplier_manifest.json`, schema 1 |

The run above was performed from a checkout of this repository, so it exercises
the same directory layout that a reader obtains from the archive. The complete
suite, `verification/run_all.py`, was run from the same checkout on the same
date and passed 29 of 29 programs in 558.8 s.

Programs executed, all passing: `verify_laplacian_rigidity.py`,
`explore_full_multiplier.py`, `verify_full_multiplier_rigidity.py`,
`verify_general_multiplier_rigidity.py`,
`audit_general_multiplier_certificate.py`,
`verify_unrestricted_output_rigidity.py`,
`audit_unrestricted_output_certificate.py`,
`verify_minimal_boolean_seed.py`, `verify_solenoidal_seed_semantics.py`,
`verify_sparse_certificate.py`, `verify_local_conditioning.py`,
`verify_strain_vorticity_pullback.py`,
`verify_publication_certificate_index.py`,
`verify_lean_source_hygiene.py`.

The two `audit_*` programs import neither the corresponding Fourier row
builders nor the row reducers; they reconstruct the convolution by recipient
wavevector, so their agreement is meaningful implementation independence. Both
are written in Python, so a re-implementation in a second computer-algebra
system would strengthen the evidence further. This is stated in §10.2 of the
manuscript and must not be overclaimed.

## Recorded Lean build and axiom report

`lake build` was run on 17 September 2026 against the toolchain pinned in
`lean-toolchain` (`leanprover/lean4:v4.33.1`) and completed successfully, 2742
jobs, with no errors. `lake env lean lean/CheckAxioms.lean` then reported the
axiom dependencies of 73 declarations:

| Field | Value |
|---|---|
| `sorryAx` occurrences | none, so no proof is admitted |
| Declarations reported | 73 |
| Declarations free of `native_decide` | 57 |
| Distinct `native_decide` axioms | 11 |
| Reached by `theoremA` and `corollaryB` | 7, through `SeedCertificate` |
| Reached by the Boolean-seed rank and nullity | 4, through `SolenoidalSeedCertificate` |

The two groups of axioms are disjoint, so the classification result and the
Boolean-seed computation rest on different finite evaluations. Every
`native_decide` axiom is an explicit trust boundary: it certifies a finite
computation by compiled evaluation rather than by kernel reduction, and so
trusts the Lean compiler, its runtime and GMP. The manuscript's §10.3 trust
boundary remains controlled by the Lean development's own `README.md`.

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

## Release provenance

- The snapshot is the immutable tag `v1.0.5`, retained in the repository.
- The archival identifier is the Zenodo concept DOI
  [10.5281/zenodo.22819121](https://doi.org/10.5281/zenodo.22819121); the
  version DOI of this snapshot is listed under "Versions" on that record.
- `verify_publication_certificate_index.py` checks
  [certificate-index.json](certificate-index.json) against the constants
  asserted by the exact programs, and runs as part of the entry point above,
  so the manifest and the certificate index are checked at this tag.
- The manuscript cites the concept DOI in its data and code availability
  statement.

## Independent review

The argument and its novelty boundary have not yet had independent specialist
review. The certificates described above are machine-checked; that is a
different and weaker claim than peer review, and is not a substitute for it.
