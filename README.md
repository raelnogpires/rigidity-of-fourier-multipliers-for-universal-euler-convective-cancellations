# Rigidity of Fourier Multipliers for Universal Euler Convective Cancellations

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22819121.svg)](https://doi.org/10.5281/zenodo.22819121)
[![License: CC BY 4.0](https://img.shields.io/badge/License-CC%20BY%204.0-lightgrey.svg)](https://creativecommons.org/licenses/by/4.0/)

Release repository accompanying the paper by Rael Nogueira Pires.

## Contents

- `paper/` — arXiv-ready LaTeX source, bibliography, `.bbl`, and frozen
  certificate supplement.
- `verification/` — exact-arithmetic certificate programs and their manifest.
- `lean/` — Lean 4 formalization with Mathlib.

## Reproduction

Build the publication-critical exact checks from this directory:

```sh
python3 -B verification/run_fourier_multiplier_checks.py
```

Run the complete Python suite with `python3 -B verification/run_all.py`.
Build the Lean development with the repository-local toolchain described in
`lean/README.md`.

Build the paper from `paper/` with:

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
bibtex manuscript
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
```

The release identifier is the immutable Git tag or archival DOI assigned to
this repository snapshot. Retain it when citing or archiving these materials.

## Citation

Each release is archived on Zenodo. Cite the concept DOI [10.5281/zenodo.22819121](https://doi.org/10.5281/zenodo.22819121)
to refer to the work as a whole; it always resolves to the newest release. To
pin the exact snapshot you used, cite that release's own version DOI, listed
under "Versions" on the Zenodo record.

Note that v1.0.3 and earlier were archived before this repository carried a
license file; those snapshots were published under the MIT License. CC BY 4.0
applies from v1.0.4 onward.

> Nogueira Pires, R. (2026). *Certificate programs and Lean 4 formalization
> for "Rigidity of Fourier Multipliers for Universal Euler Convective
> Cancellations"* (v1.0.6) [Software]. Zenodo.
> https://doi.org/10.5281/zenodo.22819121

Machine-readable citation metadata is in
[`CITATION.cff`](CITATION.cff); the metadata published with each Zenodo release
is pinned by [`.zenodo.json`](.zenodo.json).

## Releasing

Zenodo mints a new version DOI from each published GitHub release, and takes
its metadata from [`.zenodo.json`](.zenodo.json), so that file is the single
place to edit citation metadata. Before tagging a release, update the tag name
recorded in [`paper/supplement/verification-notes.md`](paper/supplement/verification-notes.md)
— under "Recorded run" and "Release provenance" — and re-run the entry point so
the recorded result matches the snapshot being archived.

## Scope and trust boundary

The certificate programs use exact integer, rational, or modular arithmetic;
they do not replace the analytic proofs. The Lean development contains no
admitted proofs, but selected finite computations use `native_decide` and thus
trust the Lean compiler, runtime, and GMP. The physical-to-matrix provenance
for the Hermitian seed is additionally checked by the independent Python
semantic verifier. See `paper/supplement/verification-notes.md` and
`lean/README.md` for the full boundary.

## License

All contents of this repository — the manuscript, the verification programs,
and the Lean formalization — are licensed under the
[Creative Commons Attribution 4.0 International License](https://creativecommons.org/licenses/by/4.0/)
(CC BY 4.0). You may share and adapt the material for any purpose, including
commercially, provided you give appropriate credit.

When reusing the verification programs or the Lean development, note that
CC BY 4.0 is a content license: it grants no explicit patent rights and
imposes no source-availability obligation. Attribute this repository by its
immutable Git tag or archival DOI.

Releases up to and including v1.0.3 were published under the MIT License;
that grant remains in effect for those snapshots.
