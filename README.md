# Rigidity of Fourier Multipliers for Universal Euler Convective Cancellations

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

## Scope and trust boundary

The certificate programs use exact integer, rational, or modular arithmetic;
they do not replace the analytic proofs. The Lean development contains no
admitted proofs, but selected finite computations use `native_decide` and thus
trust the Lean compiler, runtime, and GMP. The physical-to-matrix provenance
for the Hermitian seed is additionally checked by the independent Python
semantic verifier. See `paper/supplement/verification-notes.md` and
`lean/README.md` for the full boundary.
