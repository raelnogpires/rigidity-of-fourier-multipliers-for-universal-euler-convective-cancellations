# Exact verification programs

The programs in this directory use exact integer, rational, or Gaussian
rational arithmetic.  They are executable certificates and regression tests,
not substitutes for the analytic proofs or for independent peer review.

Run the complete active suite from the repository root:

```sh
python3 -B verification/run_all.py
```

For the Fourier-multiplier classification alone, use the shorter maintained
entrypoint:

```sh
python3 -B verification/run_fourier_multiplier_checks.py
```

It runs the primary and independent seed certificates, lattice propagation,
sparse optimality, and local-conditioning checks in isolated subprocesses.
The expected ranks, modular minors, row digest, and local block ranks are
recorded in [`fourier_multiplier_manifest.json`](fourier_multiplier_manifest.json).

An independent SageMath reproduction of the two finite seed certificates is
also available:

```sh
conda run -n sage python verification/reproduce_seed_certificates_sage.py
```

With a traditional SageMath distribution rather than the conda-forge
package, use

```sh
sage -python verification/reproduce_seed_certificates_sage.py
```

It reconstructs the Fourier convolution rows without importing the Python
verifiers, then checks the seven-mode `56 -> 54` and unit-cube `156 -> 144`
ranks, their explicit kernels, fixed modular minors, and deterministic
certificate data.  SageMath is optional and is not required by either runner
above.  The Sage verifier performs no file writes.

## Groups

| Group | Programs |
|---|---|
| Scalar, helical, and full rigidity | `verify_laplacian_rigidity.py`, `explore_full_multiplier.py`, `verify_full_multiplier_rigidity.py` |
| General and unrestricted output | `verify_general_multiplier_rigidity.py`, `audit_general_multiplier_certificate.py`, `verify_unrestricted_output_rigidity.py`, `audit_unrestricted_output_certificate.py` |
| Independent SageMath seeds | `reproduce_seed_certificates_sage.py` |
| Minimality, sparsity, conditioning | `verify_minimal_boolean_seed.py`, `verify_sparse_certificate.py`, `verify_local_conditioning.py` |
| Tensorial and wall flux | `verify_tensorial_miller_identity.py`, `verify_no_slip_tensorial_flux.py`, `verify_flat_channel_wall_flux.py` |
| Vorticity geometry | `verify_vorticity_compatibility_geometry.py`, `verify_vorticity_only_identity.py` |
| Adaptive metrics and atlas | `verify_adaptive_miller_metric.py`, `verify_adaptive_anisotropic_energy.py`, `verify_scale_normalized_barrier_atlas.py`, `verify_tetrahedral_gram_transversality.py` |
| Active subspace and Gram shape | `verify_active_subspace_geometry.py`, `verify_planarity_shape_dynamics.py`, `verify_whitened_gram_shape.py`, `verify_gram_shape_coordinates.py`, `verify_gram_shape_orbit.py`, `verify_gram_isotropic_cusp.py` |

The former publication package contained an older frozen copy of part of this
suite.  That duplicate package was removed; these are now the only maintained
verifier sources in the working tree.


## Strain–vorticity regression checks

`verify_strain_vorticity_pullback.py` uses rational Gaussian arithmetic to
compare direct symmetric-gradient contractions with convective contractions.
It checks the inverse-curl sign, all twelve generator directions, the actual
anisotropic operator against its symbol, the Hessian defect, and an explicit
counterexample to the formerly claimed unweighted Miller cancellation.
These are finite regression checks, not universal proofs.

`verify_lean_source_hygiene.py` rejects admitted proofs and user axioms after
removing nested comments and strings. It cannot detect a mathematically wrong
theorem statement; the semantic regressions and Lean build are separate gates.
