import FourierMultiplierRigidity.CorollaryB
import FourierMultiplierRigidity.SolenoidalPropagation
import FourierMultiplierRigidity.FiniteCertificateOptimality

/-!
# Theorem D: classification, propagation, and finite optimality

This module combines the qualitative classification, Boolean-seed
propagation, the typed rank-26 Boolean seed matrix, and exact
finite-dimensional matrix counts.  The seed matrix has proved nullity two,
and the lower bounds are consequences of rank-nullity rather than prose.
The external exact verifier `verify_solenoidal_seed_semantics.py` reconstructs
the twenty-six seed rows from explicit Euler test fields; that reconstruction
is not yet an internal kernel-checked Lean theorem.

Trust: `theoremD` inherits Corollary B's native_decide dependencies.
`theoremD_propagation` uses the analytic propagation lemmas. Inspect their
actual dependencies with `lean/CheckAxioms.lean`.
-/

namespace FourierMultiplierRigidity
set_option maxRecDepth 4000000

/-! ## The qualitative classification (= Corollary B) -/

/-- **Theorem D (qualitative).**  A reality-compatible multiplier with
solenoidal output has universal cancellation if and only if it has the scalar
form `R = c I + d curl`.  This is definitionally `corollaryB`. -/
theorem theoremD (R : MultiplierSymbol) (hsol : HasSolenoidalOutput R) :
    UniversalCancellation R ↔ HasScalarForm R :=
  corollaryB R hsol

/-! ## The solenoidal propagation theorem

This is the propagation content beyond Corollary B.  It shows that
vanishing need only be checked on the seven Boolean seed modes — solenoidal
output upgrades the two-triad propagation to a one-triad propagation that
reaches the remaining unit-cube modes, and from there the existing lattice
induction takes over. -/

/-- A symbol family that has active triad cancellation, solenoidal output,
reality compatibility, and vanishes on the seven-mode Boolean seed must vanish
at every nonzero lattice mode. -/
theorem theoremD_propagation
    (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hD : HasActiveTriadCancellation D)
    (hsol : HasSolenoidalOutputMap D)
    (hreal : RealityCompatibleMap D)
    (hB : VanishesOnBooleanSeed D) :
    ∀ k, k ≠ 0 → VanishesAt D k :=
  solenoidal_vanishes_everywhere_of_booleanSeed D hD hsol hreal hB

/-! ## Exact scalar evaluation counts -/

/-- The formal matrix-level finite-optimality statement: for an `M`-mode
parameter space, matrices with the three manuscript row counts and prescribed
nullity exist, and no real scalar matrix with that nullity can have fewer
rows.  The geometric realization by ordered triad tests is a separate part
of Theorem D's analytic/exact certificate argument. -/
theorem theoremD_finite_optimality (M : Nat) (hM : 1 ≤ M) :
    (∃ A : Matrix (Fin (8 * M - 2)) (Fin (8 * M)) ℝ,
      FiniteCertificate.nullity A = 2) ∧
    (∃ A : Matrix (Fin (4 * M - 2)) (Fin (4 * M)) ℝ,
      FiniteCertificate.nullity A = 2) ∧
    (∃ A : Matrix (Fin (12 * M - 12)) (Fin (12 * M)) ℝ,
      FiniteCertificate.nullity A = 12) ∧
    (∀ {E : Nat} (A : Matrix (Fin E) (Fin (8 * M)) ℝ),
      FiniteCertificate.nullity A = 2 → 8 * M - 2 ≤ E) ∧
    (∀ {E : Nat} (A : Matrix (Fin E) (Fin (4 * M)) ℝ),
      FiniteCertificate.nullity A = 2 → 4 * M - 2 ≤ E) ∧
    (∀ {E : Nat} (A : Matrix (Fin E) (Fin (12 * M)) ℝ),
      FiniteCertificate.nullity A = 12 → 12 * M - 12 ≤ E) :=
  FiniteCertificate.theoremD_exact_scalar_counts M hM

/-! ## Certificate construction arithmetic

For an M-mode coordinate box the certificate uses exactly:

* 26 = 4 × 7 − 2 seed tests (on the Boolean seed);
* 4 tests per new mode (one unequal-length triad, rank 4 target block);
* Total: 26 + 4(M − 7) = 4M − 2 tests.

The two-dimensional kernel (energy and helicity) is unavoidable, so 4M − 2
is optimal among all such certificates.

Separate compiler-trusted seed computations are provided in `SolenoidalSeedCertificate.lean`:

```
booleanSeed_rank : rowRankB booleanSeedMatrixF = 26
booleanMinorMatrixR_det_ne_zero : booleanMinorMatrixR.det ≠ 0
energy_in_kernel : ∀ row ∈ booleanSeedMatrixZ, dotRowZ row energyVecZ = 0
helicity_in_kernel : ∀ row ∈ booleanSeedMatrixZ, dotRowZ row helicityVecZ = 0
```
-/

/-! ## Ordered-certificate count identities -/

/-- A 54-row complex-solenoidal seed followed by eight scalar observations
for each of the remaining `M - 7` modes has exactly the sharp count `8M - 2`. -/
theorem complexSolenoidal_ordered_count (M : Nat) (hM : 7 ≤ M) :
    54 + 8 * (M - 7) = 8 * M - 2 := by
  omega

/-- A 26-row Hermitian-solenoidal seed followed by four scalar observations
for each remaining mode has exactly the sharp count `4M - 2`. -/
theorem hermitianSolenoidal_ordered_count (M : Nat) (hM : 7 ≤ M) :
    26 + 4 * (M - 7) = 4 * M - 2 := by
  omega

/-- A 144-row unrestricted seed on thirteen modes followed by twelve scalar
observations for each remaining mode has exactly the sharp count `12M - 12`. -/
theorem unrestrictedOutput_ordered_count (M : Nat) (hM : 13 ≤ M) :
    144 + 12 * (M - 13) = 12 * M - 12 := by
  omega

end FourierMultiplierRigidity
