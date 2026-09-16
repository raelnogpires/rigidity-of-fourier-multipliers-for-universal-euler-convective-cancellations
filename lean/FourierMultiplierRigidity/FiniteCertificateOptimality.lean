import FourierMultiplierRigidity.SolenoidalSeedCertificate

/-!
# Finite certificate optimality

This module formalizes the finite-dimensional optimality argument used in
Theorem D.  A family of `E` real scalar field evaluations is represented by
its evaluation matrix with `E` rows.  Rank-nullity proves that a certificate
with a `K`-dimensional unavoidable kernel in a `P`-parameter symbol space must
have at least `P-K` rows.  Coordinate certificates show that this bound is
sharp as a statement of linear algebra, and the three parameter/kernel counts
from Theorem D are instantiated explicitly.
-/

namespace FourierMultiplierRigidity.FiniteCertificate

open Module

/-- The nullity of a real evaluation matrix. -/
noncomputable def nullity {E P : Nat} (A : Matrix (Fin E) (Fin P) ℝ) : Nat :=
  finrank ℝ (LinearMap.ker A.mulVecLin)

/-- An exact scalar certificate is its evaluation matrix together with the
proof that the unavoidable kernel has precisely dimension `K`.  The row
type has the optimal cardinality `P-K` by construction. -/
structure ExactScalarCertificate (P K : Nat) where
  evaluations : Matrix (Fin (P - K)) (Fin P) ℝ
  exactKernel : nullity evaluations = K

/-- Rank-nullity plus `rank ≤ number of rows`: `E` scalar evaluations on a
`P`-parameter space with nullity `K` force `P ≤ E + K`. -/
theorem evaluation_lower_bound {E P K : Nat}
    (A : Matrix (Fin E) (Fin P) ℝ) (hnull : nullity A = K) :
    P ≤ E + K := by
  have hrank : A.rank ≤ E := Matrix.rank_le_height A
  have hdim : A.rank + nullity A = P := by
    simpa [Matrix.rank, nullity] using
      A.mulVecLin.finrank_range_add_finrank_ker
  omega

/-- The coordinate certificate retaining the first `P-K` coordinates. -/
def coordinateCertificate (P K : Nat) :
    Matrix (Fin (P - K)) (Fin P) ℝ :=
  fun i j => if j.val = i.val then 1 else 0

theorem coordinateCertificate_rank (P K : Nat) :
    (coordinateCertificate P K).rank = P - K := by
  let col : Fin (P - K) → Fin P := fun j =>
    ⟨j.val, lt_of_lt_of_le j.isLt (Nat.sub_le P K)⟩
  have hminor :
      (coordinateCertificate P K).submatrix id col =
        (1 : Matrix (Fin (P - K)) (Fin (P - K)) ℝ) := by
    ext i j
    simp [coordinateCertificate, col, Matrix.one_apply, Fin.ext_iff, eq_comm]
  have hlo : P - K ≤ (coordinateCertificate P K).rank := by
    simpa [hminor] using
      Matrix.rank_submatrix_le (coordinateCertificate P K) id col
  have hhi := Matrix.rank_le_height (coordinateCertificate P K)
  omega

/-- The coordinate certificate realizes every admissible kernel dimension. -/
theorem coordinateCertificate_nullity (P K : Nat) (hKP : K ≤ P) :
    nullity (coordinateCertificate P K) = K := by
  have hdim :
      (coordinateCertificate P K).rank +
          nullity (coordinateCertificate P K) = P := by
    simpa [Matrix.rank, nullity] using
      (coordinateCertificate P K).mulVecLin.finrank_range_add_finrank_ker
  rw [coordinateCertificate_rank P K] at hdim
  omega

/-- Exact sharpness of the scalar-evaluation count `P-K`. -/
theorem scalar_certificate_optimality (P K : Nat) (hKP : K ≤ P) :
    (∃ A : Matrix (Fin (P - K)) (Fin P) ℝ, nullity A = K) ∧
    (∀ {E : Nat} (A : Matrix (Fin E) (Fin P) ℝ),
      nullity A = K → P - K ≤ E) := by
  constructor
  · exact ⟨coordinateCertificate P K,
      coordinateCertificate_nullity P K hKP⟩
  · intro E A hnull
    have h := evaluation_lower_bound A hnull
    omega

/-! ## The three classes in Theorem D -/

/-- A complex solenoidal symbol on `M` unoriented modes has `8M` real
parameters and a two-dimensional energy-helicity kernel, hence at least
`8M-2` scalar evaluations are necessary. -/
theorem complexSolenoidal_minimal {M E : Nat}
    (A : Matrix (Fin E) (Fin (8 * M)) ℝ) (hnull : nullity A = 2) :
    8 * M - 2 ≤ E := by
  have h := evaluation_lower_bound A hnull
  omega

/-- A Hermitian solenoidal symbol on `M` unoriented modes has `4M` real
parameters and the same two-dimensional kernel. -/
theorem hermitianSolenoidal_minimal {M E : Nat}
    (A : Matrix (Fin E) (Fin (4 * M)) ℝ) (hnull : nullity A = 2) :
    4 * M - 2 ≤ E := by
  have h := evaluation_lower_bound A hnull
  omega

/-- An unrestricted-output symbol on `M` unoriented modes has `12M` real
parameters and the twelve-dimensional symmetric-generator kernel. -/
theorem unrestrictedOutput_minimal {M E : Nat}
    (A : Matrix (Fin E) (Fin (12 * M)) ℝ) (hnull : nullity A = 12) :
    12 * M - 12 ≤ E := by
  have h := evaluation_lower_bound A hnull
  omega

/-- Abstract sharp certificates with the complex-solenoidal count exist. -/
theorem complexSolenoidal_abstract_sharp (M : Nat) (hM : 1 ≤ M) :
    ∃ A : Matrix (Fin (8 * M - 2)) (Fin (8 * M)) ℝ,
      nullity A = 2 :=
  (scalar_certificate_optimality (8 * M) 2 (by omega)).1

/-- Abstract sharp certificates with the Hermitian-solenoidal count exist. -/
theorem hermitianSolenoidal_abstract_sharp (M : Nat) (hM : 1 ≤ M) :
    ∃ A : Matrix (Fin (4 * M - 2)) (Fin (4 * M)) ℝ,
      nullity A = 2 :=
  (scalar_certificate_optimality (4 * M) 2 (by omega)).1

/-- Abstract sharp certificates with the unrestricted-output count exist. -/
theorem unrestrictedOutput_abstract_sharp (M : Nat) (hM : 1 ≤ M) :
    ∃ A : Matrix (Fin (12 * M - 12)) (Fin (12 * M)) ℝ,
      nullity A = 12 :=
  (scalar_certificate_optimality (12 * M) 12 (by omega)).1

/-! ## Packaged sharp certificates and the certified Hermitian seed -/

/-- Every admissible parameter/kernel pair has an exact optimal certificate. -/
noncomputable def exactCoordinateCertificate (P K : Nat) (hKP : K ≤ P) :
    ExactScalarCertificate P K where
  evaluations := coordinateCertificate P K
  exactKernel := coordinateCertificate_nullity P K hKP

/-- The Boolean seed is not an arbitrary coordinate projection: this is the
actual denominator-free `26 × 28` evaluation matrix checked in
`SolenoidalSeedCertificate`, packaged as an exact certificate. -/
noncomputable def booleanHermitianSeedCertificate :
    ExactScalarCertificate 28 2 where
  evaluations :=
    SolenoidalSeedCertificate.booleanSeedMatrixR
  exactKernel := by
    exact SolenoidalSeedCertificate.booleanSeedMatrixR_nullity

/-- Complete finite-dimensional content of Theorem D: the three sharp row
counts are simultaneously attainable, and every scalar evaluation matrix
with the asserted exact kernel needs at least that many rows. -/
theorem theoremD_exact_scalar_counts (M : Nat) (hM : 1 ≤ M) :
    (∃ A : Matrix (Fin (8 * M - 2)) (Fin (8 * M)) ℝ, nullity A = 2) ∧
    (∃ A : Matrix (Fin (4 * M - 2)) (Fin (4 * M)) ℝ, nullity A = 2) ∧
    (∃ A : Matrix (Fin (12 * M - 12)) (Fin (12 * M)) ℝ, nullity A = 12) ∧
    (∀ {E : Nat} (A : Matrix (Fin E) (Fin (8 * M)) ℝ),
      nullity A = 2 → 8 * M - 2 ≤ E) ∧
    (∀ {E : Nat} (A : Matrix (Fin E) (Fin (4 * M)) ℝ),
      nullity A = 2 → 4 * M - 2 ≤ E) ∧
    (∀ {E : Nat} (A : Matrix (Fin E) (Fin (12 * M)) ℝ),
      nullity A = 12 → 12 * M - 12 ≤ E) := by
  refine ⟨complexSolenoidal_abstract_sharp M hM,
    hermitianSolenoidal_abstract_sharp M hM,
    unrestrictedOutput_abstract_sharp M hM, ?_, ?_, ?_⟩
  · intro E A h
    exact complexSolenoidal_minimal A h
  · intro E A h
    exact hermitianSolenoidal_minimal A h
  · intro E A h
    exact unrestrictedOutput_minimal A h

end FourierMultiplierRigidity.FiniteCertificate
