import FourierMultiplierRigidity.TheoremA
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Theorem A⁰: all-mode completion

This module removes the mean-zero restriction from Theorem A. It introduces
the full space of real, divergence-free trigonometric polynomials, proves that
the zero Fourier block of a multiplier is invisible to the convective cubic
form, and transfers the nonzero-mode classification and uniqueness from
Theorem A.

No new axioms are introduced. `theoremAZero` inherits exactly the finite seed
certificate dependencies of `theoremA` through its necessity direction.
-/

namespace FourierMultiplierRigidity

set_option maxRecDepth 4000000

/-- A real divergence-free trigonometric polynomial with no restriction on
its spatial mean. -/
structure AllModeTrigField where
  coeff : LatticeVec →₀ CVec
  divergenceFree : ∀ k, Transverse k (coeff k)
  reality : ∀ k, coeff (-k) = conjVec (coeff k)

/-- Regard a mean-zero field as an all-mode field. -/
def TrigField.toAllMode (w : TrigField) : AllModeTrigField where
  coeff := w.coeff
  divergenceFree := w.divergenceFree
  reality := w.reality

/-- The Fourier coefficient of `(w · ∇)w` for an all-mode field. -/
noncomputable def allModeConvectiveCoeff
    (w : AllModeTrigField) (k : LatticeVec) : CVec :=
  Complex.I • w.coeff.sum fun p up ↦
    w.coeff.sum fun q uq ↦
      if p + q = k then Vec3.dot (latticeToComplex q) up • uq else 0

/-- The all-mode convective cubic form. -/
noncomputable def allModeCubicForm
    (R : MultiplierSymbol) (w : AllModeTrigField) : ℂ :=
  w.coeff.sum fun k uk ↦
    Vec3.dot (R.map k uk) (allModeConvectiveCoeff w (-k))

/-- Universal cancellation on all real divergence-free trigonometric
polynomials, including fields with nonzero spatial mean. -/
def UniversalAllModeCancellation (R : MultiplierSymbol) : Prop :=
  ∀ w : AllModeTrigField, allModeCubicForm R w = 0

@[simp] theorem allModeCubicForm_toAllMode
    (R : MultiplierSymbol) (w : TrigField) :
    allModeCubicForm R w.toAllMode = cubicForm R w := by
  rfl

/-- All-mode cancellation restricts to the mean-zero cancellation used in
Theorem A. -/
theorem universalCancellation_of_allMode
    (R : MultiplierSymbol) (hR : UniversalAllModeCancellation R) :
    UniversalCancellation R := by
  intro w
  simpa using hR w.toAllMode

/-! ## The zero recipient -/

/-- One ordered interaction on the all-mode phase space. -/
def allModeOrderedInteraction
    (R : LatticeVec → CVec →ₗ[ℂ] CVec) (w : AllModeTrigField)
    (p q r : LatticeVec) : ℂ :=
  if p + q + r = 0 then
    Vec3.dot (R p (w.coeff p))
      (Vec3.dot (w.coeff q) (latticeToComplex r) • w.coeff r)
  else 0

/-- A zero-frequency recipient cannot see periodic convection. This is the
Fourier form of `∫ (w · ∇)w = 0`. -/
theorem allModeOrderedInteraction_zero_recipient
    (R : LatticeVec → CVec →ₗ[ℂ] CVec) (w : AllModeTrigField)
    (q r : LatticeVec) :
    allModeOrderedInteraction R w 0 q r = 0 := by
  unfold allModeOrderedInteraction
  simp only [zero_add]
  by_cases hsum : q + r = 0
  · rw [if_pos hsum]
    have hr : r = -q := by
      funext i
      have hi := congrFun hsum i
      simp at hi ⊢
      omega
    have hq := w.divergenceFree q
    have hscalar :
        Vec3.dot (w.coeff q) (latticeToComplex r) = 0 := by
      rw [hr]
      simp [Transverse, latticeToComplex, Vec3.dot] at hq ⊢
      linear_combination -hq
    rw [hscalar, zero_smul]
    simp [Vec3.dot]
  · rw [if_neg hsum]

/-! ## Finite-sum realization -/

private theorem allMode_finsupp_sum_eq_support_sum
    {α M N : Type*} [Zero M] [AddCommMonoid N]
    (f : α →₀ M) (g : α → M → N) :
    f.sum g = ∑ a ∈ f.support, g a (f a) := by
  rfl

/-- The convolution definition is the complete ordered triple sum. -/
theorem allModeCubicForm_eq_I_mul_tripleSum
    (R : MultiplierSymbol) (w : AllModeTrigField) :
    allModeCubicForm R w = Complex.I *
      tripleSum w.coeff.support (allModeOrderedInteraction R.map w) := by
  classical
  simp [allModeCubicForm, allModeConvectiveCoeff, tripleSum,
    allModeOrderedInteraction, pair_sum_eq_neg_iff_triple_sum_eq_zero,
    Vec3.dot_sum_right, Vec3.dot_smul_right, Finset.mul_sum,
    allMode_finsupp_sum_eq_support_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hsum : p + q + r = 0
  · simp [hsum, Vec3.dot]
    ring
  · simp [hsum, Vec3.dot]

/-! ## Generator cancellation with a nonzero mean -/

theorem generator_allMode_sixPermutationSum_zero
    (A B : RMatrix) (hA : A.transpose = A) (hB : B.transpose = B)
    (w : AllModeTrigField) :
    ∀ p q r,
      sixPermutationSum (allModeOrderedInteraction (generatorMap A B) w)
        p q r = 0 := by
  intro p q r
  by_cases hsum : p + q + r = 0
  · have hprq : p + r + q = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hqpr : q + p + r = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hqrp : q + r + p = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hrpq : r + p + q = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hrqp : r + q + p = 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have htriad := symmetric_generator_triad_cancel A B hA hB p q r
      (w.coeff p) (w.coeff q) (w.coeff r) hsum
      (w.divergenceFree p) (w.divergenceFree q) (w.divergenceFree r)
    simp [sixPermutationSum, allModeOrderedInteraction, hsum, hprq, hqpr,
      hqrp, hrpq, hrqp, triadBracket, rawRecipient, Vec3.dot_add_right,
      Vec3.dot_smul_right] at htriad ⊢
    linear_combination htriad
  · have hprq : p + r + q ≠ 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hqpr : q + p + r ≠ 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hqrp : q + r + p ≠ 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hrpq : r + p + q ≠ 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    have hrqp : r + q + p ≠ 0 := by
      simpa [add_comm, add_left_comm, add_assoc] using hsum
    simp [sixPermutationSum, allModeOrderedInteraction, hsum, hprq, hqpr,
      hqrp, hrpq, hrqp]

theorem generator_allMode_orderedInteraction_sum_zero
    (A B : RMatrix) (hA : A.transpose = A) (hB : B.transpose = B)
    (w : AllModeTrigField) :
    tripleSum w.coeff.support
      (allModeOrderedInteraction (generatorMap A B) w) = 0 :=
  tripleSum_eq_zero_of_six_permutations _ _
    (generator_allMode_sixPermutationSum_zero A B hA hB w)

/-- Agreement on nonzero transverse fibers is sufficient in the all-mode
problem: recipient-zero terms vanish before the multiplier is evaluated. -/
theorem hasGeneratorForm_universalAllModeCancellation
    (R : MultiplierSymbol) (hform : HasGeneratorForm R) :
    UniversalAllModeCancellation R := by
  obtain ⟨A, B, hA, hB, hmap⟩ := hform
  intro w
  rw [allModeCubicForm_eq_I_mul_tripleSum]
  have hinteraction : ∀ p q r,
      allModeOrderedInteraction R.map w p q r =
        allModeOrderedInteraction (generatorMap A B) w p q r := by
    intro p q r
    by_cases hp : p = 0
    · subst p
      rw [allModeOrderedInteraction_zero_recipient,
        allModeOrderedInteraction_zero_recipient]
    · rw [allModeOrderedInteraction, allModeOrderedInteraction,
        hmap p hp (w.coeff p) (w.divergenceFree p)]
  have hsum :
      tripleSum w.coeff.support (allModeOrderedInteraction R.map w) =
        tripleSum w.coeff.support
          (allModeOrderedInteraction (generatorMap A B) w) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    exact hinteraction p q r
  rw [hsum, generator_allMode_orderedInteraction_sum_zero A B hA hB w]
  simp

/-! ## Theorem A⁰ -/

/-- **Theorem A⁰ (all-mode completion).** Universal cancellation on all real
divergence-free trigonometric polynomials holds exactly when the nonzero
Fourier fibers have the unique symmetric generator form. The conclusion does
not mention `R.map 0`; reality compatibility is its only restriction. -/
theorem theoremAZero (R : MultiplierSymbol) :
    UniversalAllModeCancellation R ↔ HasGeneratorForm R := by
  constructor
  · intro hR
    exact (theoremA R).mp (universalCancellation_of_allMode R hR)
  · exact hasGeneratorForm_universalAllModeCancellation R

/-- The symmetric generator witnesses in Theorem A⁰ are unique. -/
theorem theoremAZero_witnesses_unique
    (R : MultiplierSymbol)
    (A B A' B' : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hA' : A'.transpose = A') (hB' : B'.transpose = B')
    (h : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
      R.map k v = generatorMap A B k v)
    (h' : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
      R.map k v = generatorMap A' B' k v) :
    A = A' ∧ B = B' :=
  generator_witnesses_unique R A B A' B' hA hB hA' hB' h h'

/-! ## Explicit arbitrariness of the zero block -/

/-- Reality compatibility at frequency zero says precisely that the zero block
commutes with coordinatewise complex conjugation, i.e. it is a real block. -/
theorem zeroBlock_isReal (R : MultiplierSymbol) (v : CVec) :
    R.map 0 (conjVec v) = conjVec (R.map 0 v) := by
  exact R.realityCompatible 0 v (by
    simp [Transverse, latticeToComplex, Vec3.dot])

/-- The real matrix represented by the zero-frequency complex-linear block. -/
noncomputable def zeroBlockMatrix (R : MultiplierSymbol) : RMatrix :=
  fun i j ↦ (LinearMap.toMatrix' (R.map 0) i j).re

/-- Reality compatibility is not merely a commutation identity at zero: it
forces the complete zero block to be the complexification of a unique real
matrix. -/
theorem zeroBlock_eq_complexification (R : MultiplierSymbol) :
    R.map 0 = (complexifyMatrix (zeroBlockMatrix R)).mulVecLin := by
  apply LinearMap.ext
  intro v
  rw [← LinearMap.toMatrix'_mulVec (R.map 0) v]
  apply congrArg (fun M : CMatrix => Matrix.mulVec M v)
  ext i j
  let e : CVec := Pi.single j 1
  have he : conjVec e = e := by
    funext l
    by_cases hlj : l = j
    · subst l
      simp [e, conjVec]
    · simp [e, conjVec, hlj]
  have hreal := zeroBlock_isReal R e
  rw [he] at hreal
  have hcomponent := congrFun hreal i
  have him : (R.map 0 e i).im = 0 := by
    have hi := congrArg Complex.im hcomponent
    simp [conjVec] at hi
    linarith
  apply Complex.ext
  · simp [complexifyMatrix, zeroBlockMatrix]
  · simp [complexifyMatrix, zeroBlockMatrix, LinearMap.toMatrix'_apply,
      e, him]

/-- Exact all-mode normal form.  Unlike `HasGeneratorForm`, this predicate
also records the otherwise arbitrary real matrix at frequency zero. -/
def HasAllModeGeneratorForm (R : MultiplierSymbol) : Prop :=
  ∃ A B Z : RMatrix,
    A.transpose = A ∧ B.transpose = B ∧
    R.map 0 = (complexifyMatrix Z).mulVecLin ∧
    ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
      R.map k v = generatorMap A B k v

/-- Fully packaged form of Theorem A⁰: the two symmetric nonzero-mode
generators are unique and the zero block is exactly the complexification of
an arbitrary real `3 × 3` matrix. -/
theorem theoremAZero_exact (R : MultiplierSymbol) :
    UniversalAllModeCancellation R ↔ HasAllModeGeneratorForm R := by
  rw [theoremAZero]
  constructor
  · rintro ⟨A, B, hA, hB, hmap⟩
    exact ⟨A, B, zeroBlockMatrix R, hA, hB,
      zeroBlock_eq_complexification R, hmap⟩
  · rintro ⟨A, B, Z, hA, hB, hzero, hmap⟩
    exact ⟨A, B, hA, hB, hmap⟩

/-- Replace the zero-frequency block by an arbitrary real matrix. -/
noncomputable def replaceZeroBlock
    (R : MultiplierSymbol) (Z : RMatrix) : MultiplierSymbol where
  map k := if k = 0 then (complexifyMatrix Z).mulVecLin else R.map k
  realityCompatible := by
    intro k v hv
    by_cases hk : k = 0
    · subst k
      simp [complex_matrix_mulVec_conj]
    · have hnk : -k ≠ 0 := neg_ne_zero_of_ne_zero hk
      simp [hk, hnk, R.realityCompatible k v hv]

/-- Changing the real zero block does not change all-mode cancellation. -/
theorem replaceZeroBlock_universalAllModeCancellation_iff
    (R : MultiplierSymbol) (Z : RMatrix) :
    UniversalAllModeCancellation (replaceZeroBlock R Z) ↔
      UniversalAllModeCancellation R := by
  rw [theoremAZero, theoremAZero]
  constructor
  · rintro ⟨A, B, hA, hB, hmap⟩
    exact ⟨A, B, hA, hB, fun k hk v hv ↦ by
      simpa [replaceZeroBlock, hk] using hmap k hk v hv⟩
  · rintro ⟨A, B, hA, hB, hmap⟩
    exact ⟨A, B, hA, hB, fun k hk v hv ↦ by
      simpa [replaceZeroBlock, hk] using hmap k hk v hv⟩

end FourierMultiplierRigidity
