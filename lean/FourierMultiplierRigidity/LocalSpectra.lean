import FourierMultiplierRigidity.SolenoidalPropagation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Local singular spectra and conditioning

The raw and Leray-projected interaction maps have two orthogonal output
channels in the normalized frames of the manuscript.  This module defines
their `2 × 4` coordinate matrices, computes the Gram matrices, derives the
closed squared-singular-value formulas, proves the Hermitian observation
bound in squared form, and checks both the sharp stable-route polynomial and
the explicit quadratically ill-conditioned family.
-/

namespace FourierMultiplierRigidity.LocalSpectra

noncomputable section

/-! ## Geometric source of the coordinate matrices -/

/-- Algebraic Leray projection onto the plane perpendicular to `p`. -/
def lerayProjection (p y : RVec) : RVec :=
  y - (Vec3.dot p y / Vec3.dot p p) • p

/-- The four unnormalized recipient values from which `rawMatrix` is
obtained by dividing the input and output frame vectors by their norms. -/
theorem rawRecipient_frame_table (q r : RVec) :
    let z := Vec3.cross q r
    let J := crossRotate z
    rawRecipientAlgebra q r z z = 0 ∧
    rawRecipientAlgebra q r z (J r) = -(Vec3.dot z z) • z ∧
    rawRecipientAlgebra q r (J q) z = Vec3.dot z z • z ∧
    rawRecipientAlgebra q r (J q) (J r) =
      Vec3.dot z z • J (r - q) := by
  dsimp only
  constructor
  · simpa using rawRecipient_parametrization q r (1 : ℝ) 1 0 0
  constructor
  · simpa using rawRecipient_parametrization q r (1 : ℝ) 0 0 1
  constructor
  · simpa using rawRecipient_parametrization q r (0 : ℝ) 1 1 0
  · simpa using rawRecipient_parametrization q r (0 : ℝ) 0 1 1

theorem leray_cross_normal (q r : RVec) :
    lerayProjection (-(q + r)) (Vec3.cross q r) = Vec3.cross q r := by
  funext i
  fin_cases i <;>
    simp [lerayProjection, Vec3.dot, Vec3.cross] <;> ring

theorem leray_crossRotate_difference_scaled (q r : RVec) :
    let p := -(q + r)
    let z := Vec3.cross q r
    let J := crossRotate z
    Vec3.dot p p • J (r - q) - Vec3.dot p (J (r - q)) • p =
      (Vec3.dot q q - Vec3.dot r r) • J p := by
  dsimp only
  funext i
  fin_cases i <;>
    simp [crossRotate, Vec3.dot, Vec3.cross] <;> ring

/-- Exact projected tangent identity.  Its coefficient is the
unequal-shell factor; this is the geometric bridge to the last entry of
`projectedMatrix`. -/
theorem leray_crossRotate_difference (q r : RVec)
    (hk : Vec3.dot (-(q + r)) (-(q + r)) ≠ 0) :
    let z := Vec3.cross q r
    let J := crossRotate z
    lerayProjection (-(q + r)) (J (r - q)) =
      ((Vec3.dot q q - Vec3.dot r r) /
        Vec3.dot (-(q + r)) (-(q + r))) • J (-(q + r)) := by
  dsimp only
  have hscaled := leray_crossRotate_difference_scaled q r
  funext i
  have hi := congrFun hscaled i
  simp only [lerayProjection, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hk]
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Vec3.dot] at hi ⊢
  ring_nf at hi ⊢
  exact hi

/-- The universal two-channel matrix.  Its rows are orthogonal, so the two
diagonal entries of `L Lᵀ` are its squared nonzero singular values. -/
def twoChannelMatrix (a b d : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![0, -a, b, 0;
     0,  0, 0, d]

theorem twoChannel_gram (a b d : ℝ) :
    twoChannelMatrix a b d * Matrix.transpose (twoChannelMatrix a b d) =
      !![a ^ 2 + b ^ 2, 0;
         0, d ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoChannelMatrix, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

/-- The normalized raw interaction matrix from Proposition `raw singular
spectrum`. -/
def rawMatrix (Z lambda mu rho : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  twoChannelMatrix (Z / Real.sqrt mu) (Z / Real.sqrt lambda)
    (Z * rho / (Real.sqrt lambda * Real.sqrt mu))

/-- The normalized Leray-projected interaction matrix. -/
def projectedMatrix (Z lambda mu kappa : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  twoChannelMatrix (Z / Real.sqrt mu) (Z / Real.sqrt lambda)
    (Z * (lambda - mu) /
      (Real.sqrt kappa * Real.sqrt lambda * Real.sqrt mu))

def sigmaNormalSq (Zsq lambda mu : ℝ) : ℝ :=
  Zsq * (lambda + mu) / (lambda * mu)

def sigmaRawTangentSq (Zsq lambda mu rhoSq : ℝ) : ℝ :=
  Zsq * rhoSq / (lambda * mu)

def sigmaProjectedTangentSq (Zsq lambda mu kappa : ℝ) : ℝ :=
  Zsq * (lambda - mu) ^ 2 / (kappa * lambda * mu)

theorem normal_channel_formula (Z lambda mu : ℝ)
    (hl : 0 < lambda) (hm : 0 < mu) :
    (Z / Real.sqrt mu) ^ 2 + (Z / Real.sqrt lambda) ^ 2 =
      sigmaNormalSq (Z ^ 2) lambda mu := by
  have hsl := Real.sq_sqrt hl.le
  have hsm := Real.sq_sqrt hm.le
  have hsl0 := Real.sqrt_ne_zero'.mpr hl
  have hsm0 := Real.sqrt_ne_zero'.mpr hm
  unfold sigmaNormalSq
  field_simp
  rw [hsl, hsm]
  ring

theorem raw_tangent_formula (Z lambda mu rho : ℝ)
    (hl : 0 < lambda) (hm : 0 < mu) :
    (Z * rho / (Real.sqrt lambda * Real.sqrt mu)) ^ 2 =
      sigmaRawTangentSq (Z ^ 2) lambda mu (rho ^ 2) := by
  have hsl := Real.sq_sqrt hl.le
  have hsm := Real.sq_sqrt hm.le
  have hsl0 := Real.sqrt_ne_zero'.mpr hl
  have hsm0 := Real.sqrt_ne_zero'.mpr hm
  unfold sigmaRawTangentSq
  field_simp
  rw [hsl, hsm]

theorem projected_tangent_formula (Z lambda mu kappa : ℝ)
    (hl : 0 < lambda) (hm : 0 < mu) (hk : 0 < kappa) :
    (Z * (lambda - mu) /
        (Real.sqrt kappa * Real.sqrt lambda * Real.sqrt mu)) ^ 2 =
      sigmaProjectedTangentSq (Z ^ 2) lambda mu kappa := by
  have hsl := Real.sq_sqrt hl.le
  have hsm := Real.sq_sqrt hm.le
  have hsk := Real.sq_sqrt hk.le
  have hsl0 := Real.sqrt_ne_zero'.mpr hl
  have hsm0 := Real.sqrt_ne_zero'.mpr hm
  have hsk0 := Real.sqrt_ne_zero'.mpr hk
  unfold sigmaProjectedTangentSq
  field_simp
  rw [hsl, hsm, hsk]
  ring

/-- Exact raw Gram matrix, hence the two squared singular values in the
normalized coordinates. -/
theorem rawMatrix_gram (Z lambda mu rho : ℝ)
    (hl : 0 < lambda) (hm : 0 < mu) :
    rawMatrix Z lambda mu rho * Matrix.transpose (rawMatrix Z lambda mu rho) =
      !![sigmaNormalSq (Z ^ 2) lambda mu, 0;
         0, sigmaRawTangentSq (Z ^ 2) lambda mu (rho ^ 2)] := by
  rw [rawMatrix, twoChannel_gram]
  rw [normal_channel_formula Z lambda mu hl hm,
    raw_tangent_formula Z lambda mu rho hl hm]

/-- Exact projected Gram matrix and projected squared spectrum. -/
theorem projectedMatrix_gram (Z lambda mu kappa : ℝ)
    (hl : 0 < lambda) (hm : 0 < mu) (hk : 0 < kappa) :
    projectedMatrix Z lambda mu kappa *
        Matrix.transpose (projectedMatrix Z lambda mu kappa) =
      !![sigmaNormalSq (Z ^ 2) lambda mu, 0;
         0, sigmaProjectedTangentSq (Z ^ 2) lambda mu kappa] := by
  rw [projectedMatrix, twoChannel_gram]
  rw [normal_channel_formula Z lambda mu hl hm,
    projected_tangent_formula Z lambda mu kappa hl hm hk]

/-! ## Complete complex-block observation and multiplicities -/

/-- Vectorized observation of an arbitrary complex `2 × 2` target block.
There are four real copies of the two output coordinates: real/imaginary
parts of each of the two complex rows. -/
def fourfoldObservationMatrix (L : Matrix (Fin 2) (Fin 4) ℝ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 2) ℝ :=
  fun row col ↦ if row.1 = col.1 then L col.2 row.2 else 0

/-- The Gram matrix of the complete observation is four identical copies of
`L Lᵀ`.  This is the precise real-multiplicity-four statement. -/
theorem fourfoldObservation_gram (L : Matrix (Fin 2) (Fin 4) ℝ) :
    Matrix.transpose (fourfoldObservationMatrix L) *
        fourfoldObservationMatrix L =
      fun i j ↦ if i.1 = j.1 then
        (L * Matrix.transpose L) i.2 j.2 else 0 := by
  classical
  ext i j
  rcases i with ⟨ci, ii⟩
  rcases j with ⟨cj, jj⟩
  simp only [fourfoldObservationMatrix, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Fintype.sum_prod_type]
  by_cases hij : ci = cj
  · subst cj
    simp
  · have hji : cj ≠ ci := Ne.symm hij
    simp [hij, hji]

/-- The full projected target observation has the two squared singular
values from Proposition 8.2, each with real multiplicity four. -/
theorem projectedObservation_gram (Z lambda mu kappa : ℝ)
    (hl : 0 < lambda) (hm : 0 < mu) (hk : 0 < kappa) :
    Matrix.transpose
        (fourfoldObservationMatrix (projectedMatrix Z lambda mu kappa)) *
        fourfoldObservationMatrix (projectedMatrix Z lambda mu kappa) =
      fun i j ↦ if i.1 = j.1 then
        if i.2 = j.2 then
          if i.2 = (0 : Fin 2) then sigmaNormalSq (Z ^ 2) lambda mu
          else sigmaProjectedTangentSq (Z ^ 2) lambda mu kappa
        else 0
      else 0 := by
  rw [fourfoldObservation_gram,
    projectedMatrix_gram Z lambda mu kappa hl hm hk]
  ext i j
  rcases i with ⟨ci, ii⟩
  rcases j with ⟨cj, jj⟩
  by_cases hc : ci = cj
  · subst cj
    fin_cases ii <;> fin_cases jj <;> simp
  · simp [hc]

theorem sigmaNormalSq_pos (Zsq lambda mu : ℝ)
    (hZ : 0 < Zsq) (hl : 0 < lambda) (hm : 0 < mu) :
    0 < sigmaNormalSq Zsq lambda mu := by
  unfold sigmaNormalSq
  positivity

theorem sigmaRawTangentSq_pos (Zsq lambda mu rhoSq : ℝ)
    (hZ : 0 < Zsq) (hl : 0 < lambda) (hm : 0 < mu)
    (hrho : 0 < rhoSq) :
    0 < sigmaRawTangentSq Zsq lambda mu rhoSq := by
  unfold sigmaRawTangentSq
  positivity

theorem sigmaProjectedTangentSq_pos (Zsq lambda mu kappa : ℝ)
    (hZ : 0 < Zsq) (hl : 0 < lambda) (hm : 0 < mu)
    (hk : 0 < kappa) (hne : lambda ≠ mu) :
    0 < sigmaProjectedTangentSq Zsq lambda mu kappa := by
  unfold sigmaProjectedTangentSq
  positivity

/-- Squared form of the exact projection-defect factor. -/
theorem projection_defect_factor_sq
    (Zsq lambda mu kappa rhoSq : ℝ)
    (hl : lambda ≠ 0) (hm : mu ≠ 0) (hk : kappa ≠ 0)
    (hrho : rhoSq ≠ 0) :
    sigmaProjectedTangentSq Zsq lambda mu kappa =
      sigmaRawTangentSq Zsq lambda mu rhoSq *
        ((lambda - mu) ^ 2 / (kappa * rhoSq)) := by
  unfold sigmaProjectedTangentSq sigmaRawTangentSq
  field_simp

/-! ## Target observation -/

/-- Squared Hilbert--Schmidt norm of a Hermitian `2 × 2` block with diagonal
entries `a,b` and off-diagonal entry `cRe + i cIm`. -/
def hermitianHSSq (a b cRe cIm : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + 2 * (cRe ^ 2 + cIm ^ 2)

/-- Squared norm of the complete local Hermitian observation. -/
def hermitianObservationSq
    (sn st a b cRe cIm : ℝ) : ℝ :=
  sn * (a ^ 2 + cRe ^ 2 + cIm ^ 2) +
  st * (b ^ 2 + cRe ^ 2 + cIm ^ 2)

/-- The manuscript's observation lower bound, in the equivalent squared form. -/
theorem hermitian_observation_lower_bound
    (sn st a b cRe cIm : ℝ) :
    min sn st * hermitianHSSq a b cRe cIm ≤
      hermitianObservationSq sn st a b cRe cIm := by
  have hn := min_le_left sn st
  have ht := min_le_right sn st
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have hc : 0 ≤ cRe ^ 2 + cIm ^ 2 := by positivity
  unfold hermitianHSSq hermitianObservationSq
  nlinarith

/-! ## Stable route -/

def axisNormalSq (n : ℝ) : ℝ := (n ^ 2 + 2) / 2
def axisTangentSq (n : ℝ) : ℝ :=
  (n ^ 2 - 2) ^ 2 / (2 * (n ^ 2 + 2 * n + 2))

/-- The shifted-axis formulas are the projected spectrum, not a separately
postulated pair.  Substituting the axis-step parameters
`(Z², λ, μ, κ) = (n², n², 2, n² + 2n + 2)` into `sigmaNormalSq` and
`sigmaProjectedTangentSq` returns `axisNormalSq` and `axisTangentSq`, so the
sharp bounds below are bounds on the Gram-verified spectrum. -/
theorem axis_spectrum (n : ℝ) (hn : 1 ≤ n) :
    axisNormalSq n = sigmaNormalSq (n ^ 2) (n ^ 2) 2 ∧
    axisTangentSq n =
      sigmaProjectedTangentSq (n ^ 2) (n ^ 2) 2 (n ^ 2 + 2 * n + 2) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn
  have hsq : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hn0)
  have hkpos : (0 : ℝ) < n ^ 2 + 2 * n + 2 := by nlinarith
  constructor
  · unfold axisNormalSq sigmaNormalSq
    field_simp
  · unfold axisTangentSq sigmaProjectedTangentSq
    field_simp

/-- The factorization used for the sharp squared condition-number bound on
the shifted-axis steps. -/
theorem axis_condition_polynomial (n : ℝ) :
    15 * (n ^ 2 - 2) ^ 2 -
        (n ^ 2 + 2) * (n ^ 2 + 2 * n + 2) =
      (n - 1) * (n - 2) * (14 * n ^ 2 + 40 * n + 28) := by
  ring

theorem axis_condition_bound (n : ℝ) (hn : 1 ≤ n)
    (hgap : n = 1 ∨ 2 ≤ n) :
    axisNormalSq n ≤ 15 * axisTangentSq n := by
  have hden : 0 < 2 * (n ^ 2 + 2 * n + 2) := by nlinarith [sq_nonneg n]
  have hfac : 0 ≤ (n - 1) * (n - 2) := by rcases hgap with rfl | h <;> nlinarith
  have hquad : 0 ≤ 14 * n ^ 2 + 40 * n + 28 := by nlinarith [sq_nonneg n]
  have hpoly := axis_condition_polynomial n
  have hnum :
      0 ≤ 15 * (n ^ 2 - 2) ^ 2 -
        (n ^ 2 + 2) * (n ^ 2 + 2 * n + 2) := by
    rw [hpoly]
    positivity
  have hcalc :
      15 * axisTangentSq n - axisNormalSq n =
        (15 * (n ^ 2 - 2) ^ 2 -
          (n ^ 2 + 2) * (n ^ 2 + 2 * n + 2)) /
            (2 * (n ^ 2 + 2 * n + 2)) := by
    unfold axisNormalSq axisTangentSq
    field_simp
  rw [← sub_nonneg, hcalc]
  exact div_nonneg hnum hden.le

/-- The sharp lower bound `1/10` for the shifted-axis tangential channel at
the two exceptional integer values. -/
theorem axis_tangent_small_cases :
    axisTangentSq 1 = 1 / 10 ∧ axisTangentSq 2 = 1 / 5 := by
  norm_num [axisTangentSq]

theorem axis_tangent_lower_bound (n : ℝ) (hn : 1 ≤ n)
    (hgap : n = 1 ∨ 2 ≤ n) :
    1 / 10 ≤ axisTangentSq n := by
  have hden : 0 < 2 * (n ^ 2 + 2 * n + 2) := by
    nlinarith [sq_nonneg n]
  have hnum : 0 ≤ 5 * (n ^ 2 - 2) ^ 2 - (n ^ 2 + 2 * n + 2) := by
    rcases hgap with rfl | htwo
    · norm_num
    · have hq : 0 ≤ 5 * n ^ 2 + 15 * n + 14 := by
        nlinarith [sq_nonneg n]
      have hf : 0 ≤ (n - 2) * (5 * n ^ 2 + 15 * n + 14) :=
        mul_nonneg (by linarith) hq
      nlinarith
  unfold axisTangentSq
  rw [le_div_iff₀ hden]
  nlinarith

theorem axis_route_sharp_bounds (n : ℝ) (hn : 1 ≤ n)
    (hgap : n = 1 ∨ 2 ≤ n) :
    1 / 10 ≤ min (axisNormalSq n) (axisTangentSq n) ∧
    axisNormalSq n / axisTangentSq n ≤ 15 ∧
    Real.sqrt (axisNormalSq n / axisTangentSq n) ≤ Real.sqrt 15 := by
  have ht := axis_tangent_lower_bound n hn hgap
  have htp : 0 < axisTangentSq n := by linarith
  have hnrm : 1 / 10 ≤ axisNormalSq n := by
    unfold axisNormalSq
    nlinarith [sq_nonneg n]
  have hc := axis_condition_bound n hn hgap
  have hratio : axisNormalSq n / axisTangentSq n ≤ 15 := by
    rw [div_le_iff₀ htp]
    exact hc
  exact ⟨le_min hnrm ht, hratio, Real.sqrt_le_sqrt hratio⟩

/-! ## Remaining route families -/

theorem bootstrap_spectra :
    (sigmaNormalSq 2 1 2 = 3 ∧
      sigmaProjectedTangentSq 2 1 2 3 = 1 / 3) ∧
    (sigmaNormalSq 2 3 1 = 8 / 3 ∧
      sigmaProjectedTangentSq 2 3 1 2 = 4 / 3) := by
  norm_num [sigmaNormalSq, sigmaProjectedTangentSq]

/-- The two bootstrap triads meet the same sharp bounds as the propagating
routes, so no step of the sparse route is left without one. -/
theorem bootstrap_route_bounds :
    (1 / 10 ≤ min (sigmaNormalSq 2 1 2) (sigmaProjectedTangentSq 2 1 2 3) ∧
      sigmaNormalSq 2 1 2 ≤ 15 * sigmaProjectedTangentSq 2 1 2 3) ∧
    (1 / 10 ≤ min (sigmaNormalSq 2 3 1) (sigmaProjectedTangentSq 2 3 1 2) ∧
      sigmaNormalSq 2 3 1 ≤ 15 * sigmaProjectedTangentSq 2 3 1 2) := by
  refine ⟨⟨le_min ?_ ?_, ?_⟩, ⟨le_min ?_ ?_, ?_⟩⟩ <;>
    norm_num [sigmaNormalSq, sigmaProjectedTangentSq]

def completionNormalSq (n : ℝ) : ℝ :=
  n ^ 2 * (n ^ 2 + 2) / (n ^ 2 + 1)

def completionTangentSq (n : ℝ) : ℝ :=
  n ^ 4 / (n ^ 2 + 1)

theorem completion_spectrum (n : ℝ) (hn : n ≠ 0) :
    sigmaNormalSq (n ^ 2) (n ^ 2 + 1) 1 = completionNormalSq n ∧
    sigmaProjectedTangentSq (n ^ 2) (n ^ 2 + 1) 1 (n ^ 2) =
      completionTangentSq n := by
  constructor
  · unfold sigmaNormalSq completionNormalSq
    ring
  · unfold sigmaProjectedTangentSq completionTangentSq
    field_simp
    ring

theorem completion_tangent_lower_bound (n : ℝ) (hn : 2 ≤ n) :
    16 / 5 ≤ completionTangentSq n := by
  have hden : 0 < n ^ 2 + 1 := by positivity
  unfold completionTangentSq
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg (n ^ 2 - 4)]

theorem completion_squared_condition_bound (n : ℝ) (hn : 2 ≤ n) :
    (n ^ 2 + 2) / n ^ 2 ≤ 3 / 2 := by
  have hn2 : 0 < n ^ 2 := by positivity
  rw [div_le_iff₀ hn2]
  nlinarith [sq_nonneg n]

theorem completion_condition_formula (n : ℝ) (hn : n ≠ 0) :
    completionNormalSq n / completionTangentSq n =
      (n ^ 2 + 2) / n ^ 2 := by
  unfold completionNormalSq completionTangentSq
  field_simp

def generalNormalSq (m d : ℝ) : ℝ := d * (m + 1) / m

def generalTangentSq (m a d : ℝ) : ℝ :=
  d * (m - 1) ^ 2 / (m * (m + 1 + 2 * a))

theorem general_spectrum (m a d : ℝ) (hm : m ≠ 0)
    (hp : m + 1 + 2 * a ≠ 0) :
    sigmaNormalSq d m 1 = generalNormalSq m d ∧
    sigmaProjectedTangentSq d m 1 (m + 1 + 2 * a) =
      generalTangentSq m a d := by
  constructor
  · unfold sigmaNormalSq generalNormalSq
    ring
  · unfold sigmaProjectedTangentSq generalTangentSq
    field_simp

theorem general_small_spectra :
    (generalNormalSq 2 2 = 3 ∧ generalTangentSq 2 0 2 = 1 / 3) ∧
    (generalNormalSq 2 1 = 3 / 2 ∧ generalTangentSq 2 1 1 = 1 / 10) := by
  norm_num [generalNormalSq, generalTangentSq]

theorem general_route_bounds (m a d : ℝ)
    (hm : 3 ≤ m) (ha : 0 ≤ a) (hasq : a ^ 2 ≤ m) (hd : 1 ≤ d) :
    1 < generalNormalSq m d ∧
    1 / 10 ≤ generalTangentSq m a d ∧
    generalNormalSq m d ≤ 15 * generalTangentSq m a d := by
  have hm0 : 0 < m := by linarith
  have ham : a ≤ m - 1 := by
    by_contra h
    have hgt : m - 1 < a := lt_of_not_ge h
    have hpoly : m < (m - 1) ^ 2 := by
      nlinarith [sq_nonneg (m - 3)]
    nlinarith [sq_nonneg a]
  have hparent : 0 < m + 1 + 2 * a := by linarith
  have hden : 0 < m * (m + 1 + 2 * a) := mul_pos hm0 hparent
  have hma : 2 * m * a ≤ 2 * m * (m - 1) := by
    exact mul_le_mul_of_nonneg_left ham (by positivity)
  have hdenUpper : m * (m + 1 + 2 * a) ≤ m * (3 * m - 1) := by
    nlinarith
  have hnormal : 1 < generalNormalSq m d := by
    unfold generalNormalSq
    rw [lt_div_iff₀ hm0]
    nlinarith
  have htangent : 1 / 10 ≤ generalTangentSq m a d := by
    have hpoly : m * (3 * m - 1) ≤ 10 * (m - 1) ^ 2 := by
      nlinarith [sq_nonneg (m - 3)]
    have hunit : m * (m + 1 + 2 * a) ≤ 10 * (m - 1) ^ 2 :=
      hdenUpper.trans hpoly
    have hscale : 10 * (m - 1) ^ 2 ≤ 10 * d * (m - 1) ^ 2 := by
      nlinarith [sq_nonneg (m - 1)]
    unfold generalTangentSq
    rw [le_div_iff₀ hden]
    nlinarith
  have hcondition : generalNormalSq m d ≤ 15 * generalTangentSq m a d := by
    have hparentUpper :
        (m + 1) * (m + 1 + 2 * a) ≤ (m + 1) * (3 * m - 1) := by
      apply mul_le_mul_of_nonneg_left
      · nlinarith
      · linarith
    have hpoly : (m + 1) * (3 * m - 1) ≤ 15 * (m - 1) ^ 2 := by
      nlinarith [sq_nonneg (m - 3)]
    have hbracket :
        0 ≤ 15 * (m - 1) ^ 2 - (m + 1) * (m + 1 + 2 * a) := by
      linarith
    have hnum :
        0 ≤ d * (15 * (m - 1) ^ 2 -
          (m + 1) * (m + 1 + 2 * a)) :=
      mul_nonneg (by linarith) hbracket
    have hcalc :
        15 * generalTangentSq m a d - generalNormalSq m d =
          d * (15 * (m - 1) ^ 2 -
            (m + 1) * (m + 1 + 2 * a)) /
              (m * (m + 1 + 2 * a)) := by
      unfold generalNormalSq generalTangentSq
      field_simp
    rw [← sub_nonneg, hcalc]
    exact div_nonneg hnum hden.le
  exact ⟨hnormal, htangent, hcondition⟩

/-- The `m = 2` general step.  Integrality forces `a ∈ {0, 1}`; both choices
meet the same sharp bounds, with equality in the condition-number bound at
`a = 1`. -/
theorem general_route_bounds_two (a d : ℝ) (ha : a = 0 ∨ a = 1) (hd : 1 ≤ d) :
    1 < generalNormalSq 2 d ∧
    1 / 10 ≤ generalTangentSq 2 a d ∧
    generalNormalSq 2 d ≤ 15 * generalTangentSq 2 a d := by
  have hnorm : generalNormalSq 2 d = 3 * d / 2 := by
    unfold generalNormalSq
    ring
  rcases ha with rfl | rfl
  · have htan : generalTangentSq 2 0 d = d / 6 := by
      unfold generalTangentSq
      norm_num
    rw [hnorm, htan]
    exact ⟨by linarith, by linarith, by linarith⟩
  · have htan : generalTangentSq 2 1 d = d / 10 := by
      unfold generalTangentSq
      norm_num
    rw [hnorm, htan]
    exact ⟨by linarith, by linarith, by linarith⟩

theorem general_route_sharp_condition_two (a d : ℝ) (ha : a = 0 ∨ a = 1)
    (hd : 1 ≤ d) :
    generalNormalSq 2 d / generalTangentSq 2 a d ≤ 15 ∧
    Real.sqrt (generalNormalSq 2 d / generalTangentSq 2 a d) ≤
      Real.sqrt 15 := by
  obtain ⟨_, ht, hc⟩ := general_route_bounds_two a d ha hd
  have htp : 0 < generalTangentSq 2 a d := by linarith
  have hratio : generalNormalSq 2 d / generalTangentSq 2 a d ≤ 15 := by
    rw [div_le_iff₀ htp]
    exact hc
  exact ⟨hratio, Real.sqrt_le_sqrt hratio⟩

theorem general_route_sharp_condition (m a d : ℝ)
    (hm : 3 ≤ m) (ha : 0 ≤ a) (hasq : a ^ 2 ≤ m) (hd : 1 ≤ d) :
    generalNormalSq m d / generalTangentSq m a d ≤ 15 ∧
    Real.sqrt (generalNormalSq m d / generalTangentSq m a d) ≤
      Real.sqrt 15 := by
  obtain ⟨_, ht, hc⟩ := general_route_bounds m a d hm ha hasq hd
  have htp : 0 < generalTangentSq m a d := by linarith
  have hratio : generalNormalSq m d / generalTangentSq m a d ≤ 15 := by
    rw [div_le_iff₀ htp]
    exact hc
  exact ⟨hratio, Real.sqrt_le_sqrt hratio⟩

/-! ## An unstable unequal-shell family -/

/-- Exact normal and tangent squared singular values for the manuscript's
family `qₙ=(n,0,0)`, `rₙ=(0,n,1)`. -/
theorem badFamily_spectrum (n : ℝ) (hn : 0 < n) :
    sigmaNormalSq (n ^ 2 * (n ^ 2 + 1)) (n ^ 2) (n ^ 2 + 1) =
        2 * n ^ 2 + 1 ∧
    sigmaProjectedTangentSq (n ^ 2 * (n ^ 2 + 1))
        (n ^ 2) (n ^ 2 + 1) (2 * n ^ 2 + 1) =
        (2 * n ^ 2 + 1)⁻¹ := by
  have hn2 : n ^ 2 ≠ 0 := by positivity
  have hp : 2 * n ^ 2 + 1 ≠ 0 := by positivity
  constructor
  · unfold sigmaNormalSq
    field_simp
    ring
  · unfold sigmaProjectedTangentSq
    field_simp
    ring

/-- Consequently the squared condition number is `(2n²+1)²`, and the
condition number itself is `2n²+1`; unequal shell lengths alone are not
uniformly conditioning. -/
theorem badFamily_squared_condition (n : ℝ) (hn : 0 < n) :
    (2 * n ^ 2 + 1) / (2 * n ^ 2 + 1)⁻¹ =
      (2 * n ^ 2 + 1) ^ 2 := by
  have hp : 2 * n ^ 2 + 1 ≠ 0 := by positivity
  field_simp

theorem badFamily_condition (n : ℝ) (hn : 0 < n) :
    Real.sqrt ((2 * n ^ 2 + 1) / (2 * n ^ 2 + 1)⁻¹) =
      2 * n ^ 2 + 1 := by
  rw [badFamily_squared_condition n hn, Real.sqrt_sq_eq_abs]
  exact abs_of_pos (by positivity)

/-! ## Passage from local spectral input to a finite global certificate -/

/-- The abstract last step in the finite-certificate stability statement.
Here `xPerp` is the orthogonal-to-kernel component of `x`; the hypotheses
record that the certificate ignores the kernel component and that `gamma` is
its least positive singular value on the complement. -/
theorem global_stability_from_least_singular_value
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (A : E → F) (gamma : ℝ) (x xPerp : E)
    (hgamma : 0 < gamma) (hSame : A xPerp = A x)
    (hLower : gamma * ‖xPerp‖ ≤ ‖(A xPerp)‖) :
    ‖xPerp‖ ≤ gamma⁻¹ * ‖(A x)‖ := by
  calc
    ‖xPerp‖ = gamma⁻¹ * (gamma * ‖xPerp‖) := by
      field_simp
    _ ≤ gamma⁻¹ * ‖(A xPerp)‖ :=
      mul_le_mul_of_nonneg_left hLower (inv_nonneg.mpr hgamma.le)
    _ = gamma⁻¹ * ‖(A x)‖ := by rw [hSame]

/-! The preceding lemma is the scalar algebra used in the last line.  The
next result supplies its geometric data canonically from the orthogonal
projection onto the kernel. -/

section GlobalKernelDistance

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The component of `x` orthogonal to the kernel of an observation map. -/
def kernelPerpComponent (A : E →L[ℝ] F) (x : E) : E :=
  x - A.ker.starProjection x

theorem kernelPerpComponent_mem_orthogonal (A : E →L[ℝ] F) (x : E) :
    kernelPerpComponent A x ∈ A.kerᗮ := by
  exact Submodule.sub_starProjection_mem_orthogonal (K := A.ker) x

/-- Removing the kernel projection does not change any observation. -/
theorem map_kernelPerpComponent (A : E →L[ℝ] F) (x : E) :
    A (kernelPerpComponent A x) = A x := by
  rw [kernelPerpComponent, map_sub]
  have hp : A.ker.starProjection x ∈ A.ker :=
    Submodule.starProjection_apply_mem _ _
  have hp0 : A (A.ker.starProjection x) = 0 := A.mem_ker.mp hp
  rw [hp0, sub_zero]

/-- Genuine finite-dimensional stability modulo the exact kernel.  The
left-hand side is the norm of `x` after orthogonal projection away from the
kernel (equivalently, its Hilbert-space distance to that kernel). -/
theorem global_stability_mod_kernel
    (A : E →L[ℝ] F) (gamma : ℝ) (hgamma : 0 < gamma)
    (hLower : ∀ y ∈ A.kerᗮ, gamma * ‖y‖ ≤ ‖A y‖) (x : E) :
    ‖kernelPerpComponent A x‖ ≤ gamma⁻¹ * ‖A x‖ := by
  apply global_stability_from_least_singular_value A gamma x
    (kernelPerpComponent A x) hgamma
  · exact map_kernelPerpComponent A x
  · exact hLower _ (kernelPerpComponent_mem_orthogonal A x)

/-- The least singular value is not an assumption.  In finite dimensions every
continuous linear map is bounded below on the orthogonal complement of its
kernel, with a constant depending only on the map.  This is exactly the
`gamma` of the stability estimate, so the estimate needs no spectral
hypothesis. -/
theorem exists_least_singular_value [FiniteDimensional ℝ E] (A : E →L[ℝ] F) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ y ∈ A.kerᗮ, gamma * ‖y‖ ≤ ‖A y‖ := by
  have hinj : (A.toLinearMap.comp A.kerᗮ.subtype).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have hker : (y : E) ∈ A.ker := hy
    have hperp : (y : E) ∈ A.kerᗮ := y.2
    exact Subtype.ext (inner_self_eq_zero.mp (hperp _ hker))
  obtain ⟨C, hC, hanti⟩ :=
    LinearMap.exists_antilipschitzWith (A.toLinearMap.comp A.kerᗮ.subtype) hinj
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hCinv : (0 : ℝ) < (C : ℝ)⁻¹ := inv_pos.mpr hCpos
  refine ⟨(C : ℝ)⁻¹, hCinv, fun y hy => ?_⟩
  have hd := hanti.le_mul_dist (⟨y, hy⟩ : A.kerᗮ) 0
  simp only [dist_zero_right, map_zero] at hd
  have hnorm : ‖y‖ ≤ (C : ℝ) * ‖A y‖ := by simpa using hd
  calc (C : ℝ)⁻¹ * ‖y‖ ≤ (C : ℝ)⁻¹ * ((C : ℝ) * ‖A y‖) :=
        mul_le_mul_of_nonneg_left hnorm hCinv.le
    _ = ‖A y‖ := by
        field_simp

/-- **Finite-certificate stability, with no spectral hypothesis.**  Every
observation map on a finite-dimensional parameter space has a positive
stability constant: approximate vanishing of the observations forces the
parameter to be correspondingly close to the kernel.  No claim is made that
the constant is uniform over a family of certificates. -/
theorem exists_stability_constant [FiniteDimensional ℝ E] (A : E →L[ℝ] F) :
    ∃ gamma : ℝ, 0 < gamma ∧
      ∀ x : E, ‖kernelPerpComponent A x‖ ≤ gamma⁻¹ * ‖A x‖ := by
  obtain ⟨gamma, hgamma, hLower⟩ := exists_least_singular_value A
  exact ⟨gamma, hgamma, fun x => global_stability_mod_kernel A gamma hgamma hLower x⟩

end GlobalKernelDistance

end
end FourierMultiplierRigidity.LocalSpectra
