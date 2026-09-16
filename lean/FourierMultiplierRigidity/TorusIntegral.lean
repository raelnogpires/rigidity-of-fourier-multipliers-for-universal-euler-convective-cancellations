import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import FourierMultiplierRigidity

/-!
# Normalized integration over the three-torus

This module provides the analytic ingredients needed to state the
strain–vorticity functional as an actual integral of an actual function on
`𝕋³ = (ℝ/2πℤ)³`, rather than as a resonant sum of Fourier coefficients.

* `char k x` is the character `e^{i k·x}` of a lattice wavevector;
* `torusMean f` is `(2π)⁻³ ∫_{𝕋³} f`, written as an iterated interval integral;
* `torusMean_char` is the orthogonality relation, obtained from the genuine
  one-dimensional integral `∫₀^{2π} e^{int} dt` rather than assumed;
* `torusMean_sum` and `torusMean_tripleSum` integrate a finite trigonometric
  polynomial term by term.

Nothing here is specific to the strain–vorticity problem; the physical-space
bridge itself is in `PhysicalSpaceIntegral.lean`.
-/

namespace FourierMultiplierRigidity.Torus

noncomputable section

/-- A point of the torus assembled from its three coordinates. -/
def pt (x₀ x₁ x₂ : ℝ) : Fin 3 → ℝ := ![x₀, x₁, x₂]

@[simp] theorem pt_zero (x₀ x₁ x₂ : ℝ) : pt x₀ x₁ x₂ 0 = x₀ := rfl
@[simp] theorem pt_one (x₀ x₁ x₂ : ℝ) : pt x₀ x₁ x₂ 1 = x₁ := rfl
@[simp] theorem pt_two (x₀ x₁ x₂ : ℝ) : pt x₀ x₁ x₂ 2 = x₂ := rfl

/-- The one-dimensional Fourier factor `e^{i n t}`. -/
def expTerm (n : ℤ) (t : ℝ) : ℂ := Complex.exp (Complex.I * (n : ℂ) * (t : ℂ))

/-- The Fourier character `e^{i k·x}` of a lattice wavevector. -/
def char (k : LatticeVec) (x : Fin 3 → ℝ) : ℂ :=
  expTerm (k 0) (x 0) * expTerm (k 1) (x 1) * expTerm (k 2) (x 2)

/-- `char` really is the exponential of `i` times the phase `k·x`. -/
theorem char_eq_exp (k : LatticeVec) (x : Fin 3 → ℝ) :
    char k x =
      Complex.exp (Complex.I *
        ((k 0 * x 0 + k 1 * x 1 + k 2 * x 2 : ℝ) : ℂ)) := by
  unfold char expTerm
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expTerm_add (m n : ℤ) (t : ℝ) :
    expTerm (m + n) t = expTerm m t * expTerm n t := by
  unfold expTerm
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem expTerm_zero (t : ℝ) : expTerm 0 t = 1 := by
  simp [expTerm]

/-- Characters turn lattice addition into multiplication. -/
theorem char_add (k l : LatticeVec) (x : Fin 3 → ℝ) :
    char (k + l) x = char k x * char l x := by
  unfold char
  simp only [Pi.add_apply, expTerm_add]
  ring

@[simp] theorem char_zero (x : Fin 3 → ℝ) : char 0 x = 1 := by
  simp [char]

@[fun_prop]
theorem continuous_expTerm (n : ℤ) : Continuous (expTerm n) := by
  unfold expTerm
  fun_prop

theorem expTerm_add_arg (n : ℤ) (a b : ℝ) :
    expTerm n (a + b) = expTerm n a * expTerm n b := by
  unfold expTerm
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem expTerm_arg_zero (n : ℤ) : expTerm n 0 = 1 := by
  simp [expTerm]

theorem expTerm_neg_cancel (n : ℤ) (a : ℝ) : expTerm n a * expTerm n (-a) = 1 := by
  rw [← expTerm_add_arg]
  simp

/-- Differentiating a one-dimensional character. -/
theorem hasDerivAt_expTerm (n : ℤ) (t : ℝ) :
    HasDerivAt (expTerm n) (Complex.I * (n : ℂ) * expTerm n t) t := by
  unfold expTerm
  refine (?_ : HasDerivAt (fun y : ℂ => Complex.exp (Complex.I * (n : ℂ) * y))
      (Complex.I * (n : ℂ) * Complex.exp (Complex.I * (n : ℂ) * ((t : ℝ) : ℂ)))
      ((t : ℝ) : ℂ)).comp_ofReal
  rw [(fun α β => by ring : ∀ α β : ℂ, α * Complex.exp β = Complex.exp β * α)]
  refine (Complex.hasDerivAt_exp _).comp ((t : ℝ) : ℂ) ?_
  simpa using (hasDerivAt_id ((t : ℝ) : ℂ)).const_mul (Complex.I * (n : ℂ))

/-- Freezing all but one coordinate turns a character into a one-dimensional
character in the remaining variable. -/
theorem char_update (k : LatticeVec) (x : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    char k (Function.update x i t) =
      (char k x * expTerm (k i) (-(x i))) * expTerm (k i) t := by
  have key : ∀ l : Fin 3, expTerm (k l) (Function.update x i t l) =
      expTerm (k l) (x l) *
        (if l = i then expTerm (k i) (-(x i)) * expTerm (k i) t else 1) := by
    intro l
    by_cases hl : l = i
    · subst hl
      rw [Function.update_self, if_pos rfl, ← mul_assoc, expTerm_neg_cancel,
        one_mul]
    · rw [Function.update_of_ne hl, if_neg hl, mul_one]
  unfold char
  rw [key 0, key 1, key 2]
  fin_cases i <;> simp <;> ring

/-- The exact value of the one-dimensional character integral. -/
def charInt (n : ℤ) : ℂ := if n = 0 then 2 * (Real.pi : ℂ) else 0

/-- Orthogonality in one variable: a nonconstant character integrates to zero
over a full period.  This is a genuine integral computation. -/
theorem integral_expTerm (n : ℤ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), expTerm n t) = charInt n := by
  by_cases hn : n = 0
  · subst hn
    simp [charInt]
  · have hc : Complex.I * (n : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, hn]
    have hint : (∫ t in (0 : ℝ)..(2 * Real.pi), expTerm n t) =
        (Complex.exp (Complex.I * (n : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (n : ℂ) * ((0 : ℝ) : ℂ))) /
        (Complex.I * (n : ℂ)) := by
      simpa [expTerm, mul_assoc] using
        integral_exp_mul_complex (a := (0 : ℝ)) (b := 2 * Real.pi) hc
    have htop : Complex.exp (Complex.I * (n : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have h := Complex.exp_int_mul_two_pi_mul_I n
      rw [← h]
      congr 1
      push_cast
      ring
    rw [hint, htop, charInt, if_neg hn]
    simp

theorem integral_const_mul_expTerm (a : ℂ) (n : ℤ) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), a * expTerm n t) = a * charInt n := by
  rw [intervalIntegral.integral_const_mul, integral_expTerm]

/-- The normalized mean of a function over the three-torus, written as an
iterated integral over one full period in each coordinate. -/
def torusMean (f : (Fin 3 → ℝ) → ℂ) : ℂ :=
  ((((2 * Real.pi) ^ 3 : ℝ) : ℂ))⁻¹ *
    ∫ x₀ in (0 : ℝ)..(2 * Real.pi), ∫ x₁ in (0 : ℝ)..(2 * Real.pi),
      ∫ x₂ in (0 : ℝ)..(2 * Real.pi), f (pt x₀ x₁ x₂)

theorem torusMean_congr {f g : (Fin 3 → ℝ) → ℂ} (h : ∀ x, f x = g x) :
    torusMean f = torusMean g := by
  simp only [funext h]

private theorem two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero two_ne_zero hpi

/-- Term-by-term integration of a finite trigonometric polynomial: only the
resonant terms survive. -/
theorem torusMean_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (m : ι → LatticeVec) :
    torusMean (fun x => ∑ i ∈ s, c i * char (m i) x) =
      ∑ i ∈ s, (if m i = 0 then c i else 0) := by
  classical
  have hinner : ∀ x₀ x₁ : ℝ,
      (∫ x₂ in (0 : ℝ)..(2 * Real.pi),
          ∑ i ∈ s, c i * char (m i) (pt x₀ x₁ x₂)) =
        ∑ i ∈ s, (c i * expTerm (m i 0) x₀ * expTerm (m i 1) x₁) *
          charInt (m i 2) := by
    intro x₀ x₁
    have hfun : (fun x₂ : ℝ => ∑ i ∈ s, c i * char (m i) (pt x₀ x₁ x₂)) =
        fun x₂ : ℝ => ∑ i ∈ s,
          (c i * expTerm (m i 0) x₀ * expTerm (m i 1) x₁) * expTerm (m i 2) x₂ := by
      funext x₂
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [char, pt_zero, pt_one, pt_two]
      ring
    have hsum := intervalIntegral.integral_finsetSum
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 2 * Real.pi) (s := s)
      (f := fun i (x₂ : ℝ) =>
        (c i * expTerm (m i 0) x₀ * expTerm (m i 1) x₁) * expTerm (m i 2) x₂)
      (fun i _ => (Continuous.intervalIntegrable (by fun_prop) _ _))
    rw [hfun, hsum]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul_expTerm _ _
  have hmid : ∀ x₀ : ℝ,
      (∫ x₁ in (0 : ℝ)..(2 * Real.pi),
          ∑ i ∈ s, (c i * expTerm (m i 0) x₀ * expTerm (m i 1) x₁) *
            charInt (m i 2)) =
        ∑ i ∈ s, (c i * expTerm (m i 0) x₀) * charInt (m i 1) * charInt (m i 2) := by
    intro x₀
    have hfun : (fun x₁ : ℝ => ∑ i ∈ s,
          (c i * expTerm (m i 0) x₀ * expTerm (m i 1) x₁) * charInt (m i 2)) =
        fun x₁ : ℝ => ∑ i ∈ s,
          ((c i * expTerm (m i 0) x₀) * charInt (m i 2)) * expTerm (m i 1) x₁ := by
      funext x₁
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hsum := intervalIntegral.integral_finsetSum
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 2 * Real.pi) (s := s)
      (f := fun i (x₁ : ℝ) =>
        ((c i * expTerm (m i 0) x₀) * charInt (m i 2)) * expTerm (m i 1) x₁)
      (fun i _ => (Continuous.intervalIntegrable (by fun_prop) _ _))
    rw [hfun, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul_expTerm]
    ring
  have houter :
      (∫ x₀ in (0 : ℝ)..(2 * Real.pi),
          ∑ i ∈ s, (c i * expTerm (m i 0) x₀) * charInt (m i 1) * charInt (m i 2)) =
        ∑ i ∈ s, c i * charInt (m i 0) * charInt (m i 1) * charInt (m i 2) := by
    have hfun : (fun x₀ : ℝ => ∑ i ∈ s,
          (c i * expTerm (m i 0) x₀) * charInt (m i 1) * charInt (m i 2)) =
        fun x₀ : ℝ => ∑ i ∈ s,
          (c i * charInt (m i 1) * charInt (m i 2)) * expTerm (m i 0) x₀ := by
      funext x₀
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hsum := intervalIntegral.integral_finsetSum
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 2 * Real.pi) (s := s)
      (f := fun i (x₀ : ℝ) =>
        (c i * charInt (m i 1) * charInt (m i 2)) * expTerm (m i 0) x₀)
      (fun i _ => (Continuous.intervalIntegrable (by fun_prop) _ _))
    rw [hfun, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul_expTerm]
    ring
  unfold torusMean
  simp only [hinner, hmid, houter]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : m i = 0
  · have h0 : m i 0 = 0 := by rw [hm]; rfl
    have h1 : m i 1 = 0 := by rw [hm]; rfl
    have h2 : m i 2 = 0 := by rw [hm]; rfl
    rw [if_pos hm, charInt, charInt, charInt, if_pos h0, if_pos h1, if_pos h2]
    have hcast : ((((2 * Real.pi) ^ 3 : ℝ) : ℂ)) = (2 * (Real.pi : ℂ)) ^ 3 := by
      push_cast
      ring
    rw [hcast]
    field_simp
  · have hsome : m i 0 ≠ 0 ∨ m i 1 ≠ 0 ∨ m i 2 ≠ 0 := by
      by_contra hcon
      have h0 : m i 0 = 0 := by by_contra h; exact hcon (Or.inl h)
      have h1 : m i 1 = 0 := by by_contra h; exact hcon (Or.inr (Or.inl h))
      have h2 : m i 2 = 0 := by by_contra h; exact hcon (Or.inr (Or.inr h))
      refine hm (funext fun j => ?_)
      fin_cases j <;> simp [h0, h1, h2]
    rw [if_neg hm]
    rcases hsome with h | h | h <;>
      simp [charInt, h]

/-- Orthogonality of the characters of the three-torus. -/
theorem torusMean_char (k : LatticeVec) :
    torusMean (char k) = if k = 0 then 1 else 0 := by
  classical
  have h := torusMean_sum (ι := Unit) {()} (fun _ => (1 : ℂ)) (fun _ => k)
  simpa using h

/-- Term-by-term integration of the resonant triple sums used by the
strain–vorticity functional. -/
theorem torusMean_tripleSum (s : Finset LatticeVec)
    (F : LatticeVec → LatticeVec → LatticeVec → ℂ) :
    torusMean (fun x => ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, F p q r * char (p + q + r) x) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, (if p + q + r = 0 then F p q r else 0) := by
  classical
  have hprod : ∀ (G : LatticeVec → LatticeVec → LatticeVec → ℂ),
      ∑ t ∈ s ×ˢ s ×ˢ s, G t.1 t.2.1 t.2.2 =
        ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, G p q r := by
    intro G
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.sum_product]
  have hfun : ∀ x : Fin 3 → ℝ,
      (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, F p q r * char (p + q + r) x) =
        ∑ t ∈ s ×ˢ s ×ˢ s,
          (fun t : LatticeVec × LatticeVec × LatticeVec => F t.1 t.2.1 t.2.2) t *
            char ((fun t : LatticeVec × LatticeVec × LatticeVec =>
              t.1 + t.2.1 + t.2.2) t) x := by
    intro x
    exact (hprod (fun p q r => F p q r * char (p + q + r) x)).symm
  rw [torusMean_congr hfun,
    torusMean_sum (s ×ˢ s ×ˢ s)
      (fun t : LatticeVec × LatticeVec × LatticeVec => F t.1 t.2.1 t.2.2)
      (fun t : LatticeVec × LatticeVec × LatticeVec => t.1 + t.2.1 + t.2.2)]
  exact hprod (fun p q r => if p + q + r = 0 then F p q r else 0)

end

end FourierMultiplierRigidity.Torus
