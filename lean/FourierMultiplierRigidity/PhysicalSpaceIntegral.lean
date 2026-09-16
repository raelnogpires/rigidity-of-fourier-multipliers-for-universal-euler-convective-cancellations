import FourierMultiplierRigidity.PhysicalSpaceCorollaryC
import FourierMultiplierRigidity.TorusIntegral

/-!
# The strain–vorticity functional as a genuine physical-space integral

`PhysicalSpaceCorollaryC.lean` builds the zero Fourier mode of
`sym ∇(Tu) : (ω ⊗ ω)` as a resonant sum of Fourier coefficients.  This module
removes the remaining interpretive step: it evaluates the finite Fourier
fields as honest functions on the torus, differentiates them with `deriv`,
contracts the resulting tensors pointwise, and integrates the resulting scalar
field over `𝕋³`.

* `velocity u` and `mappedVelocity T u` are functions `ℝ³ → ℂ³`;
* `physicalCurl` is built from real partial derivatives, and
  `physicalCurl_velocity` identifies it with the Fourier curl;
* `strainVorticityDensity T u x` is the pointwise contraction
  `sym ∇(Tu) : (ω ⊗ ω)` at `x`, with no Fourier bookkeeping in its statement;
* `torusMean_strainVorticityDensity` proves that its normalized integral over
  the torus is the functional `physicalSVCubicForm` used by Corollary C;
* `corollaryC_torusIntegral` is therefore Corollary C with a physical-space
  integral as its hypothesis;
* `torusMean_strainVorticity_eq_neg_transport` is the integration-by-parts
  identity `∫ sym ∇(Tu) : (ω ⊗ ω) = -∫ Tu · (ω · ∇)ω`, between two integrals
  of genuinely differentiated physical fields.
-/

namespace FourierMultiplierRigidity.StrainVorticity

open FourierMultiplierRigidity.Torus

noncomputable section

/-! ## Physical fields and their partial derivatives -/

/-- The `i`-th partial derivative of a scalar field on the torus. -/
def partialDeriv (i : Fin 3) (f : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  deriv (fun t : ℝ => f (Function.update x i t)) (x i)

/-- The physical field of a finite family of Fourier coefficients. -/
def fourierValue (s : Finset LatticeVec) (a : LatticeVec → CVec)
    (x : Fin 3 → ℝ) : CVec :=
  fun j => ∑ k ∈ s, char k x * a k j

/-- Differentiating a finite Fourier series coordinatewise, term by term. -/
theorem hasDerivAt_fourierValue (s : Finset LatticeVec) (a : LatticeVec → CVec)
    (x : Fin 3 → ℝ) (i j : Fin 3) :
    HasDerivAt (fun t : ℝ => fourierValue s a (Function.update x i t) j)
      (∑ k ∈ s, (Complex.I * (k i : ℂ)) * (char k x * a k j)) (x i) := by
  have hterm : ∀ k ∈ s,
      HasDerivAt (fun t : ℝ => char k (Function.update x i t) * a k j)
        ((Complex.I * (k i : ℂ)) * (char k x * a k j)) (x i) := by
    intro k _
    have hbase := (hasDerivAt_expTerm (k i) (x i)).const_mul
      (char k x * expTerm (k i) (-(x i)) * a k j)
    have hfun : (fun t : ℝ => char k (Function.update x i t) * a k j) =
        fun t : ℝ =>
          (char k x * expTerm (k i) (-(x i)) * a k j) * expTerm (k i) t := by
      funext t
      rw [char_update]
      ring
    have hcancel : expTerm (k i) (-(x i)) * expTerm (k i) (x i) = 1 := by
      rw [mul_comm]
      exact expTerm_neg_cancel _ _
    have hval : (char k x * expTerm (k i) (-(x i)) * a k j) *
        (Complex.I * (k i : ℂ) * expTerm (k i) (x i)) =
          (Complex.I * (k i : ℂ)) * (char k x * a k j) := by
      linear_combination (char k x * a k j * (Complex.I * (k i : ℂ))) * hcancel
    rw [hfun, ← hval]
    exact hbase
  have hfunext : (∑ k ∈ s, fun t : ℝ => char k (Function.update x i t) * a k j) =
      fun t : ℝ => ∑ k ∈ s, char k (Function.update x i t) * a k j := by
    funext t
    simp [Finset.sum_apply]
  show HasDerivAt
    (fun t : ℝ => ∑ k ∈ s, char k (Function.update x i t) * a k j)
    (∑ k ∈ s, (Complex.I * (k i : ℂ)) * (char k x * a k j)) (x i)
  rw [← hfunext]
  exact HasDerivAt.sum hterm

/-- The coordinatewise partial derivatives of a finite Fourier series. -/
theorem partialDeriv_fourierValue (s : Finset LatticeVec) (a : LatticeVec → CVec)
    (x : Fin 3 → ℝ) (i j : Fin 3) :
    partialDeriv i (fun y => fourierValue s a y j) x =
      ∑ k ∈ s, (Complex.I * (k i : ℂ)) * (char k x * a k j) :=
  (hasDerivAt_fourierValue s a x i j).deriv

/-! ## Vorticity by real differentiation -/

/-- The curl of a physical vector field, from its real partial derivatives. -/
def physicalCurl (v : (Fin 3 → ℝ) → CVec) (x : Fin 3 → ℝ) : CVec :=
  ![partialDeriv 1 (fun y => v y 2) x - partialDeriv 2 (fun y => v y 1) x,
    partialDeriv 2 (fun y => v y 0) x - partialDeriv 0 (fun y => v y 2) x,
    partialDeriv 0 (fun y => v y 1) x - partialDeriv 1 (fun y => v y 0) x]

/-- The physical curl of a finite Fourier series is the Fourier curl. -/
theorem physicalCurl_fourierValue (s : Finset LatticeVec) (a : LatticeVec → CVec)
    (x : Fin 3 → ℝ) :
    physicalCurl (fourierValue s a) x =
      fourierValue s (fun k => curlSymbol k (a k)) x := by
  have comp : ∀ (i₁ i₂ : Fin 3) (w : LatticeVec → ℂ),
      (∀ k : LatticeVec,
          w k = Complex.I * ((k i₁ : ℂ) * a k i₂ - (k i₂ : ℂ) * a k i₁)) →
      partialDeriv i₁ (fun y => fourierValue s a y i₂) x -
          partialDeriv i₂ (fun y => fourierValue s a y i₁) x =
        ∑ k ∈ s, char k x * w k := by
    intro i₁ i₂ w hw
    rw [partialDeriv_fourierValue, partialDeriv_fourierValue,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hw]
    ring
  funext j
  fin_cases j
  · exact comp 1 2 (fun k => curlSymbol k (a k) 0) fun k => by
      simp [curlSymbol, Vec3.cross, latticeToComplex]
  · exact comp 2 0 (fun k => curlSymbol k (a k) 1) fun k => by
      simp [curlSymbol, Vec3.cross, latticeToComplex]
  · exact comp 0 1 (fun k => curlSymbol k (a k) 2) fun k => by
      simp [curlSymbol, Vec3.cross, latticeToComplex]

/-- The physical velocity field of a finite Fourier field. -/
def velocity (u : TrigField) (x : Fin 3 → ℝ) : CVec :=
  fourierValue u.coeff.support (fun k => u.coeff k) x

theorem velocity_eq (u : TrigField) :
    velocity u = fourierValue u.coeff.support (fun k => u.coeff k) := rfl

/-- The physical image `T u` of a finite Fourier field. -/
def mappedVelocity (T : MultiplierSymbol) (u : TrigField) (x : Fin 3 → ℝ) : CVec :=
  fourierValue u.coeff.support (fun p => T.map p (u.coeff p)) x

theorem mappedVelocity_eq (T : MultiplierSymbol) (u : TrigField) :
    mappedVelocity T u =
      fourierValue u.coeff.support (fun p => T.map p (u.coeff p)) := rfl

/-- The physical vorticity of `u` is the field of the Fourier curl `curlField u`. -/
theorem physicalCurl_velocity (u : TrigField) (x : Fin 3 → ℝ) :
    physicalCurl (velocity u) x =
      fourierValue u.coeff.support (fun q => (curlField u).coeff q) x := by
  rw [velocity_eq, physicalCurl_fourierValue]
  simp [curlField_coeff]

theorem physicalCurl_velocity_fun (u : TrigField) :
    (fun y => physicalCurl (velocity u) y) =
      fun y => fourierValue u.coeff.support (fun q => (curlField u).coeff q) y :=
  funext fun y => physicalCurl_velocity u y

/-! ## Rearrangement helpers -/

private theorem sum_mul_sum_mul_sum (s : Finset LatticeVec)
    (a b c : LatticeVec → ℂ) :
    (∑ p ∈ s, a p) * ((∑ q ∈ s, b q) * (∑ r ∈ s, c r)) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, a p * (b q * c r) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]

private theorem sum_comm_triple {ι : Type*} [Fintype ι] (s : Finset LatticeVec)
    (G : ι → LatticeVec → LatticeVec → LatticeVec → ℂ) :
    ∑ t : ι, ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, G t p q r =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t : ι, G t p q r := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]

private theorem sum_fin_out (s : Finset LatticeVec)
    (G : Fin 3 → Fin 3 → LatticeVec → LatticeVec → LatticeVec → ℂ) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, G i j p q r =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ i : Fin 3, ∑ j : Fin 3, G i j p q r := by
  rw [show (∑ i : Fin 3, ∑ j : Fin 3, ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, G i j p q r) =
      ∑ i : Fin 3, ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ j : Fin 3, G i j p q r from
    Finset.sum_congr rfl fun i _ => sum_comm_triple s (G i)]
  exact sum_comm_triple s fun i p q r => ∑ j : Fin 3, G i j p q r

private theorem contraction_bridge (s : Finset LatticeVec)
    (A B C : LatticeVec → Fin 3 → Fin 3 → ℂ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
        (∑ p ∈ s, A p i j) * ((∑ q ∈ s, B q i j) * (∑ r ∈ s, C r i j))) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ i : Fin 3, ∑ j : Fin 3,
        A p i j * (B q i j * C r i j) := by
  rw [show (∑ i : Fin 3, ∑ j : Fin 3,
        (∑ p ∈ s, A p i j) * ((∑ q ∈ s, B q i j) * (∑ r ∈ s, C r i j))) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
        A p i j * (B q i j * C r i j) from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      sum_mul_sum_mul_sum s _ _ _]
  exact sum_fin_out s fun i j p q r => A p i j * (B q i j * C r i j)

/-! ## The physical strain–vorticity density -/

/-- The pointwise physical contraction `sym ∇(Tu) : (ω ⊗ ω)`, where `ω` is the
vorticity obtained from `u` by real differentiation. -/
def strainVorticityDensity (T : MultiplierSymbol) (u : TrigField)
    (x : Fin 3 → ℝ) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ((1 / 2 : ℂ) *
        (partialDeriv i (fun y => mappedVelocity T u y j) x +
          partialDeriv j (fun y => mappedVelocity T u y i) x)) *
      (physicalCurl (velocity u) x i * physicalCurl (velocity u) x j)

/-- The physical contraction, expanded as a resonant sum of Fourier atoms. -/
theorem strainVorticityDensity_eq_tripleSum (T : MultiplierSymbol) (u : TrigField)
    (x : Fin 3 → ℝ) :
    strainVorticityDensity T u x =
      ∑ p ∈ u.coeff.support, ∑ q ∈ u.coeff.support, ∑ r ∈ u.coeff.support,
        strainInteraction p (T.map p (u.coeff p)) ((curlField u).coeff q)
          ((curlField u).coeff r) * char (p + q + r) x := by
  classical
  have hA : ∀ i j : Fin 3,
      ((1 / 2 : ℂ) *
          (partialDeriv i (fun y => mappedVelocity T u y j) x +
            partialDeriv j (fun y => mappedVelocity T u y i) x)) =
        ∑ p ∈ u.coeff.support,
          (1 / 2 : ℂ) *
            ((Complex.I * (p i : ℂ)) * (char p x * (T.map p (u.coeff p)) j) +
              (Complex.I * (p j : ℂ)) * (char p x * (T.map p (u.coeff p)) i)) := by
    intro i j
    simp only [mappedVelocity_eq, partialDeriv_fourierValue]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hB : ∀ i : Fin 3, physicalCurl (velocity u) x i =
      ∑ q ∈ u.coeff.support, char q x * ((curlField u).coeff q) i := by
    intro i
    rw [physicalCurl_velocity]
    rfl
  rw [strainVorticityDensity]
  simp only [hA, hB]
  rw [contraction_bridge u.coeff.support
    (fun p i j => (1 / 2 : ℂ) *
      ((Complex.I * (p i : ℂ)) * (char p x * (T.map p (u.coeff p)) j) +
        (Complex.I * (p j : ℂ)) * (char p x * (T.map p (u.coeff p)) i)))
    (fun q i _ => char q x * ((curlField u).coeff q) i)
    (fun r _ j => char r x * ((curlField u).coeff r) j)]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [char_add, char_add]
  simp only [Fin.sum_univ_three, strainInteraction, Vec3.dot, latticeToComplex]
  ring

/-- **The physical-space realization.**  The normalized integral over the
three-torus of the pointwise contraction `sym ∇(Tu) : (ω ⊗ ω)` is exactly the
functional classified by Corollary C. -/
theorem torusMean_strainVorticityDensity (T : MultiplierSymbol) (u : TrigField) :
    torusMean (strainVorticityDensity T u) = physicalSVCubicForm T u := by
  rw [torusMean_congr (strainVorticityDensity_eq_tripleSum T u),
    torusMean_tripleSum]
  rfl

/-- Universal cancellation of the physical-space integral. -/
def UniversalTorusSVCancellation (T : MultiplierSymbol) : Prop :=
  ∀ u : TrigField, torusMean (strainVorticityDensity T u) = 0

theorem universalTorusSV_iff_universalSV (T : MultiplierSymbol) :
    UniversalTorusSVCancellation T ↔ UniversalSVCancellation T := by
  constructor <;> intro h u
  · rw [← physicalSVCubicForm_eq_svCubicForm, ← torusMean_strainVorticityDensity]
    exact h u
  · rw [torusMean_strainVorticityDensity, physicalSVCubicForm_eq_svCubicForm]
    exact h u

/-- **Corollary C, with a physical-space integral as its hypothesis.** -/
theorem corollaryC_torusIntegral (T : MultiplierSymbol) :
    UniversalTorusSVCancellation T ↔ HasStrainGeneratorForm T := by
  rw [universalTorusSV_iff_universalSV, corollaryC]

/-- The solenoidal specialization, again for the physical-space integral. -/
theorem corollaryC_torusIntegral_solenoidal (T : MultiplierSymbol)
    (hsol : HasSolenoidalOutput T) :
    UniversalTorusSVCancellation T ↔ HasLaplacianCurlForm T := by
  rw [universalTorusSV_iff_universalSV, corollaryC_solenoidal T hsol]

/-! ## Integration by parts in physical space -/

/-- The physical convective derivative `(ω · ∇)ω` of the vorticity. -/
def vorticityTransport (u : TrigField) (x : Fin 3 → ℝ) : CVec :=
  fun j => ∑ i : Fin 3, physicalCurl (velocity u) x i *
    partialDeriv i (fun y => physicalCurl (velocity u) y j) x

/-- The physical transport density `Tu · (ω · ∇)ω`. -/
def transportDensity (T : MultiplierSymbol) (u : TrigField)
    (x : Fin 3 → ℝ) : ℂ :=
  Vec3.dot (mappedVelocity T u x) (vorticityTransport u x)

theorem transportDensity_eq_tripleSum (T : MultiplierSymbol) (u : TrigField)
    (x : Fin 3 → ℝ) :
    transportDensity T u x =
      ∑ p ∈ u.coeff.support, ∑ q ∈ u.coeff.support, ∑ r ∈ u.coeff.support,
        (Complex.I *
            (Vec3.dot ((curlField u).coeff q) (latticeToComplex r) *
              Vec3.dot (T.map p (u.coeff p)) ((curlField u).coeff r))) *
          char (p + q + r) x := by
  classical
  have hA : ∀ j : Fin 3, mappedVelocity T u x j =
      ∑ p ∈ u.coeff.support, char p x * (T.map p (u.coeff p)) j :=
    fun _ => rfl
  have hB : ∀ i : Fin 3, physicalCurl (velocity u) x i =
      ∑ q ∈ u.coeff.support, char q x * ((curlField u).coeff q) i := by
    intro i
    rw [physicalCurl_velocity]
    rfl
  have hC : ∀ i j : Fin 3,
      partialDeriv i (fun y => physicalCurl (velocity u) y j) x =
        ∑ r ∈ u.coeff.support,
          (Complex.I * (r i : ℂ)) * (char r x * ((curlField u).coeff r) j) := by
    intro i j
    have hfun : (fun y => physicalCurl (velocity u) y j) =
        fun y => fourierValue u.coeff.support
          (fun q => (curlField u).coeff q) y j := by
      funext y
      rw [physicalCurl_velocity]
    rw [hfun, partialDeriv_fourierValue]
  have hstep : transportDensity T u x =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∑ p ∈ u.coeff.support, char p x * (T.map p (u.coeff p)) j) *
          ((∑ q ∈ u.coeff.support, char q x * ((curlField u).coeff q) i) *
            (∑ r ∈ u.coeff.support,
              (Complex.I * (r i : ℂ)) *
                (char r x * ((curlField u).coeff r) j))) := by
    simp only [transportDensity, Vec3.dot, vorticityTransport,
      Fin.sum_univ_three, hA, hB, hC]
    ring
  rw [hstep, contraction_bridge u.coeff.support
    (fun p _ j => char p x * (T.map p (u.coeff p)) j)
    (fun q i _ => char q x * ((curlField u).coeff q) i)
    (fun r i j => (Complex.I * (r i : ℂ)) *
      (char r x * ((curlField u).coeff r) j))]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [char_add, char_add]
  simp only [Fin.sum_univ_three, Vec3.dot, latticeToComplex]
  ring

/-- The normalized integral of the physical transport density. -/
theorem torusMean_transportDensity (T : MultiplierSymbol) (u : TrigField) :
    torusMean (transportDensity T u) =
      Complex.I * tripleSum u.coeff.support (transportAtom T u) := by
  classical
  rw [torusMean_congr (transportDensity_eq_tripleSum T u), torusMean_tripleSum,
    tripleSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hres : p + q + r = 0
  · simp [transportAtom, hres, Vec3.dot_smul_right]
  · simp [transportAtom, hres]

/-- **Integration by parts in physical space.**  The integral of the
symmetric-gradient contraction is minus the integral of the transport
density: `∫ sym ∇(Tu) : (ω ⊗ ω) = -∫ Tu · (ω · ∇)ω`. -/
theorem torusMean_strainVorticity_eq_neg_transport
    (T : MultiplierSymbol) (u : TrigField) :
    torusMean (strainVorticityDensity T u) = -torusMean (transportDensity T u) := by
  rw [torusMean_strainVorticityDensity, torusMean_transportDensity,
    physicalSVCubicForm_eq_neg_I_transport]

end

end FourierMultiplierRigidity.StrainVorticity
