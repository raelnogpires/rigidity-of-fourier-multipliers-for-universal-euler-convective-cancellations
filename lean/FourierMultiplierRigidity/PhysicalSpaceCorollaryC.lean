import FourierMultiplierRigidity.CorollaryC

/-!
# Physical-space realization of Corollary C

The existing Corollary C starts from the integrated-by-parts Fourier
functional.  Here we construct the zero Fourier coefficient of
`sym ∇(Tu) : (ω ⊗ ω)` itself and prove, for every finite Fourier field, that it
equals that functional.  Thus the classification theorem applies to the
physical-space contraction rather than merely to a definition chosen after
integration by parts.
-/

namespace FourierMultiplierRigidity.StrainVorticity

noncomputable section

/-- A resonant Fourier atom of `sym ∇(Tu) : (ω ⊗ ω)`. -/
def physicalStrainAtom (T : MultiplierSymbol) (u : TrigField)
    (p q r : LatticeVec) : ℂ :=
  if p + q + r = 0 then
    strainInteraction p (T.map p (u.coeff p))
      ((curlField u).coeff q) ((curlField u).coeff r)
  else 0

/-- Normalized torus integration of the physical contraction: multiplication
of finite Fourier series followed by extraction of the zero mode. -/
def physicalSVCubicForm (T : MultiplierSymbol) (u : TrigField) : ℂ :=
  tripleSum u.coeff.support (physicalStrainAtom T u)

/-! ## The complete finite Fourier polynomial and torus integral -/

/-- The full Fourier series of the pointwise contraction
`sym ∇(Tu) : (ω ⊗ ω)`.  It is a genuine finitely supported series; its
frequency `k` coefficient is assembled from every ordered triple summing to
`k`. -/
def physicalSVFourierSeries (T : MultiplierSymbol) (u : TrigField) :
    LatticeVec →₀ ℂ :=
  ∑ p ∈ u.coeff.support,
    ∑ q ∈ u.coeff.support,
      ∑ r ∈ u.coeff.support,
        Finsupp.single (p + q + r)
          (strainInteraction p (T.map p (u.coeff p))
            ((curlField u).coeff q) ((curlField u).coeff r))

/-- Normalized integration of a finite Fourier series on the three-torus.
For trigonometric polynomials this is exactly extraction of the constant
Fourier coefficient. -/
def finiteTorusIntegral (f : LatticeVec →₀ ℂ) : ℂ := f 0

/-- The normalized torus integral of the pointwise physical contraction is
the resonant triple sum used in `physicalSVCubicForm`. -/
theorem finiteTorusIntegral_physicalSVFourierSeries
    (T : MultiplierSymbol) (u : TrigField) :
    finiteTorusIntegral (physicalSVFourierSeries T u) =
      physicalSVCubicForm T u := by
  classical
  simp [finiteTorusIntegral, physicalSVFourierSeries,
    physicalSVCubicForm, tripleSum, physicalStrainAtom,
    Finsupp.single_apply]

/-- Universal cancellation stated directly as a normalized torus integral
of the complete pointwise contraction polynomial. -/
def UniversalFiniteTorusSVCancellation (T : MultiplierSymbol) : Prop :=
  ∀ u : TrigField,
    finiteTorusIntegral (physicalSVFourierSeries T u) = 0

/-- The transport atom appearing after physical-space integration by parts. -/
def transportAtom (T : MultiplierSymbol) (u : TrigField)
    (p q r : LatticeVec) : ℂ :=
  if p + q + r = 0 then
    Vec3.dot (T.map p (u.coeff p))
      (Vec3.dot ((curlField u).coeff q) (latticeToComplex r) •
        (curlField u).coeff r)
  else 0

private theorem tripleSum_swap23_physical
    {α : Type*} [DecidableEq α] (s : Finset α)
    (F : α → α → α → ℂ) :
    tripleSum s (fun p q r ↦ F p r q) = tripleSum s F := by
  simp only [tripleSum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]

private theorem tripleSum_smul_scalar
    {α : Type*} [DecidableEq α] (s : Finset α) (c : ℂ)
    (F : α → α → α → ℂ) :
    tripleSum s (fun p q r ↦ c * F p q r) = c * tripleSum s F := by
  simp [tripleSum, Finset.mul_sum]

/-- Summed integration by parts.  The factor `1/2` from the symmetric
gradient disappears because the two parent-frequency terms are exchanged by
`q ↔ r` in the complete ordered sum. -/
theorem physicalSVCubicForm_eq_neg_I_transport
    (T : MultiplierSymbol) (u : TrigField) :
    physicalSVCubicForm T u =
      -(Complex.I * tripleSum u.coeff.support (transportAtom T u)) := by
  classical
  let firstTerm (p q r : LatticeVec) : ℂ :=
    if p + q + r = 0 then
      Vec3.dot ((curlField u).coeff q) (latticeToComplex r) *
        Vec3.dot (T.map p (u.coeff p)) ((curlField u).coeff r)
    else 0
  let secondTerm (p q r : LatticeVec) : ℂ :=
    if p + q + r = 0 then
      Vec3.dot ((curlField u).coeff r) (latticeToComplex q) *
        Vec3.dot (T.map p (u.coeff p)) ((curlField u).coeff q)
    else 0
  have hatom : ∀ p q r,
      physicalStrainAtom T u p q r =
        -(Complex.I / 2) * (firstTerm p q r + secondTerm p q r) := by
    intro p q r
    by_cases hres : p + q + r = 0
    · have h := strainInteraction_eq_transport p q r
        (T.map p (u.coeff p)) ((curlField u).coeff q)
        ((curlField u).coeff r) hres
        ((curlField u).divergenceFree q) ((curlField u).divergenceFree r)
      simpa [physicalStrainAtom, firstTerm, secondTerm, hres,
        Vec3.dot_comm] using h
    · simp [physicalStrainAtom, firstTerm, secondTerm, hres]
  have hswap :
      tripleSum u.coeff.support secondTerm =
        tripleSum u.coeff.support firstTerm := by
    rw [← tripleSum_swap23_physical u.coeff.support firstTerm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    simp [firstTerm, secondTerm, add_comm, add_left_comm]
  have htransport :
      tripleSum u.coeff.support (transportAtom T u) =
        tripleSum u.coeff.support firstTerm := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    simp [transportAtom, firstTerm, Vec3.dot_smul_right, Vec3.dot_comm]
  unfold physicalSVCubicForm
  rw [show tripleSum u.coeff.support (physicalStrainAtom T u) =
      tripleSum u.coeff.support (fun p q r =>
        -(Complex.I / 2) * (firstTerm p q r + secondTerm p q r)) by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    exact hatom p q r]
  rw [show tripleSum u.coeff.support (fun p q r =>
        -(Complex.I / 2) * (firstTerm p q r + secondTerm p q r)) =
      -(Complex.I / 2) *
        (tripleSum u.coeff.support firstTerm +
          tripleSum u.coeff.support secondTerm) by
    rw [show (fun p q r => -(Complex.I / 2) *
          (firstTerm p q r + secondTerm p q r)) =
        (fun p q r => -(Complex.I / 2) * firstTerm p q r +
          -(Complex.I / 2) * secondTerm p q r) by
      funext p q r
      ring]
    rw [show tripleSum u.coeff.support (fun p q r =>
          -(Complex.I / 2) * firstTerm p q r +
            -(Complex.I / 2) * secondTerm p q r) =
        tripleSum u.coeff.support (fun p q r =>
          -(Complex.I / 2) * firstTerm p q r) +
        tripleSum u.coeff.support (fun p q r =>
          -(Complex.I / 2) * secondTerm p q r) by
      simp [tripleSum, Finset.sum_add_distrib]]
    rw [tripleSum_smul_scalar, tripleSum_smul_scalar]
    ring]
  rw [hswap, htransport]
  ring

private theorem finsupp_sum_eq_support_sum_physical
    {α M N : Type*} [Zero M] [AddCommMonoid N]
    (f : α →₀ M) (g : α → M → N) :
    f.sum g = ∑ a ∈ f.support, g a (f a) := by
  rfl

/-- Expansion of the already integrated transport functional as the same
complete resonant sum. -/
theorem svCubicForm_eq_neg_I_transport
    (T : MultiplierSymbol) (u : TrigField) :
    svCubicForm T u =
      -(Complex.I * tripleSum u.coeff.support (transportAtom T u)) := by
  classical
  unfold svCubicForm
  apply congrArg Neg.neg
  rw [finsupp_sum_eq_support_sum_physical]
  change (∑ p ∈ u.coeff.support,
      Vec3.dot (T.map p (u.coeff p)) (convectiveCoeff (curlField u) (-p))) = _
  unfold convectiveCoeff
  simp [tripleSum, transportAtom, pair_sum_eq_neg_iff_triple_sum_eq_zero,
    Vec3.dot_sum_right, Vec3.dot_smul_right, Finset.mul_sum,
    finsupp_sum_eq_support_sum_physical]
  apply Finset.sum_congr rfl
  intro p hp
  rw [curlField_support]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hres : p + q + r = 0
  · simp [hres, Vec3.dot_smul_right, Vec3.dot_comm]
  · simp [hres, Vec3.dot]

/-- The physical symmetric-gradient contraction equals the Fourier
integration-by-parts functional used by Corollary C. -/
theorem physicalSVCubicForm_eq_svCubicForm
    (T : MultiplierSymbol) (u : TrigField) :
    physicalSVCubicForm T u = svCubicForm T u := by
  rw [physicalSVCubicForm_eq_neg_I_transport,
    svCubicForm_eq_neg_I_transport]

/-- Universal cancellation stated with the physical-space contraction. -/
def UniversalPhysicalSVCancellation (T : MultiplierSymbol) : Prop :=
  ∀ u : TrigField, physicalSVCubicForm T u = 0

theorem universalPhysicalSV_iff_universalSV (T : MultiplierSymbol) :
    UniversalPhysicalSVCancellation T ↔ UniversalSVCancellation T := by
  constructor <;> intro h u
  · rw [← physicalSVCubicForm_eq_svCubicForm]
    exact h u
  · rw [physicalSVCubicForm_eq_svCubicForm]
    exact h u

theorem universalFiniteTorusSV_iff_universalPhysicalSV
    (T : MultiplierSymbol) :
    UniversalFiniteTorusSVCancellation T ↔
      UniversalPhysicalSVCancellation T := by
  constructor <;> intro h u
  · rw [← finiteTorusIntegral_physicalSVFourierSeries]
    exact h u
  · rw [finiteTorusIntegral_physicalSVFourierSeries]
    exact h u

/-- Corollary C in explicit finite-Fourier torus-integral form. -/
theorem corollaryC_finiteTorusIntegral (T : MultiplierSymbol) :
    UniversalFiniteTorusSVCancellation T ↔
      HasStrainGeneratorForm T := by
  rw [universalFiniteTorusSV_iff_universalPhysicalSV,
    universalPhysicalSV_iff_universalSV, corollaryC]

/-- Corollary C with the physical-space integral as its premise. -/
theorem corollaryC_physical (T : MultiplierSymbol) :
    UniversalPhysicalSVCancellation T ↔ HasStrainGeneratorForm T := by
  rw [universalPhysicalSV_iff_universalSV, corollaryC]

/-- Solenoidal specialization, again for the physical-space integral. -/
theorem corollaryC_physical_solenoidal
    (T : MultiplierSymbol) (hsol : HasSolenoidalOutput T) :
    UniversalPhysicalSVCancellation T ↔ HasLaplacianCurlForm T := by
  rw [universalPhysicalSV_iff_universalSV, corollaryC_solenoidal T hsol]

end
end FourierMultiplierRigidity.StrainVorticity
