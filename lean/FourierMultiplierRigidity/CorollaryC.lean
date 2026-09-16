import FourierMultiplierRigidity.CorollaryB

/-!
# Corollary C: the strain–vorticity pullback

The functional is the Fourier representation of
`⟨sym ∇(Tu), ω ⊗ ω⟩ = -⟨Tu, (ω · ∇)ω⟩`, with `ω = curl u`.
It is NOT `⟨Tu, S(u)ω⟩`.  We use the integration-by-parts expression
as the definition; `strainInteraction_eq_transport` also checks the
symmetric-gradient contraction at each resonant triple.

Curl and its inverse act on finite Fourier fields.  The field-level bridge
and surjectivity transfer Theorem A, giving all twelve parameters.  Only
with solenoidal output does Corollary B give the two-parameter subfamily.
The classification inherits Theorem A's compiler-trusted seed certificate.
-/

namespace FourierMultiplierRigidity.StrainVorticity
open scoped ComplexConjugate

noncomputable section

/-- Squared frequency, embedded in ℂ (real and positive for k ≠ 0). -/
def freqSq (k : LatticeVec) : ℂ :=
  Vec3.dot (latticeToComplex k) (latticeToComplex k)

theorem freqSq_ne_zero (k : LatticeVec) (hk : k ≠ 0) : freqSq k ≠ 0 := by
  unfold freqSq
  rw [latticeToComplex_eq_realToComplex]
  exact complexified_real_dot_self_ne_zero _ (latticeToReal_ne_zero hk)

@[simp] theorem freqSq_neg (k : LatticeVec) : freqSq (-k) = freqSq k := by
  simp [freqSq, Vec3.dot, latticeToComplex]

@[simp] theorem conj_freqSq (k : LatticeVec) : conj (freqSq k) = freqSq k := by
  simp [freqSq, Vec3.dot, latticeToComplex]

@[simp] theorem curlLinear_apply (k : LatticeVec) (v : CVec) :
    curlLinear k v = curlSymbol k v := rfl

theorem curl_transverse (k : LatticeVec) (v : CVec) :
    Transverse k (curlSymbol k v) := by
  simp [Transverse, curlSymbol, Vec3.dot_cross_self_left]

/-- Full-space identity; the longitudinal term disappears on k⊥. -/
theorem curl_sq (k : LatticeVec) (v : CVec) :
    curlSymbol k (curlSymbol k v) =
      freqSq k • v - Vec3.dot (latticeToComplex k) v • latticeToComplex k := by
  funext i
  fin_cases i <;>
    simp [curlSymbol, Vec3.cross, Vec3.dot, freqSq, smul_eq_mul,
      Complex.I_mul_I] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem curl_sq_transverse (k : LatticeVec) (v : CVec) (hv : Transverse k v) :
    curlSymbol k (curlSymbol k v) = freqSq k • v := by
  rw [curl_sq, hv, zero_smul, sub_zero]

/-- Correct sign: C⁻¹ = C/|k|² on the nonzero transverse fiber. -/
def inverseCurl (k : LatticeVec) : CVec →ₗ[ℂ] CVec :=
  (freqSq k)⁻¹ • curlLinear k

@[simp] theorem inverseCurl_apply (k : LatticeVec) (v : CVec) :
    inverseCurl k v = (freqSq k)⁻¹ • curlSymbol k v := rfl

theorem inverseCurl_transverse (k : LatticeVec) (v : CVec) :
    Transverse k (inverseCurl k v) :=
  transverse_smul _ (curl_transverse k v)

theorem inverseCurl_curl (k : LatticeVec) (hk : k ≠ 0) (v : CVec)
    (hv : Transverse k v) : inverseCurl k (curlSymbol k v) = v := by
  rw [inverseCurl_apply, curl_sq_transverse k v hv, smul_smul,
    inv_mul_cancel₀ (freqSq_ne_zero k hk), one_smul]

theorem curl_inverseCurl (k : LatticeVec) (hk : k ≠ 0) (v : CVec)
    (hv : Transverse k v) : curlSymbol k (inverseCurl k v) = v := by
  change curlLinear k ((freqSq k)⁻¹ • curlLinear k v) = v
  rw [map_smul]
  exact inverseCurl_curl k hk v hv

theorem inverseCurl_reality (k : LatticeVec) (v : CVec) :
    inverseCurl (-k) (conjVec v) = conjVec (inverseCurl k v) := by
  rw [inverseCurl_apply, inverseCurl_apply, freqSq_neg, curlSymbol_reality]
  funext i
  simp [conjVec, Pi.smul_apply, smul_eq_mul]

/-- Apply a transverse, reality-compatible mode map to a finite field. -/
def mapField (M : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hM : ∀ k v, Transverse k v → Transverse k (M k v))
    (hreal : ∀ k v, Transverse k v → M (-k) (conjVec v) = conjVec (M k v))
    (u : TrigField) : TrigField where
  coeff := Finsupp.onFinset u.coeff.support (fun k => M k (u.coeff k)) (by
    intro k hk
    exact Finsupp.mem_support_iff.mpr (fun hz => hk (by rw [hz, map_zero])))
  meanZero := by simp [u.meanZero]
  divergenceFree k := by simpa using hM k (u.coeff k) (u.divergenceFree k)
  reality k := by simpa [u.reality k] using hreal k (u.coeff k) (u.divergenceFree k)

@[simp] theorem mapField_coeff (M hM hreal u k) :
    (mapField M hM hreal u).coeff k = M k (u.coeff k) := by
  simp [mapField]

def curlField (u : TrigField) : TrigField :=
  mapField curlLinear (fun k v _ => curl_transverse k v)
    (fun k v _ => curlSymbol_reality k v) u

def inverseCurlField (u : TrigField) : TrigField :=
  mapField inverseCurl (fun k v _ => inverseCurl_transverse k v)
    (fun k v _ => inverseCurl_reality k v) u

@[simp] theorem curlField_coeff (u : TrigField) (k : LatticeVec) :
    (curlField u).coeff k = curlSymbol k (u.coeff k) := by
  change curlLinear k (u.coeff k) = curlSymbol k (u.coeff k)
  rfl

@[simp] theorem inverseCurlField_coeff (u : TrigField) (k : LatticeVec) :
    (inverseCurlField u).coeff k = inverseCurl k (u.coeff k) := by
  simp [inverseCurlField]

theorem field_ext (u v : TrigField) (h : ∀ k, u.coeff k = v.coeff k) : u = v := by
  cases u; cases v
  have hc := Finsupp.ext h
  cases hc
  rfl

@[simp] theorem curl_inverseCurlField (u : TrigField) :
    curlField (inverseCurlField u) = u := by
  apply field_ext
  intro k
  by_cases hk : k = 0
  · subst k; simp [u.meanZero, curlSymbol]
  · simpa using curl_inverseCurl k hk (u.coeff k) (u.divergenceFree k)

@[simp] theorem inverseCurl_curlField (u : TrigField) :
    inverseCurlField (curlField u) = u := by
  apply field_ext
  intro k
  by_cases hk : k = 0
  · subst k; simp [u.meanZero, curlSymbol]
  · simpa using inverseCurl_curl k hk (u.coeff k) (u.divergenceFree k)

/-- Mean-zero and transversality make curl support-preserving. -/
theorem curlField_support (u : TrigField) : (curlField u).coeff.support = u.coeff.support := by
  classical
  ext k
  simp only [Finsupp.mem_support_iff, curlField_coeff]
  constructor
  · intro h hz
    apply h
    rw [hz]
    exact (curlLinear k).map_zero
  · intro h hz
    have hk : k ≠ 0 := by
      intro hk; subst k; exact h u.meanZero
    have hi := inverseCurl_curl k hk (u.coeff k) (u.divergenceFree k)
    rw [hz, map_zero] at hi
    exact h hi.symm

/-- A direct coefficient-level symmetric-gradient contraction.
The first argument is the Fourier amplitude of Tu at p. -/
def strainInteraction (p : LatticeVec) (a b c : CVec) : ℂ :=
  (Complex.I / 2) * (Vec3.dot (latticeToComplex p) b * Vec3.dot a c +
    Vec3.dot (latticeToComplex p) c * Vec3.dot a b)

/-- Fourier integration by parts at one resonant triple, with b⊥q and c⊥r. -/
theorem strainInteraction_eq_transport (p q r : LatticeVec) (a b c : CVec)
    (hres : p + q + r = 0) (hb : Transverse q b) (hc : Transverse r c) :
    strainInteraction p a b c = -(Complex.I / 2) *
      (Vec3.dot (latticeToComplex r) b * Vec3.dot a c +
       Vec3.dot (latticeToComplex q) c * Vec3.dot a b) := by
  have hp : latticeToComplex p = -latticeToComplex q - latticeToComplex r := by
    funext i
    have hi := congrFun hres i
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    have hi' : p i = -q i - r i := by omega
    simp [latticeToComplex, hi']
  have hpb : Vec3.dot (latticeToComplex p) b = -Vec3.dot (latticeToComplex r) b := by
    rw [hp]; simp [Vec3.dot, Transverse] at hb ⊢; linear_combination -hb
  have hpc : Vec3.dot (latticeToComplex p) c = -Vec3.dot (latticeToComplex q) c := by
    rw [hp]; simp [Vec3.dot, Transverse] at hc ⊢; linear_combination -hc
  unfold strainInteraction
  rw [hpb, hpc]
  ring

/-- R = T curl⁻¹. The zero block is harmless because all tests have mean zero. -/
def pullback (T : MultiplierSymbol) : MultiplierSymbol where
  map k := (T.map k).comp (inverseCurl k)
  realityCompatible k v _ := by
    change T.map (-k) (inverseCurl (-k) (conjVec v)) = _
    rw [inverseCurl_reality, T.realityCompatible k _ (inverseCurl_transverse k v)]
    rfl

/-- The integrated-by-parts strain–vorticity functional, using Tu and ω directly. -/
def svCubicForm (T : MultiplierSymbol) (u : TrigField) : ℂ :=
  -(u.coeff.sum fun k uk => Vec3.dot (T.map k uk)
    (convectiveCoeff (curlField u) (-k)))

def UniversalSVCancellation (T : MultiplierSymbol) : Prop :=
  ∀ u : TrigField, svCubicForm T u = 0

theorem svCubicForm_eq_pullback (T : MultiplierSymbol) (u : TrigField) :
    svCubicForm T u = -cubicForm (pullback T) (curlField u) := by
  classical
  unfold svCubicForm cubicForm
  simp only [Finsupp.sum, curlField_support, curlField_coeff]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := by
    intro hz; subst k; exact Finsupp.mem_support_iff.mp hk u.meanZero
  simp [pullback, inverseCurl_curl k hk0 (u.coeff k) (u.divergenceFree k)]

theorem universalSV_iff_pullback (T : MultiplierSymbol) :
    UniversalSVCancellation T ↔ UniversalCancellation (pullback T) := by
  constructor
  · intro h w
    have hw := h (inverseCurlField w)
    rw [svCubicForm_eq_pullback, curl_inverseCurlField] at hw
    exact neg_eq_zero.mp hw
  · intro h u
    rw [svCubicForm_eq_pullback, h, neg_zero]

/-- Full twelve-parameter conclusion, with no output-range hypothesis. -/
def HasStrainGeneratorForm (T : MultiplierSymbol) : Prop :=
  ∃ A B : RMatrix, A.transpose = A ∧ B.transpose = B ∧
    ∀ k, k ≠ 0 → ∀ v, Transverse k v →
      T.map k v = generatorMap A B k (curlSymbol k v)

theorem strainGenerator_iff_pullback (T : MultiplierSymbol) :
    HasStrainGeneratorForm T ↔ HasGeneratorForm (pullback T) := by
  constructor
  · rintro ⟨A, B, hA, hB, h⟩
    refine ⟨A, B, hA, hB, ?_⟩
    intro k hk v hv
    change T.map k (inverseCurl k v) = _
    rw [h k hk _ (inverseCurl_transverse k v), curl_inverseCurl k hk v hv]
  · rintro ⟨A, B, hA, hB, h⟩
    refine ⟨A, B, hA, hB, ?_⟩
    intro k hk v hv
    have hh := h k hk (curlSymbol k v) (curl_transverse k v)
    change T.map k (inverseCurl k (curlSymbol k v)) = _ at hh
    rwa [inverseCurl_curl k hk v hv] at hh

/-- Corollary C in the unrestricted-output class. -/
theorem corollaryC (T : MultiplierSymbol) :
    UniversalSVCancellation T ↔ HasStrainGeneratorForm T := by
  rw [universalSV_iff_pullback, theoremA, ← strainGenerator_iff_pullback]

/-- Expands the generator composition into A curl + B(-Δ) + curl B curl. -/
theorem strainGenerator_expansion (A B : RMatrix) (k : LatticeVec) (v : CVec)
    (hv : Transverse k v) :
    generatorMap A B k (curlSymbol k v) =
      Matrix.mulVec (complexifyMatrix A) (curlSymbol k v) +
      freqSq k • Matrix.mulVec (complexifyMatrix B) v +
      curlSymbol k (Matrix.mulVec (complexifyMatrix B) (curlSymbol k v)) := by
  rw [generatorMap_apply, curl_sq_transverse k v hv]
  rw [show Matrix.mulVec (complexifyMatrix B) (freqSq k • v) =
    freqSq k • Matrix.mulVec (complexifyMatrix B) v from
      (complexifyMatrix B).mulVecLin.map_smul _ _]

/-- This conclusion requires solenoidal output. -/
def HasLaplacianCurlForm (T : MultiplierSymbol) : Prop :=
  ∃ c d : ℝ, ∀ k, k ≠ 0 → ∀ v, Transverse k v →
    T.map k v = (c : ℂ) • curlSymbol k v + (d : ℂ) • (freqSq k • v)

theorem pullback_solenoidal (T : MultiplierSymbol) (hsol : HasSolenoidalOutput T) :
    HasSolenoidalOutput (pullback T) := by
  intro k hk v _
  exact hsol k hk _ (inverseCurl_transverse k v)

theorem laplacianCurl_iff_pullback (T : MultiplierSymbol) :
    HasLaplacianCurlForm T ↔ HasScalarForm (pullback T) := by
  constructor
  · rintro ⟨c, d, h⟩
    refine ⟨c, d, ?_⟩
    intro k hk v hv
    change T.map k (inverseCurl k v) = _
    rw [h k hk _ (inverseCurl_transverse k v), curl_inverseCurl k hk v hv]
    simp [inverseCurl_apply, smul_smul, freqSq_ne_zero k hk]
  · rintro ⟨c, d, h⟩
    refine ⟨c, d, ?_⟩
    intro k hk v hv
    have hh := h k hk (curlSymbol k v) (curl_transverse k v)
    change T.map k (inverseCurl k (curlSymbol k v)) = _ at hh
    rwa [inverseCurl_curl k hk v hv, curl_sq_transverse k v hv] at hh

/-- Solenoidal specialization of Corollary C, retaining its essential premise. -/
theorem corollaryC_solenoidal (T : MultiplierSymbol) (hsol : HasSolenoidalOutput T) :
    UniversalSVCancellation T ↔ HasLaplacianCurlForm T := by
  rw [universalSV_iff_pullback, corollaryB _ (pullback_solenoidal T hsol),
    ← laplacianCurl_iff_pullback]

/-- The actual second-order multiplier, not the first-order Euler generator. -/
def strainGenerator (A B : RMatrix) : MultiplierSymbol where
  map k := (generatorMap A B k).comp (curlLinear k)
  realityCompatible k v _ := by
    change (generatorSymbol A B).map (-k) (curlSymbol (-k) (conjVec v)) = _
    rw [curlSymbol_reality,
      (generatorSymbol A B).realityCompatible k _ (curl_transverse k v)]
    rfl

theorem strainGenerator_cancellation (A B : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B) :
    UniversalSVCancellation (strainGenerator A B) := by
  apply (universalSV_iff_pullback _).mpr
  apply hasGeneratorForm_universalCancellation
  apply (strainGenerator_iff_pullback _).mp
  exact ⟨A, B, hA, hB, fun _ _ _ _ => rfl⟩

end
end FourierMultiplierRigidity.StrainVorticity
