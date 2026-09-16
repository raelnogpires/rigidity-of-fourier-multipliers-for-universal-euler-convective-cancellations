import FourierMultiplierRigidity.TheoremA

/-!
# Corollary B: solenoidal rigidity

If the multiplier is additionally required to preserve divergence-free fields,
the twelve-parameter family of Theorem A collapses to two real constants:

```lean
theorem corollaryB (R : MultiplierSymbol) (hsol : HasSolenoidalOutput R) :
    UniversalCancellation R ↔ HasScalarForm R
```

with `HasScalarForm R` saying `R (k) = c I + d curl` on every nonzero
transverse fiber.  Energy and helicity are the only possibilities, and the
cubic identity itself forces every nonzero-mode block to be Hermitian — no
Hermitian hypothesis is imposed anywhere.

The argument follows Section 3.2 of the manuscript.  Applying the range
condition to the generator form and splitting into real and imaginary parts
gives `k · A v = 0` and `k · B (k × v) = 0` for every real transverse `v`.
Since `v ↦ k × v` is onto the transverse plane — the division-free triple
product `cross_cross_transverse` — both reduce to `w ⊥ k → k · A w = 0`, and
symmetry turns that into `A k ∥ k`.  `scalarity_from_lattice_directions`
(Lemma 3.2, already proved in the root module) then forces `A = a I` and
`B = b I`, so `R = a I + 2b curl`.

The one genuinely new ingredient is `parallel_of_orthogonal_to_transverse`: a
real vector orthogonal to the whole transverse plane of `k` is parallel to `k`.
That is the equality case of Cauchy--Schwarz, obtained here from the explicit
witness `(k·k) w - (w·k) k` and positive-definiteness of the real dot product.

Everything in this file is kernel-checked.  `corollaryB` inherits the same
seven `native_decide` axioms as `theoremA`; see `lean/README.md`.
-/

namespace FourierMultiplierRigidity
set_option maxRecDepth 4000000

/-- A real vector orthogonal to the whole transverse plane of `k` is parallel
to `k`.  This is the equality case of Cauchy--Schwarz, run through the
explicit witness `(k·k) w - (w·k) k`. -/
theorem parallel_of_orthogonal_to_transverse (k w : RVec) (hk : k ≠ 0)
    (h : ∀ v : RVec, Vec3.dot k v = 0 → Vec3.dot w v = 0) : Parallel w k := by
  have hkk : 0 < Vec3.dot k k := real_dot_self_pos k hk
  set c := Vec3.dot w k / Vec3.dot k k with hc
  have hv0 : Vec3.dot k (Vec3.dot k k • w - Vec3.dot w k • k) = 0 := by
    simp [Vec3.dot]; ring
  have heq := h _ hv0
  have heq' : Vec3.dot k k * Vec3.dot w w - Vec3.dot w k * Vec3.dot w k = 0 := by
    have : Vec3.dot w (Vec3.dot k k • w - Vec3.dot w k • k)
        = Vec3.dot k k * Vec3.dot w w - Vec3.dot w k * Vec3.dot w k := by
      simp [Vec3.dot]; ring
    linarith [this ▸ heq]
  have key : Vec3.dot (w - c • k) (w - c • k) = 0 := by
    have expand : Vec3.dot (w - c • k) (w - c • k)
        = Vec3.dot w w - 2 * c * Vec3.dot w k + c * c * Vec3.dot k k := by
      simp [Vec3.dot]; ring
    rw [expand, hc]
    field_simp
    nlinarith [heq']
  have hzero : w - c • k = 0 := by
    by_contra hne
    have := real_dot_self_pos _ hne
    linarith
  exact ⟨c, sub_eq_zero.mp hzero⟩

theorem real_symmetric_mulVec_dot (A : RMatrix) (hA : A.transpose = A) (u v : RVec) :
    Vec3.dot (Matrix.mulVec A u) v = Vec3.dot (Matrix.mulVec A v) u := by
  have h₀₁ : A 0 1 = A 1 0 := by
    have := congrFun (congrFun hA 0) 1; simpa using this.symm
  have h₀₂ : A 0 2 = A 2 0 := by
    have := congrFun (congrFun hA 0) 2; simpa using this.symm
  have h₁₂ : A 1 2 = A 2 1 := by
    have := congrFun (congrFun hA 1) 2; simpa using this.symm
  simp [Vec3.dot, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [h₀₁, h₀₂, h₁₂]
  ring

/-- Vector triple product on the transverse plane: `k × (k × w) = -(k·k) w`
when `k · w = 0`.  Division-free, so `linear_combination` closes it. -/
theorem cross_cross_transverse (k w : RVec) (hw : Vec3.dot k w = 0) :
    Vec3.cross k (Vec3.cross k w) = -(Vec3.dot k k) • w := by
  funext i
  fin_cases i <;>
    simp [Vec3.cross, Vec3.dot] at hw ⊢ <;>
    first
      | linear_combination k 0 * hw
      | linear_combination k 1 * hw
      | linear_combination k 2 * hw

theorem transverse_cross (k w : RVec) : Vec3.dot k (Vec3.cross k w) = 0 :=
  Vec3.dot_cross_self_left k w

theorem dot_realToComplexVec (a b : RVec) :
    Vec3.dot (realToComplexVec a) (realToComplexVec b) = ((Vec3.dot a b : ℝ) : ℂ) := by
  simp [Vec3.dot, realToComplexVec]

theorem latticeToReal_ne_zero {k : LatticeVec} (hk : k ≠ 0) : latticeToReal k ≠ 0 := by
  intro h
  apply hk
  funext i
  have hi := congrFun h i
  simp [latticeToReal] at hi
  exact_mod_cast hi

/-- The range condition, split into its real and imaginary parts on a real
transverse input. -/
theorem solenoidal_real_split (A B : RMatrix) (k : LatticeVec) (v : RVec)
    (hsol : Transverse k (generatorMap A B k (realToComplexVec v))) :
    Vec3.dot (latticeToReal k) (Matrix.mulVec A v) = 0 ∧
      Vec3.dot (latticeToReal k) (crossAnticommutator B k v) = 0 := by
  rw [generatorMap_on_real] at hsol
  unfold Transverse at hsol
  rw [latticeToComplex_eq_realToComplex] at hsol
  rw [Vec3.dot_add_right, Vec3.dot_smul_right, dot_realToComplexVec,
    dot_realToComplexVec] at hsol
  constructor
  · have := congrArg Complex.re hsol
    simpa using this
  · have := congrArg Complex.im hsol
    simpa using this

theorem cross_smul_right (c : ℝ) (u v : RVec) :
    Vec3.cross u (c • v) = c • Vec3.cross u v := by
  funext i
  fin_cases i <;> simp [Vec3.cross] <;> ring

/-- The range condition forces both generator matrices to preserve every
lattice direction. -/
theorem preserves_of_solenoidal (R : MultiplierSymbol) (A B : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hform : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
      R.map k v = generatorMap A B k v)
    (hsol : HasSolenoidalOutput R) :
    PreservesLatticeDirections A ∧ PreservesLatticeDirections B := by
  have hgen : ∀ (k : LatticeVec), k ≠ 0 → ∀ v : RVec, TransverseR k v →
      Transverse k (generatorMap A B k (realToComplexVec v)) := by
    intro k hk v hv
    rw [← hform k hk _ (transverse_complexification hv)]
    exact hsol k hk _ (transverse_complexification hv)
  constructor
  · intro k hk
    apply parallel_of_orthogonal_to_transverse _ _ (latticeToReal_ne_zero hk)
    intro v hv
    rw [real_symmetric_mulVec_dot A hA, Vec3.dot_comm]
    exact (solenoidal_real_split A B k v (hgen k hk v hv)).1
  · intro k hk
    have hkne := latticeToReal_ne_zero hk
    have hkk : Vec3.dot (latticeToReal k) (latticeToReal k) ≠ 0 :=
      ne_of_gt (real_dot_self_pos _ hkne)
    apply parallel_of_orthogonal_to_transverse _ _ hkne
    intro w hw
    rw [real_symmetric_mulVec_dot B hB, Vec3.dot_comm]
    set v : RVec :=
      (-(Vec3.dot (latticeToReal k) (latticeToReal k))⁻¹) •
        Vec3.cross (latticeToReal k) w with hvdef
    have hvT : TransverseR k v := by
      unfold TransverseR
      rw [hvdef, Vec3.dot_smul_right, transverse_cross]
      ring
    have hcross : Vec3.cross (latticeToReal k) v = w := by
      rw [hvdef, cross_smul_right, cross_cross_transverse _ _ hw, smul_smul]
      field_simp
      simp
    have hsplit := (solenoidal_real_split A B k v (hgen k hk v hvT)).2
    unfold crossAnticommutator at hsplit
    rw [Vec3.dot_add_right, Vec3.dot_cross_self_left, hcross, add_zero] at hsplit
    exact hsplit

theorem scalar_matrix_symm (a : ℝ) :
    (a • (1 : RMatrix)).transpose = a • (1 : RMatrix) := by
  simp

theorem generatorMap_scalar (a b : ℝ) (k : LatticeVec) (v : CVec) :
    generatorMap (a • (1 : RMatrix)) (b • (1 : RMatrix)) k v =
      (a : ℂ) • v + ((2 * b : ℝ) : ℂ) • curlSymbol k v := by
  rw [generatorMap_apply]
  funext i
  fin_cases i <;>
    simp [complexifyMatrix, Matrix.mulVec, dotProduct, curlSymbol, Vec3.cross,
      latticeToComplex, Matrix.one_apply, Fin.sum_univ_succ] <;> ring

/-- Energy and helicity: the solenoidal conclusion `R = c I + d curl`. -/
def HasScalarForm (R : MultiplierSymbol) : Prop :=
  ∃ c d : ℝ, ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
    R.map k v = (c : ℂ) • v + (d : ℂ) • curlSymbol k v

/-- **Corollary B (solenoidal rigidity).**  If the multiplier additionally
preserves divergence-free fields, the twelve-parameter family collapses to two
real constants: universal cancellation holds exactly for `R = c I + d curl`.
In particular the cubic identity forces every nonzero-mode block to be
Hermitian, and energy and helicity are the only possibilities. -/
theorem corollaryB (R : MultiplierSymbol) (hsol : HasSolenoidalOutput R) :
    UniversalCancellation R ↔ HasScalarForm R := by
  constructor
  · intro hR
    obtain ⟨A, B, hA, hB, hform⟩ := universalCancellation_hasGeneratorForm R hR
    obtain ⟨hPA, hPB⟩ := preserves_of_solenoidal R A B hA hB hform hsol
    obtain ⟨a, ha⟩ := scalarity_from_lattice_directions A hPA
    obtain ⟨b, hb⟩ := scalarity_from_lattice_directions B hPB
    refine ⟨a, 2 * b, ?_⟩
    intro k hk v hv
    rw [hform k hk v hv, ha, hb, generatorMap_scalar]
  · rintro ⟨c, d, hcd⟩
    apply hasGeneratorForm_universalCancellation
    refine ⟨c • (1 : RMatrix), (d / 2) • (1 : RMatrix),
      scalar_matrix_symm c, scalar_matrix_symm (d / 2), ?_⟩
    intro k hk v hv
    rw [hcd k hk v hv, generatorMap_scalar]
    norm_num
    congr 1
    ring

end FourierMultiplierRigidity
