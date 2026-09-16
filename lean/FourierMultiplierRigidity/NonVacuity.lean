import FourierMultiplierRigidity.CorollaryB

/-!
# Non-vacuity of the classification

A formalization can be true but empty.  Two failure modes matter here:

* if `TrigField` admitted only trivial fields, `UniversalCancellation` would
  hold for every symbol and `theoremA` would merely be asserting that every
  symbol is a generator;
* if `HasGeneratorForm` held for every symbol, the iff would carry no
  information either.

This file rules both out with a single witness.  `sqNormSymbol` is
`R (k) = ‖k‖² I`: reality-compatible, but quadratic in `k`, whereas every
generator `A + B C_k + C_k B` is affine in `k`.  The real part of the generator
form is the `k`-independent term `A v`, so comparing `k = e₀` with `k = 2 e₀`
on the same transverse vector forces `1 = 4`.  Hence `sqNormSymbol` is not a
generator — `sqNormSymbol_not_generator`, kernel-checked and independent of the
seed certificate.

Feeding that through `theoremA` gives `sqNormSymbol_not_universal`, and hence
`exists_nonvanishing_cubicForm`: some admissible trigonometric field has
nonzero cubic form.  So both sides of the classification are proper
restrictions, and both directions of the iff have content.
-/

namespace FourierMultiplierRigidity

/-- `R(k) = ‖k‖² I`.  Reality-compatible, but quadratic in `k`, whereas every
generator `A + B C_k + C_k B` is affine in `k`. -/
noncomputable def sqNormSymbol : MultiplierSymbol where
  map k := (((k 0 * k 0 + k 1 * k 1 + k 2 * k 2 : ℤ) : ℂ)) • LinearMap.id
  realityCompatible := by
    intro k v _
    funext i
    simp [conjVec, Pi.neg_apply]

theorem sqNormSymbol_not_generator : ¬ HasGeneratorForm sqNormSymbol := by
  rintro ⟨A, B, hA, hB, h⟩
  have key : ∀ n : ℤ, n ≠ 0 → (Matrix.mulVec A ![0, 1, 0]) 1 = ((n * n : ℤ) : ℝ) := by
    intro n hn
    have hk : (![n, 0, 0] : LatticeVec) ≠ 0 := by
      intro hc
      exact hn (by simpa using congrFun hc 0)
    have ht : Transverse (![n, 0, 0] : LatticeVec) (realToComplexVec ![0, 1, 0]) := by
      simp [Transverse, Vec3.dot, latticeToComplex, realToComplexVec]
    have hn2 := h ![n, 0, 0] hk _ ht
    rw [generatorMap_on_real] at hn2
    have hc := congrFun hn2 1
    have := congrArg Complex.re hc
    simpa [sqNormSymbol, realToComplexVec, Complex.add_re, Complex.mul_re] using this.symm
  have h1 := key 1 (by norm_num)
  have h2 := key 2 (by norm_num)
  rw [h1] at h2
  norm_num at h2

/-- Hence the classification is not vacuous: some reality-compatible symbol
fails universal cancellation, so `TrigField` really does supply witnesses. -/
theorem sqNormSymbol_not_universal : ¬ UniversalCancellation sqNormSymbol :=
  fun hU => sqNormSymbol_not_generator (theoremA sqNormSymbol |>.mp hU)

theorem exists_nonvanishing_cubicForm : ∃ w : TrigField, cubicForm sqNormSymbol w ≠ 0 := by
  by_contra hc
  exact sqNormSymbol_not_universal (fun w => not_not.mp (fun hw => hc ⟨w, hw⟩))

end FourierMultiplierRigidity
