import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import FourierMultiplierRigidity.SeedCertificate

/-!
# Fourier-multiplier rigidity for universal Euler convective cancellations

This file formalizes Theorem A from
`research/01-fourier-multiplier-rigidity/proof.md`.

The development is intentionally kept separate from the exact Python
certificates: no fact is imported from them.

Two different levels of trust are used, and they must not be conflated:

* the analytic development — the generator algebra, triadwise sufficiency, the
  raw-recipient lemmas and the lattice propagation theorem — is checked by
  Lean's kernel, and depends only on `propext`, `Classical.choice` and
  `Quot.sound`;
* the finite rank and inverse certificates for the thirteen-mode unit cube are
  discharged by `native_decide`, which evaluates compiled code instead of
  reducing in the kernel.  Those results therefore additionally trust the Lean
  compiler and its runtime.

`lean/README.md` records which theorems fall on which side, together with the
`#print axioms` invocations that reproduce the split.  The final assembly of Theorem A is in `TheoremA.lean`; its semantic seed
bridge is in `SeedBridge.lean`.
-/

namespace FourierMultiplierRigidity

open scoped ComplexConjugate

abbrev RVec := Fin 3 → ℝ
abbrev CVec := Fin 3 → ℂ
abbrev LatticeVec := Fin 3 → ℤ
abbrev RMatrix := Matrix (Fin 3) (Fin 3) ℝ
abbrev CMatrix := Matrix (Fin 3) (Fin 3) ℂ

namespace Vec3

/-- The complex-bilinear dot product used in the Fourier pairing. -/
def dot {R : Type*} [CommRing R] (u v : Fin 3 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The coordinate cross product in three dimensions. -/
def cross {R : Type*} [CommRing R] (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

@[simp] theorem cross_zero_left {R : Type*} [CommRing R] (v : Fin 3 → R) :
    cross 0 v = 0 := by
  funext i
  fin_cases i <;> simp [cross]

@[simp] theorem cross_zero_right {R : Type*} [CommRing R] (v : Fin 3 → R) :
    cross v 0 = 0 := by
  funext i
  fin_cases i <;> simp [cross]

theorem cross_self {R : Type*} [CommRing R] (v : Fin 3 → R) :
    cross v v = 0 := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

@[simp] theorem cross_smul_left {R : Type*} [CommRing R]
    (c : R) (u v : Fin 3 → R) : cross (c • u) v = c • cross u v := by
  funext i
  fin_cases i <;> simp [cross] <;> ring

theorem dot_cross_self_left {R : Type*} [CommRing R] (u v : Fin 3 → R) :
    dot u (cross u v) = 0 := by
  change u 0 * (u 1 * v 2 - u 2 * v 1) +
      u 1 * (u 2 * v 0 - u 0 * v 2) +
      u 2 * (u 0 * v 1 - u 1 * v 0) = 0
  ring

theorem dot_comm {R : Type*} [CommRing R] (u v : Fin 3 → R) :
    dot u v = dot v u := by
  simp [dot]
  ring

@[simp] theorem dot_add_right {R : Type*} [CommRing R]
    (u v w : Fin 3 → R) : dot u (v + w) = dot u v + dot u w := by
  simp [dot]
  ring

@[simp] theorem dot_add_left {R : Type*} [CommRing R]
    (u v w : Fin 3 → R) : dot (u + v) w = dot u w + dot v w := by
  simp [dot]
  ring

@[simp] theorem dot_sub_left {R : Type*} [CommRing R]
    (u v w : Fin 3 → R) : dot (u - v) w = dot u w - dot v w := by
  simp [dot]
  ring

@[simp] theorem dot_smul_right {R : Type*} [CommRing R]
    (a : R) (u v : Fin 3 → R) : dot u (a • v) = a * dot u v := by
  simp [dot]
  ring

@[simp] theorem dot_smul_left {R : Type*} [CommRing R]
    (a : R) (u v : Fin 3 → R) : dot (a • u) v = a * dot u v := by
  simp [dot]
  ring

@[simp] theorem dot_sum_right {R ι : Type*} [CommRing R]
    (s : Finset ι) (u : Fin 3 → R) (f : ι → Fin 3 → R) :
    dot u (∑ x ∈ s, f x) = ∑ x ∈ s, dot u (f x) := by
  simp [dot, Finset.mul_sum, Finset.sum_add_distrib]

end Vec3

/-- Embed a lattice wavevector into a real vector. -/
def latticeToReal (k : LatticeVec) : RVec := fun i ↦ (k i : ℝ)

/-- Embed a lattice wavevector into a complex vector. -/
def latticeToComplex (k : LatticeVec) : CVec := fun i ↦ (k i : ℂ)

/-- The Fourier symbol `C_k v = i (k × v)` of curl. -/
def curlSymbol (k : LatticeVec) (v : CVec) : CVec :=
  Complex.I • Vec3.cross (latticeToComplex k) v

/-- A vector lies in the complex transverse fiber at `k`. -/
def Transverse (k : LatticeVec) (v : CVec) : Prop :=
  Vec3.dot (latticeToComplex k) v = 0

@[simp] theorem transverse_zero (k : LatticeVec) : Transverse k 0 := by
  simp [Transverse, Vec3.dot]

theorem transverse_add {k : LatticeVec} {u v : CVec}
    (hu : Transverse k u) (hv : Transverse k v) : Transverse k (u + v) := by
  unfold Transverse at hu hv ⊢
  rw [Vec3.dot_add_right, hu, hv]
  simp

theorem transverse_smul {k : LatticeVec} {v : CVec} (c : ℂ)
    (hv : Transverse k v) : Transverse k (c • v) := by
  unfold Transverse at hv ⊢
  rw [Vec3.dot_smul_right, hv]
  simp

/-- Two real vectors are parallel. This includes the zero vector. -/
def Parallel (u v : RVec) : Prop := ∃ c : ℝ, u = c • v

/-- A matrix maps every nonzero lattice direction to its own span. -/
def PreservesLatticeDirections (L : RMatrix) : Prop :=
  ∀ k : LatticeVec, k ≠ 0 →
    Parallel (Matrix.mulVec L (latticeToReal k)) (latticeToReal k)

/-- Lemma 3.2: a real matrix preserving every lattice direction is scalar.

The manuscript assumes symmetry, but the directional hypothesis alone already
forces the conclusion, so this kernel-checked statement is slightly stronger.
-/
theorem scalarity_from_lattice_directions (L : RMatrix)
    (hL : PreservesLatticeDirections L) :
    ∃ c : ℝ, L = c • (1 : RMatrix) := by
  let e₀ : LatticeVec := ![1, 0, 0]
  let e₁ : LatticeVec := ![0, 1, 0]
  let e₂ : LatticeVec := ![0, 0, 1]
  let e₀₁ : LatticeVec := ![1, 1, 0]
  let e₀₂ : LatticeVec := ![1, 0, 1]
  obtain ⟨c₀, hc₀⟩ := hL e₀ (by simp [e₀])
  obtain ⟨c₁, hc₁⟩ := hL e₁ (by simp [e₁])
  obtain ⟨c₂, hc₂⟩ := hL e₂ (by simp [e₂])
  obtain ⟨c₀₁, hc₀₁⟩ := hL e₀₁ (by simp [e₀₁])
  obtain ⟨c₀₂, hc₀₂⟩ := hL e₀₂ (by simp [e₀₂])
  have h₀₀ := congrFun hc₀ 0
  have h₁₀ := congrFun hc₀ 1
  have h₂₀ := congrFun hc₀ 2
  have h₀₁ := congrFun hc₁ 0
  have h₁₁ := congrFun hc₁ 1
  have h₂₁ := congrFun hc₁ 2
  have h₀₂ := congrFun hc₂ 0
  have h₁₂ := congrFun hc₂ 1
  have h₂₂ := congrFun hc₂ 2
  have h₀₀₁ := congrFun hc₀₁ 0
  have h₁₀₁ := congrFun hc₀₁ 1
  have h₀₀₂ := congrFun hc₀₂ 0
  have h₂₀₂ := congrFun hc₀₂ 2
  simp [Matrix.mulVec, dotProduct, latticeToReal, e₀, Fin.sum_univ_succ] at h₀₀ h₁₀ h₂₀
  simp [Matrix.mulVec, dotProduct, latticeToReal, e₁, Fin.sum_univ_succ] at h₀₁ h₁₁ h₂₁
  simp [Matrix.mulVec, dotProduct, latticeToReal, e₂, Fin.sum_univ_succ] at h₀₂ h₁₂ h₂₂
  simp [Matrix.mulVec, dotProduct, latticeToReal, e₀₁, Fin.sum_univ_succ] at h₀₀₁ h₁₀₁
  simp [Matrix.mulVec, dotProduct, latticeToReal, e₀₂, Fin.sum_univ_succ] at h₀₀₂ h₂₀₂
  refine ⟨c₀, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- A real vector lies in the transverse plane at a lattice mode. -/
def TransverseR (k : LatticeVec) (v : RVec) : Prop :=
  Vec3.dot (latticeToReal k) v = 0

/-- The real part of the first-order generator after removing its factor `i`. -/
def crossAnticommutator (B : RMatrix) (k : LatticeVec) (v : RVec) : RVec :=
  Matrix.mulVec B (Vec3.cross (latticeToReal k) v) +
    Vec3.cross (latticeToReal k) (Matrix.mulVec B v)

/-- Proposition 3.1 after adding and subtracting the equations at `k` and
`-k`: the zero-order and first-order symmetric generators have trivial
intersection on all transverse lattice fibers. -/
theorem uniqueness_of_split_generator (A B : RMatrix)
    (_hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : RVec), TransverseR k v →
      Matrix.mulVec A v = 0 ∧ crossAnticommutator B k v = 0) :
    A = 0 ∧ B = 0 := by
  let e₀ : LatticeVec := ![1, 0, 0]
  let e₁ : LatticeVec := ![0, 1, 0]
  let e₂ : LatticeVec := ![0, 0, 1]
  let v₀ : RVec := ![1, 0, 0]
  let v₁ : RVec := ![0, 1, 0]
  let v₂ : RVec := ![0, 0, 1]
  have he₀ : e₀ ≠ 0 := by simp [e₀]
  have he₁ : e₁ ≠ 0 := by simp [e₁]
  have he₂ : e₂ ≠ 0 := by simp [e₂]
  have ht₀₁ : TransverseR e₀ v₁ := by simp [TransverseR, Vec3.dot, latticeToReal, e₀, v₁]
  have ht₀₂ : TransverseR e₀ v₂ := by simp [TransverseR, Vec3.dot, latticeToReal, e₀, v₂]
  have ht₁₀ : TransverseR e₁ v₀ := by simp [TransverseR, Vec3.dot, latticeToReal, e₁, v₀]
  have ht₂₀ : TransverseR e₂ v₀ := by simp [TransverseR, Vec3.dot, latticeToReal, e₂, v₀]
  obtain ⟨ha₀₁, hb₀₁⟩ := h e₀ he₀ v₁ ht₀₁
  obtain ⟨ha₀₂, hb₀₂⟩ := h e₀ he₀ v₂ ht₀₂
  obtain ⟨ha₁₀, hb₁₀⟩ := h e₁ he₁ v₀ ht₁₀
  obtain ⟨_, hb₂₀⟩ := h e₂ he₂ v₀ ht₂₀
  have ha₀₁₀ := congrFun ha₀₁ 0
  have ha₀₁₁ := congrFun ha₀₁ 1
  have ha₀₁₂ := congrFun ha₀₁ 2
  have ha₀₂₀ := congrFun ha₀₂ 0
  have ha₀₂₁ := congrFun ha₀₂ 1
  have ha₀₂₂ := congrFun ha₀₂ 2
  have ha₁₀₀ := congrFun ha₁₀ 0
  have ha₁₀₁ := congrFun ha₁₀ 1
  have ha₁₀₂ := congrFun ha₁₀ 2
  simp [Matrix.mulVec, dotProduct, v₀, v₁, v₂, Fin.sum_univ_succ] at ha₀₁₀ ha₀₁₁ ha₀₁₂ ha₀₂₀ ha₀₂₁ ha₀₂₂ ha₁₀₀ ha₁₀₁ ha₁₀₂
  have hAzero : A = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> assumption
  have hb₀₁₀ := congrFun hb₀₁ 0
  have hb₀₁₁ := congrFun hb₀₁ 1
  have hb₀₁₂ := congrFun hb₀₁ 2
  have hb₀₂₀ := congrFun hb₀₂ 0
  have hb₀₂₁ := congrFun hb₀₂ 1
  have hb₀₂₂ := congrFun hb₀₂ 2
  have hb₁₀₀ := congrFun hb₁₀ 0
  have hb₁₀₁ := congrFun hb₁₀ 1
  have hb₁₀₂ := congrFun hb₁₀ 2
  have hb₂₀₀ := congrFun hb₂₀ 0
  have hb₂₀₁ := congrFun hb₂₀ 1
  have hb₂₀₂ := congrFun hb₂₀ 2
  simp [crossAnticommutator, Vec3.cross, Matrix.mulVec, dotProduct, latticeToReal,
    e₀, e₁, e₂, v₀, v₁, v₂, Fin.sum_univ_succ] at hb₀₁₀ hb₀₁₁ hb₀₁₂ hb₀₂₀ hb₀₂₁ hb₀₂₂ hb₁₀₀ hb₁₀₁ hb₁₀₂ hb₂₀₀ hb₂₀₁ hb₂₀₂
  have hs₀₁ : B 0 1 = B 1 0 := by
    have := congrFun (congrFun hB 0) 1
    simpa using this.symm
  have hs₀₂ : B 0 2 = B 2 0 := by
    have := congrFun (congrFun hB 0) 2
    simpa using this.symm
  have hs₁₂ : B 1 2 = B 2 1 := by
    have := congrFun (congrFun hB 1) 2
    simpa using this.symm
  have hBzero : B = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  exact ⟨hAzero, hBzero⟩

/-! ## Fourier-side formulation of trigonometric polynomial fields -/

/-- Componentwise complex conjugation. -/
def conjVec (v : CVec) : CVec := fun i ↦ conj (v i)

@[simp] theorem conjVec_zero : conjVec 0 = 0 := by
  funext i
  simp [conjVec]

@[simp] theorem conjVec_add (u v : CVec) : conjVec (u + v) = conjVec u + conjVec v := by
  funext i
  simp [conjVec]

@[simp] theorem conjVec_sub (u v : CVec) : conjVec (u - v) = conjVec u - conjVec v := by
  funext i
  simp [conjVec]

@[simp] theorem conjVec_conjVec (v : CVec) : conjVec (conjVec v) = v := by
  funext i
  simp [conjVec]

@[simp] theorem conjVec_eq_zero_iff (v : CVec) : conjVec v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg conjVec h
    simpa using this
  · rintro rfl
    exact conjVec_zero

theorem transverse_neg_conj {k : LatticeVec} {v : CVec}
    (hv : Transverse k v) : Transverse (-k) (conjVec v) := by
  have hc := congrArg conj hv
  simp [Transverse, Vec3.dot, latticeToComplex, conjVec] at hc ⊢
  linear_combination -hc

/-- A real, mean-zero, divergence-free trigonometric polynomial, represented
by its finitely supported Fourier coefficients. -/
structure TrigField where
  coeff : LatticeVec →₀ CVec
  meanZero : coeff 0 = 0
  divergenceFree : ∀ k, Transverse k (coeff k)
  reality : ∀ k, coeff (-k) = conjVec (coeff k)

theorem neg_ne_zero_of_ne_zero {k : LatticeVec} (hk : k ≠ 0) : -k ≠ 0 := by
  simpa using hk

theorem ne_neg_self_of_ne_zero {k : LatticeVec} (hk : k ≠ 0) : k ≠ -k := by
  intro h
  apply hk
  funext i
  have hi := congrFun h i
  simp at hi
  have hki : k i = 0 := by omega
  simpa using hki

noncomputable def realPairCoeff (k : LatticeVec) (a : CVec) : LatticeVec →₀ CVec :=
  Finsupp.single k a + Finsupp.single (-k) (conjVec a)

theorem realPairCoeff_apply (k j : LatticeVec) (a : CVec) (hk : k ≠ 0) :
    realPairCoeff k a j = if j = k then a else if j = -k then conjVec a else 0 := by
  classical
  by_cases hjk : j = k
  · subst j
    simp [realPairCoeff, ne_neg_self_of_ne_zero hk]
  · by_cases hjn : j = -k
    · subst j
      simp [realPairCoeff, hjk]
    · simp [realPairCoeff, hjk, hjn]

theorem realPairCoeff_sum {N : Type*} [AddCommMonoid N]
    (k : LatticeVec) (a : CVec) (f : LatticeVec → CVec → N)
    (hzero : ∀ j, f j 0 = 0)
    (hadd : ∀ j u v, f j (u + v) = f j u + f j v) :
    (realPairCoeff k a).sum f = f k a + f (-k) (conjVec a) := by
  classical
  rw [realPairCoeff, Finsupp.sum_add_index' hzero hadd,
    Finsupp.sum_single_index (hzero k),
    Finsupp.sum_single_index (hzero (-k))]

/-- The real Fourier field supported at one signed mode pair. -/
noncomputable def realPairField (k : LatticeVec) (a : CVec)
    (hk : k ≠ 0) (ha : Transverse k a) : TrigField where
  coeff := realPairCoeff k a
  meanZero := by
    rw [realPairCoeff_apply k 0 a hk]
    simp [hk, Ne.symm hk]
  divergenceFree := by
    intro j
    rw [realPairCoeff_apply k j a hk]
    split_ifs with hjk hjn
    · simpa [hjk] using ha
    · subst j
      exact transverse_neg_conj ha
    · exact transverse_zero j
  reality := by
    intro j
    rw [realPairCoeff_apply k (-j) a hk, realPairCoeff_apply k j a hk]
    by_cases hjk : j = k
    · subst j
      have hneg : -k ≠ k := by
        exact fun h ↦ ne_neg_self_of_ne_zero hk h.symm
      simp [hneg]
    · by_cases hjn : j = -k
      · subst j
        simp [hjk]
      · have hnegk : -j ≠ k := by
          intro h
          apply hjn
          rw [← h]
          simp
        have hnegneg : -j ≠ -k := by
          intro h
          apply hjk
          simpa using congrArg Neg.neg h
        simp [hjk, hjn, hnegk, hnegneg]

noncomputable def TrigField.add (x y : TrigField) : TrigField where
  coeff := x.coeff + y.coeff
  meanZero := by rw [Finsupp.add_apply, x.meanZero, y.meanZero]; simp
  divergenceFree := by
    intro k
    rw [Finsupp.add_apply]
    exact transverse_add (x.divergenceFree k) (y.divergenceFree k)
  reality := by
    intro k
    rw [Finsupp.add_apply, Finsupp.add_apply, x.reality k, y.reality k, conjVec_add]

noncomputable instance : Add TrigField := ⟨TrigField.add⟩

@[simp] theorem TrigField.coeff_add (x y : TrigField) (k : LatticeVec) :
    (x + y).coeff k = x.coeff k + y.coeff k := rfl

/-- A (not necessarily solenoidal-output) complex-linear multiplier symbol. -/
structure MultiplierSymbol where
  map : LatticeVec → CVec →ₗ[ℂ] CVec
  realityCompatible : ∀ (k : LatticeVec) (v : CVec), Transverse k v →
    map (-k) (conjVec v) = conjVec (map k v)

/-- The Fourier coefficient of `(w · ∇)w` at mode `k`. The two sums are
finite because `w` is a trigonometric polynomial. -/
noncomputable def convectiveCoeff (w : TrigField) (k : LatticeVec) : CVec :=
  Complex.I • w.coeff.sum fun p up ↦
    w.coeff.sum fun q uq ↦
      if p + q = k then Vec3.dot (latticeToComplex q) up • uq else 0

/-- The cubic Fourier form corresponding to
`⟨Rw, (w · ∇)w⟩`. Normalized Haar integration selects opposite
recipient modes, hence the argument `-k` below. -/
noncomputable def cubicForm (R : MultiplierSymbol) (w : TrigField) : ℂ :=
  w.coeff.sum fun k uk ↦ Vec3.dot (R.map k uk) (convectiveCoeff w (-k))

/-- Universal Euler convective cancellation on real mean-zero
divergence-free trigonometric polynomials. -/
def UniversalCancellation (R : MultiplierSymbol) : Prop :=
  ∀ w : TrigField, cubicForm R w = 0

/-- The ordered trilinear form whose diagonal is the cubic cancellation. -/
def triCoeff (R : MultiplierSymbol) (p q r : LatticeVec)
    (xp yq zr : CVec) : ℂ :=
  if p + q + r = 0 then
    Complex.I * Vec3.dot (R.map p xp)
      (Vec3.dot yq (latticeToComplex r) • zr)
  else 0

noncomputable def cubicTrilinear (R : MultiplierSymbol)
    (x y z : TrigField) : ℂ :=
  x.coeff.sum fun p xp ↦
    y.coeff.sum fun q yq ↦
      z.coeff.sum fun r zr ↦ triCoeff R p q r xp yq zr

@[simp] theorem triCoeff_zero_left (R : MultiplierSymbol) (p q r : LatticeVec)
    (y z : CVec) : triCoeff R p q r 0 y z = 0 := by
  simp [triCoeff, Vec3.dot]

@[simp] theorem triCoeff_zero_middle (R : MultiplierSymbol) (p q r : LatticeVec)
    (x z : CVec) : triCoeff R p q r x 0 z = 0 := by
  simp [triCoeff, Vec3.dot]

@[simp] theorem triCoeff_zero_right (R : MultiplierSymbol) (p q r : LatticeVec)
    (x y : CVec) : triCoeff R p q r x y 0 = 0 := by
  simp [triCoeff, Vec3.dot]

theorem triCoeff_add_left (R : MultiplierSymbol) (p q r : LatticeVec)
    (x x' y z : CVec) :
    triCoeff R p q r (x + x') y z =
      triCoeff R p q r x y z + triCoeff R p q r x' y z := by
  by_cases h : p + q + r = 0 <;>
    simp [triCoeff, h, (R.map p).map_add, Vec3.dot_add_left] <;> ring

theorem triCoeff_add_middle (R : MultiplierSymbol) (p q r : LatticeVec)
    (x y y' z : CVec) :
    triCoeff R p q r x (y + y') z =
      triCoeff R p q r x y z + triCoeff R p q r x y' z := by
  by_cases h : p + q + r = 0 <;>
    simp [triCoeff, h, Vec3.dot_add_left, add_smul, Vec3.dot_add_right] <;> ring

theorem triCoeff_add_right (R : MultiplierSymbol) (p q r : LatticeVec)
    (x y z z' : CVec) :
    triCoeff R p q r x y (z + z') =
      triCoeff R p q r x y z + triCoeff R p q r x y z' := by
  by_cases h : p + q + r = 0 <;>
    simp [triCoeff, h, smul_add, Vec3.dot_add_right] <;> ring

/-- A multiplier has solenoidal output on every nonzero transverse fiber. -/
def HasSolenoidalOutput (R : MultiplierSymbol) : Prop :=
  ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
    Transverse k (R.map k v)

/-! ## The classified generator family -/

/-- Entrywise extension of a real matrix to the complex numbers. -/
def complexifyMatrix (A : RMatrix) : CMatrix := fun i j ↦ (A i j : ℂ)

@[simp] theorem complexifyMatrix_zero : complexifyMatrix 0 = 0 := by
  rfl

/-- Componentwise embedding of a real vector into a complex vector. -/
def realToComplexVec (v : RVec) : CVec := fun i ↦ (v i : ℂ)

@[simp] theorem realToComplexVec_zero : realToComplexVec 0 = 0 := by
  rfl

@[simp] theorem realToComplexVec_add (u v : RVec) :
    realToComplexVec (u + v) = realToComplexVec u + realToComplexVec v := by
  funext i
  simp [realToComplexVec]

@[simp] theorem realToComplexVec_sub (u v : RVec) :
    realToComplexVec (u - v) = realToComplexVec u - realToComplexVec v := by
  funext i
  simp [realToComplexVec]

theorem complexify_mulVec (A : RMatrix) (v : RVec) :
    Matrix.mulVec (complexifyMatrix A) (realToComplexVec v) =
      realToComplexVec (Matrix.mulVec A v) := by
  funext i
  simp [Matrix.mulVec, dotProduct, complexifyMatrix, realToComplexVec,
    Fin.sum_univ_succ]

theorem complexify_mulVec_I_smul (A : RMatrix) (v : RVec) :
    Matrix.mulVec (complexifyMatrix A) (Complex.I • realToComplexVec v) =
      Complex.I • realToComplexVec (Matrix.mulVec A v) := by
  calc
    Matrix.mulVec (complexifyMatrix A) (Complex.I • realToComplexVec v) =
        Complex.I • Matrix.mulVec (complexifyMatrix A) (realToComplexVec v) :=
      (complexifyMatrix A).mulVecLin.map_smul Complex.I (realToComplexVec v)
    _ = Complex.I • realToComplexVec (Matrix.mulVec A v) := by
      rw [complexify_mulVec]

theorem cross_complexification (k : LatticeVec) (v : RVec) :
    Vec3.cross (latticeToComplex k) (realToComplexVec v) =
      realToComplexVec (Vec3.cross (latticeToReal k) v) := by
  funext i
  fin_cases i <;>
    simp [Vec3.cross, latticeToComplex, latticeToReal, realToComplexVec]

theorem transverse_complexification {k : LatticeVec} {v : RVec}
    (h : TransverseR k v) : Transverse k (realToComplexVec v) := by
  have hc := congrArg Complex.ofReal h
  simpa [TransverseR, Transverse, Vec3.dot, latticeToReal, latticeToComplex,
    realToComplexVec] using hc

/-- Curl as a complex-linear map on one Fourier fiber. -/
def curlLinear (k : LatticeVec) : CVec →ₗ[ℂ] CVec :=
  Complex.I • crossProduct (latticeToComplex k)

/-- The twelve-parameter family in formula (3.2):
`A + B C_k + C_k B`. -/
def generatorMap (A B : RMatrix) (k : LatticeVec) : CVec →ₗ[ℂ] CVec :=
  (complexifyMatrix A).mulVecLin +
    (complexifyMatrix B).mulVecLin.comp (curlLinear k) +
    (curlLinear k).comp (complexifyMatrix B).mulVecLin

@[simp] theorem generatorMap_apply (A B : RMatrix) (k : LatticeVec) (v : CVec) :
    generatorMap A B k v =
      Matrix.mulVec (complexifyMatrix A) v +
      Matrix.mulVec (complexifyMatrix B) (curlSymbol k v) +
      curlSymbol k (Matrix.mulVec (complexifyMatrix B) v) := by
  rfl

theorem generatorMap_on_real (A B : RMatrix) (k : LatticeVec) (v : RVec) :
    generatorMap A B k (realToComplexVec v) =
      realToComplexVec (Matrix.mulVec A v) +
        Complex.I • realToComplexVec (crossAnticommutator B k v) := by
  rw [generatorMap_apply, complexify_mulVec]
  simp only [curlSymbol, cross_complexification, complexify_mulVec,
    complexify_mulVec_I_smul, crossAnticommutator, realToComplexVec_add, smul_add]
  rw [add_assoc]

theorem generatorMap_real_eq_zero_iff (A B : RMatrix) (k : LatticeVec) (v : RVec) :
    generatorMap A B k (realToComplexVec v) = 0 ↔
      Matrix.mulVec A v = 0 ∧ crossAnticommutator B k v = 0 := by
  rw [generatorMap_on_real]
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrFun h i
      apply_fun Complex.re at hi
      simpa [realToComplexVec] using hi
    · funext i
      have hi := congrFun h i
      apply_fun Complex.im at hi
      simpa [realToComplexVec] using hi
  · rintro ⟨hA, hB⟩
    rw [hA, hB]
    funext i
    simp

theorem generatorMap_sub (A A' B B' : RMatrix) (k : LatticeVec) :
    generatorMap (A - A') (B - B') k = generatorMap A B k - generatorMap A' B' k := by
  have hc (M N : RMatrix) :
      complexifyMatrix (M - N) = complexifyMatrix M - complexifyMatrix N := by
    ext i j
    simp [complexifyMatrix]
  have hm (M N : CMatrix) :
      (M - N).mulVecLin = M.mulVecLin - N.mulVecLin := by
    apply LinearMap.ext
    intro v
    funext i
    simp [Matrix.mulVec, dotProduct]
  apply LinearMap.ext
  intro v
  simp only [generatorMap, hc, hm, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply]
  rw [(curlLinear k).map_sub]
  abel

/-- The uniqueness clause in Theorem A, now stated directly for the complex
generator maps on all nonzero transverse fibers. -/
theorem generator_parameters_unique (A B A' B' : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hA' : A'.transpose = A') (hB' : B'.transpose = B')
    (h : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
      generatorMap A B k v = generatorMap A' B' k v) :
    A = A' ∧ B = B' := by
  have hsA : (A - A').transpose = A - A' := by
    simp [hA, hA']
  have hsB : (B - B').transpose = B - B' := by
    simp [hB, hB']
  have hsplit : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : RVec), TransverseR k v →
      Matrix.mulVec (A - A') v = 0 ∧ crossAnticommutator (B - B') k v = 0 := by
    intro k hk v hv
    rw [← generatorMap_real_eq_zero_iff]
    rw [generatorMap_sub]
    exact sub_eq_zero.mpr (h k hk (realToComplexVec v) (transverse_complexification hv))
  obtain ⟨hzeroA, hzeroB⟩ :=
    uniqueness_of_split_generator (A - A') (B - B') hsA hsB hsplit
  exact ⟨sub_eq_zero.mp hzeroA, sub_eq_zero.mp hzeroB⟩

theorem complex_matrix_mulVec_conj (A : RMatrix) (v : CVec) :
    Matrix.mulVec (complexifyMatrix A) (conjVec v) =
      conjVec (Matrix.mulVec (complexifyMatrix A) v) := by
  funext i
  simp [Matrix.mulVec, dotProduct, complexifyMatrix, conjVec, Fin.sum_univ_succ]

theorem curlSymbol_reality (k : LatticeVec) (v : CVec) :
    curlSymbol (-k) (conjVec v) = conjVec (curlSymbol k v) := by
  funext i
  fin_cases i <;>
    simp [curlSymbol, Vec3.cross, latticeToComplex, conjVec] <;> ring

/-- Every real pair `A,B` defines a reality-compatible multiplier symbol. -/
noncomputable def generatorSymbol (A B : RMatrix) : MultiplierSymbol where
  map := generatorMap A B
  realityCompatible := by
    intro k v _hv
    rw [generatorMap_apply, generatorMap_apply]
    rw [complex_matrix_mulVec_conj, curlSymbol_reality,
      complex_matrix_mulVec_conj, complex_matrix_mulVec_conj, curlSymbol_reality]
    simp

/-- Subtract a classified generator from an arbitrary multiplier. -/
noncomputable def differenceSymbol (R : MultiplierSymbol) (A B : RMatrix) :
    MultiplierSymbol where
  map k := R.map k - generatorMap A B k
  realityCompatible := by
    intro k v hv
    have hg : generatorMap A B (-k) (conjVec v) =
        conjVec (generatorMap A B k v) :=
      (generatorSymbol A B).realityCompatible k v hv
    simp only [LinearMap.sub_apply]
    rw [R.realityCompatible k v hv, hg, conjVec_sub]

/-! ## Triadwise sufficiency -/

/-- The symmetrized convective recipient produced at the `p`-mode by the
other two members `q,r` of a triad. -/
def rawRecipient (q r : LatticeVec) (u v : CVec) : CVec :=
  Vec3.dot u (latticeToComplex r) • v +
    Vec3.dot v (latticeToComplex q) • u

/-- The bracket inside the complex triad coefficient of Lemma 5.1. -/
def triadBracket (R : LatticeVec → CVec →ₗ[ℂ] CVec)
    (p q r : LatticeVec) (a u v : CVec) : ℂ :=
  Vec3.dot (R p a) (rawRecipient q r u v) +
  Vec3.dot (R q u) (rawRecipient r p v a) +
  Vec3.dot (R r v) (rawRecipient p q a u)

theorem complex_symmetric_mulVec_dot (A : RMatrix) (hA : A.transpose = A)
    (u v : CVec) :
    Vec3.dot (Matrix.mulVec (complexifyMatrix A) u) v =
      Vec3.dot (Matrix.mulVec (complexifyMatrix A) v) u := by
  have h₀₁ : A 0 1 = A 1 0 := by
    have := congrFun (congrFun hA 0) 1
    simpa using this.symm
  have h₀₂ : A 0 2 = A 2 0 := by
    have := congrFun (congrFun hA 0) 2
    simpa using this.symm
  have h₁₂ : A 1 2 = A 2 1 := by
    have := congrFun (congrFun hA 1) 2
    simpa using this.symm
  simp [Vec3.dot, Matrix.mulVec, dotProduct, complexifyMatrix, Fin.sum_univ_succ]
  rw [h₀₁, h₀₂, h₁₂]
  ring

theorem latticeToComplex_add (p q : LatticeVec) :
    latticeToComplex (p + q) = latticeToComplex p + latticeToComplex q := by
  funext i
  simp [latticeToComplex]

theorem latticeToComplex_eq_zero {p q r : LatticeVec} (h : p + q + r = 0) :
    latticeToComplex p + latticeToComplex q + latticeToComplex r = 0 := by
  funext i
  have hi := congrFun h i
  simp [latticeToComplex] at hi ⊢
  exact_mod_cast hi

/-- Formula (4.1) at one Fourier triad: every constant real symmetric
zero-order multiplier has zero triad bracket. -/
theorem symmetric_zero_order_triad_cancel (A : RMatrix) (hA : A.transpose = A)
    (p q r : LatticeVec) (a u v : CVec)
    (hpqr : p + q + r = 0)
    (ha : Transverse p a) (hu : Transverse q u) (hv : Transverse r v) :
    triadBracket (fun _ ↦ (complexifyMatrix A).mulVecLin) p q r a u v = 0 := by
  have hfreq := latticeToComplex_eq_zero hpqr
  have hav := congrArg (Vec3.dot a) hfreq
  have huv := congrArg (Vec3.dot u) hfreq
  have hvv := congrArg (Vec3.dot v) hfreq
  have hap : Vec3.dot a (latticeToComplex p) = 0 := by
    rw [Vec3.dot_comm]
    exact ha
  have huq : Vec3.dot u (latticeToComplex q) = 0 := by
    rw [Vec3.dot_comm]
    exact hu
  have hvr : Vec3.dot v (latticeToComplex r) = 0 := by
    rw [Vec3.dot_comm]
    exact hv
  have ha' : Vec3.dot a (latticeToComplex q) +
      Vec3.dot a (latticeToComplex r) = 0 := by
    simp only [Vec3.dot_add_right] at hav
    rw [hap] at hav
    simpa [Vec3.dot] using hav
  have hu' : Vec3.dot u (latticeToComplex p) +
      Vec3.dot u (latticeToComplex r) = 0 := by
    simp only [Vec3.dot_add_right] at huv
    rw [huq] at huv
    simpa [Vec3.dot] using huv
  have hv' : Vec3.dot v (latticeToComplex p) +
      Vec3.dot v (latticeToComplex q) = 0 := by
    simp only [Vec3.dot_add_right] at hvv
    rw [hvr] at hvv
    simpa [Vec3.dot] using hvv
  have haRev : Vec3.dot a (latticeToComplex r) +
      Vec3.dot a (latticeToComplex q) = 0 := by
    simpa [add_comm] using ha'
  have huRev : Vec3.dot u (latticeToComplex r) +
      Vec3.dot u (latticeToComplex p) = 0 := by
    simpa [add_comm] using hu'
  have hau := complex_symmetric_mulVec_dot A hA a u
  have havm := complex_symmetric_mulVec_dot A hA a v
  have huvM := complex_symmetric_mulVec_dot A hA u v
  simp only [triadBracket, rawRecipient, Matrix.mulVecLin_apply,
    Vec3.dot_add_right, Vec3.dot_smul_right]
  rw [hau, havm, huvM]
  calc
    _ = Vec3.dot (Matrix.mulVec (complexifyMatrix A) u) a *
          (Vec3.dot v (latticeToComplex p) + Vec3.dot v (latticeToComplex q)) +
        Vec3.dot (Matrix.mulVec (complexifyMatrix A) v) a *
          (Vec3.dot u (latticeToComplex r) + Vec3.dot u (latticeToComplex p)) +
        Vec3.dot (Matrix.mulVec (complexifyMatrix A) v) u *
          (Vec3.dot a (latticeToComplex r) + Vec3.dot a (latticeToComplex q)) := by ring
    _ = 0 := by rw [hv', huRev, haRev]; ring

/-- Formula (4.3) at one Fourier triad: every constant real symmetric
first-order multiplier `B C_k + C_k B` has zero triad bracket. -/
theorem symmetric_first_order_triad_cancel (B : RMatrix) (hB : B.transpose = B)
    (p q r : LatticeVec) (a u v : CVec)
    (hpqr : p + q + r = 0)
    (_ha : Transverse p a) (_hu : Transverse q u) (_hv : Transverse r v) :
    triadBracket (fun k ↦ generatorMap 0 B k) p q r a u v = 0 := by
  have hfreq := latticeToComplex_eq_zero hpqr
  have hf₀ := congrFun hfreq 0
  have hf₁ := congrFun hfreq 1
  have hf₂ := congrFun hfreq 2
  have hs₀₁ : B 0 1 = B 1 0 := by
    have := congrFun (congrFun hB 0) 1
    simpa using this.symm
  have hs₀₂ : B 0 2 = B 2 0 := by
    have := congrFun (congrFun hB 0) 2
    simpa using this.symm
  have hs₁₂ : B 1 2 = B 2 1 := by
    have := congrFun (congrFun hB 1) 2
    simpa using this.symm
  simp only [triadBracket, rawRecipient, generatorMap_apply, curlSymbol]
  simp [Vec3.dot, Vec3.cross, Matrix.mulVec, dotProduct, complexifyMatrix,
    latticeToComplex, Fin.sum_univ_succ] at hf₀ hf₁ hf₂ ⊢
  rw [hs₀₁, hs₀₂, hs₁₂]
  have hr₀ : (r 0 : ℂ) = -(p 0 : ℂ) - (q 0 : ℂ) := by
    linear_combination hf₀
  have hr₁ : (r 1 : ℂ) = -(p 1 : ℂ) - (q 1 : ℂ) := by
    linear_combination hf₁
  have hr₂ : (r 2 : ℂ) = -(p 2 : ℂ) - (q 2 : ℂ) := by
    linear_combination hf₂
  rw [hr₀, hr₁, hr₂]
  ring

/-- The complete twelve-parameter generator family has zero bracket on every
divergence-free Fourier triad. -/
theorem symmetric_generator_triad_cancel (A B : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (p q r : LatticeVec) (a u v : CVec)
    (hpqr : p + q + r = 0)
    (ha : Transverse p a) (hu : Transverse q u) (hv : Transverse r v) :
    triadBracket (generatorMap A B) p q r a u v = 0 := by
  have hzero := symmetric_zero_order_triad_cancel A hA p q r a u v hpqr ha hu hv
  have hfirst := symmetric_first_order_triad_cancel B hB p q r a u v hpqr ha hu hv
  calc
    triadBracket (generatorMap A B) p q r a u v =
        triadBracket (fun _ ↦ (complexifyMatrix A).mulVecLin) p q r a u v +
          triadBracket (fun k ↦ generatorMap 0 B k) p q r a u v := by
      simp [triadBracket, generatorMap, rawRecipient, Vec3.dot_add_left]
      ring
    _ = 0 := by rw [hzero, hfirst]; simp

theorem triadBracket_sub
    (R S : LatticeVec → CVec →ₗ[ℂ] CVec)
    (p q r : LatticeVec) (a u v : CVec) :
    triadBracket (fun k ↦ R k - S k) p q r a u v =
      triadBracket R p q r a u v - triadBracket S p q r a u v := by
  simp [triadBracket, Vec3.dot_sub_left]
  ring

/-! ## From triads to the finite-support cubic form -/

/-- A triple finite sum, used to make the permutation argument explicit. -/
def tripleSum {α : Type*} (s : Finset α) (T : α → α → α → ℂ) : ℂ :=
  ∑ x ∈ s, ∑ y ∈ s, ∑ z ∈ s, T x y z

/-- Sum a trilinear interaction over all six permutations of its inputs. -/
def sixPermutationSum {α : Type*} (T : α → α → α → ℂ) (x y z : α) : ℂ :=
  T x y z + T x z y + T y x z + T y z x + T z x y + T z y x

private theorem tripleSum_swap12 {α : Type*} [DecidableEq α] (s : Finset α)
    (T : α → α → α → ℂ) :
    tripleSum s (fun x y z ↦ T y x z) = tripleSum s T := by
  simp only [tripleSum]
  rw [Finset.sum_comm]

private theorem tripleSum_swap23 {α : Type*} [DecidableEq α] (s : Finset α)
    (T : α → α → α → ℂ) :
    tripleSum s (fun x y z ↦ T x z y) = tripleSum s T := by
  simp only [tripleSum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]

private theorem tripleSum_cycle {α : Type*} [DecidableEq α] (s : Finset α)
    (T : α → α → α → ℂ) :
    tripleSum s (fun x y z ↦ T y z x) = tripleSum s T := by
  simp only [tripleSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_comm]

/-- If every six-permutation orbit sum vanishes, then the complete ordered
triple sum vanishes. Division by six is legitimate over `ℂ`. -/
theorem tripleSum_eq_zero_of_six_permutations {α : Type*} [DecidableEq α]
    (s : Finset α) (T : α → α → α → ℂ)
    (h : ∀ x y z, sixPermutationSum T x y z = 0) : tripleSum s T = 0 := by
  have h12 : tripleSum s (fun x y z ↦ T y x z) = tripleSum s T :=
    tripleSum_swap12 s T
  have h23 : tripleSum s (fun x y z ↦ T x z y) = tripleSum s T :=
    tripleSum_swap23 s T
  have hc1 : tripleSum s (fun x y z ↦ T y z x) = tripleSum s T :=
    tripleSum_cycle s T
  have hc2 : tripleSum s (fun x y z ↦ T z x y) = tripleSum s T := by
    symm
    simpa only [tripleSum] using (tripleSum_cycle s (fun x y z ↦ T z x y))
  have h13 : tripleSum s (fun x y z ↦ T z y x) = tripleSum s T := by
    calc
      tripleSum s (fun x y z ↦ T z y x) =
          tripleSum s (fun x y z ↦ T z x y) := by
        simpa only [tripleSum] using
          (tripleSum_swap12 s (fun x y z ↦ T z y x)).symm
      _ = tripleSum s T := hc2
  have hsix : tripleSum s (sixPermutationSum T) = 0 := by
    simp [tripleSum, h]
  simp only [tripleSum, sixPermutationSum, Finset.sum_add_distrib] at hsix
  change tripleSum s T + tripleSum s (fun x y z ↦ T x z y) +
    tripleSum s (fun x y z ↦ T y x z) + tripleSum s (fun x y z ↦ T y z x) +
    tripleSum s (fun x y z ↦ T z x y) + tripleSum s (fun x y z ↦ T z y x) = 0 at hsix
  rw [h23, h12, hc1, hc2, h13] at hsix
  have hsix' : (6 : ℂ) * tripleSum s T = 0 := by
    linear_combination hsix
  exact (mul_eq_zero.mp hsix').resolve_left (by norm_num)

/-- One ordered recipient-parent-parent interaction. -/
def orderedInteraction (R : LatticeVec → CVec →ₗ[ℂ] CVec) (w : TrigField)
    (p q r : LatticeVec) : ℂ :=
  if p + q + r = 0 then
    Vec3.dot (R p (w.coeff p))
      (Vec3.dot (w.coeff q) (latticeToComplex r) • w.coeff r)
  else 0

theorem generator_sixPermutationSum_zero (A B : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B) (w : TrigField) :
    ∀ p q r, sixPermutationSum (orderedInteraction (generatorMap A B) w) p q r = 0 := by
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
    simp [sixPermutationSum, orderedInteraction, hsum, hprq, hqpr, hqrp, hrpq,
      hrqp, triadBracket, rawRecipient, Vec3.dot_add_right,
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
    simp [sixPermutationSum, orderedInteraction, hsum, hprq, hqpr, hqrp, hrpq, hrqp]

theorem generator_orderedInteraction_sum_zero (A B : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B) (w : TrigField) :
    tripleSum w.coeff.support (orderedInteraction (generatorMap A B) w) = 0 :=
  tripleSum_eq_zero_of_six_permutations _ _
    (generator_sixPermutationSum_zero A B hA hB w)

theorem pair_sum_eq_neg_iff_triple_sum_eq_zero (p q r : LatticeVec) :
    q + r = -p ↔ p + q + r = 0 := by
  constructor <;> intro h
  · calc
      p + q + r = p + (q + r) := by abel
      _ = p + (-p) := by rw [h]
      _ = 0 := by simp
  · calc
      q + r = -p + (p + q + r) := by abel
      _ = -p := by rw [h]; simp

private theorem finsupp_sum_eq_support_sum {α M N : Type*} [Zero M] [AddCommMonoid N]
    (f : α →₀ M) (g : α → M → N) :
    f.sum g = ∑ a ∈ f.support, g a (f a) := by
  rfl

/-- The convolution definition of the cubic form is exactly `i` times the
complete ordered interaction sum. -/
theorem cubicForm_eq_I_mul_tripleSum (R : MultiplierSymbol) (w : TrigField) :
    cubicForm R w = Complex.I *
      tripleSum w.coeff.support (orderedInteraction R.map w) := by
  classical
  simp [cubicForm, convectiveCoeff, tripleSum, orderedInteraction,
    pair_sum_eq_neg_iff_triple_sum_eq_zero, Vec3.dot_sum_right,
    Vec3.dot_smul_right, Finset.mul_sum, finsupp_sum_eq_support_sum]
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

theorem cubicForm_eq_cubicTrilinear (R : MultiplierSymbol) (w : TrigField) :
    cubicForm R w = cubicTrilinear R w w w := by
  classical
  simp [cubicForm, convectiveCoeff, cubicTrilinear,
    pair_sum_eq_neg_iff_triple_sum_eq_zero, Vec3.dot_sum_right,
    Vec3.dot_smul_right, finsupp_sum_eq_support_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hsum : p + q + r = 0
  · simp [triCoeff, hsum, Vec3.dot]
    ring
  · simp [triCoeff, hsum, Vec3.dot]

theorem cubicTrilinear_add_left (R : MultiplierSymbol) (x y z t : TrigField) :
    cubicTrilinear R (x + y) z t =
      cubicTrilinear R x z t + cubicTrilinear R y z t := by
  classical
  unfold cubicTrilinear
  apply Finsupp.sum_add_index'
  · intro p
    apply Finset.sum_eq_zero
    intro q hq
    apply Finset.sum_eq_zero
    intro r hr
    exact triCoeff_zero_left R p q r (z.coeff q) (t.coeff r)
  · intro p a b
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro q hq
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro r hr
    exact triCoeff_add_left R p q r a b (z.coeff q) (t.coeff r)

theorem cubicTrilinear_add_middle (R : MultiplierSymbol) (x y z t : TrigField) :
    cubicTrilinear R x (y + z) t =
      cubicTrilinear R x y t + cubicTrilinear R x z t := by
  classical
  unfold cubicTrilinear
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro p hp
  apply Finsupp.sum_add_index'
  · intro q
    apply Finset.sum_eq_zero
    intro r hr
    exact triCoeff_zero_middle R p q r (x.coeff p) (t.coeff r)
  · intro q a b
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro r hr
    exact triCoeff_add_middle R p q r (x.coeff p) a b (t.coeff r)

theorem cubicTrilinear_add_right (R : MultiplierSymbol) (x y z t : TrigField) :
    cubicTrilinear R x y (z + t) =
      cubicTrilinear R x y z + cubicTrilinear R x y t := by
  classical
  unfold cubicTrilinear
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro p hp
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro q hq
  apply Finsupp.sum_add_index'
  · intro r
    exact triCoeff_zero_right R p q r (x.coeff p) (y.coeff q)
  · intro r a b
    exact triCoeff_add_right R p q r (x.coeff p) (y.coeff q) a b

noncomputable def mixedSix (R : MultiplierSymbol) (x y z : TrigField) : ℂ :=
  cubicTrilinear R x y z + cubicTrilinear R x z y +
  cubicTrilinear R y x z + cubicTrilinear R y z x +
  cubicTrilinear R z x y + cubicTrilinear R z y x

theorem mixedSix_eq_zero_of_universal (R : MultiplierSymbol)
    (hR : UniversalCancellation R) (x y z : TrigField) :
    mixedSix R x y z = 0 := by
  have hxyz := hR ((x + y) + z)
  have hxy := hR (x + y)
  have hxz := hR (x + z)
  have hyz := hR (y + z)
  have hx := hR x
  have hy := hR y
  have hz := hR z
  rw [cubicForm_eq_cubicTrilinear] at hxyz hxy hxz hyz hx hy hz
  simp only [cubicTrilinear_add_left, cubicTrilinear_add_middle,
    cubicTrilinear_add_right] at hxyz hxy hxz hyz
  unfold mixedSix
  linear_combination hxyz - hxy - hxz - hyz + hx + hy + hz

theorem mixed_sign_sums_ne_zero {p q r : LatticeVec}
    (hpqr : p + q + r = 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    p + q - r ≠ 0 ∧ p - q + r ≠ 0 ∧ -p + q + r ≠ 0 ∧
    p - q - r ≠ 0 ∧ -p + q - r ≠ 0 ∧ -p - q + r ≠ 0 := by
  constructor
  · intro h
    apply hr
    funext i
    have hs := congrFun hpqr i
    have hm := congrFun h i
    simp at hs hm
    have hi : r i = 0 := by omega
    simpa using hi
  constructor
  · intro h
    apply hq
    funext i
    have hs := congrFun hpqr i
    have hm := congrFun h i
    simp at hs hm
    have hi : q i = 0 := by omega
    simpa using hi
  constructor
  · intro h
    apply hp
    funext i
    have hs := congrFun hpqr i
    have hm := congrFun h i
    simp at hs hm
    have hi : p i = 0 := by omega
    simpa using hi
  constructor
  · intro h
    apply hp
    funext i
    have hs := congrFun hpqr i
    have hm := congrFun h i
    simp at hs hm
    have hi : p i = 0 := by omega
    simpa using hi
  constructor
  · intro h
    apply hq
    funext i
    have hs := congrFun hpqr i
    have hm := congrFun h i
    simp at hs hm
    have hi : q i = 0 := by omega
    simpa using hi
  · intro h
    apply hr
    funext i
    have hs := congrFun hpqr i
    have hm := congrFun h i
    simp at hs hm
    have hi : r i = 0 := by omega
    simpa using hi

def orderedAtom (R : MultiplierSymbol) (p q r : LatticeVec)
    (a u v : CVec) : ℂ :=
  Vec3.dot (R.map p a) (Vec3.dot u (latticeToComplex r) • v)

theorem cubicTrilinear_realPairField_expand (R : MultiplierSymbol)
    (p q r : LatticeVec) (a u v : CVec)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (ha : Transverse p a) (hu : Transverse q u) (hv : Transverse r v) :
    cubicTrilinear R (realPairField p a hp ha) (realPairField q u hq hu)
      (realPairField r v hr hv) =
      triCoeff R p q r a u v + triCoeff R p q (-r) a u (conjVec v) +
      triCoeff R p (-q) r a (conjVec u) v +
      triCoeff R p (-q) (-r) a (conjVec u) (conjVec v) +
      triCoeff R (-p) q r (conjVec a) u v +
      triCoeff R (-p) q (-r) (conjVec a) u (conjVec v) +
      triCoeff R (-p) (-q) r (conjVec a) (conjVec u) v +
      triCoeff R (-p) (-q) (-r) (conjVec a) (conjVec u) (conjVec v) := by
  classical
  let sumR (pp qq : LatticeVec) (xp yq : CVec) :=
    realPairCoeff_sum r v
      (fun rr zr ↦ triCoeff R pp qq rr xp yq zr)
      (fun rr ↦ triCoeff_zero_right R pp qq rr xp yq)
      (fun rr z₁ z₂ ↦ triCoeff_add_right R pp qq rr xp yq z₁ z₂)
  have sumQ (pp : LatticeVec) (xp : CVec) :
      (realPairCoeff q u).sum (fun qq yq ↦
        (realPairCoeff r v).sum fun rr zr ↦ triCoeff R pp qq rr xp yq zr) =
      (triCoeff R pp q r xp u v + triCoeff R pp q (-r) xp u (conjVec v)) +
      (triCoeff R pp (-q) r xp (conjVec u) v +
        triCoeff R pp (-q) (-r) xp (conjVec u) (conjVec v)) := by
    rw [realPairCoeff_sum q u]
    · rw [sumR, sumR]
    · intro qq
      rw [sumR]
      simp
    · intro qq y₁ y₂
      rw [sumR, sumR, sumR]
      rw [triCoeff_add_middle, triCoeff_add_middle]
      ring
  unfold cubicTrilinear
  dsimp only [realPairField]
  change (realPairCoeff p a).sum _ = _
  rw [realPairCoeff_sum p a]
  · rw [sumQ, sumQ]
    ring
  · intro pp
    rw [sumQ]
    simp
  · intro pp x₁ x₂
    rw [sumQ, sumQ, sumQ]
    simp only [triCoeff_add_left]
    ring

theorem cubicTrilinear_realPairField_reduce (R : MultiplierSymbol)
    (p q r : LatticeVec) (a u v : CVec)
    (hpqr : p + q + r = 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (ha : Transverse p a) (hu : Transverse q u) (hv : Transverse r v) :
    cubicTrilinear R (realPairField p a hp ha) (realPairField q u hq hu)
      (realPairField r v hr hv) =
      Complex.I * orderedAtom R p q r a u v -
        Complex.I * conj (orderedAtom R p q r a u v) := by
  rw [cubicTrilinear_realPairField_expand R p q r a u v hp hq hr ha hu hv]
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := mixed_sign_sums_ne_zero hpqr hp hq hr
  have h₁' : p + q + (-r) ≠ 0 := by simpa [sub_eq_add_neg] using h₁
  have h₂' : p + (-q) + r ≠ 0 := by simpa [sub_eq_add_neg] using h₂
  have h₄' : p + (-q) + (-r) ≠ 0 := by simpa [sub_eq_add_neg] using h₄
  have h₅' : -p + q + (-r) ≠ 0 := by simpa [sub_eq_add_neg] using h₅
  have h₆' : -p + -q + r ≠ 0 := by simpa [sub_eq_add_neg] using h₆
  have hneg : -p + -q + -r = 0 := by
    calc
      -p + -q + -r = -(p + q + r) := by abel
      _ = 0 := by rw [hpqr]; simp
  have hreal := R.realityCompatible p a ha
  simp [triCoeff, hpqr, h₁', h₂', h₃, h₄', h₅', h₆', hneg,
    orderedAtom, hreal, Vec3.dot, latticeToComplex, conjVec]
  ring

theorem six_orderedAtoms_eq_triadBracket (R : MultiplierSymbol)
    (p q r : LatticeVec) (a u v : CVec) :
    orderedAtom R p q r a u v + orderedAtom R p r q a v u +
      orderedAtom R q p r u a v + orderedAtom R q r p u v a +
      orderedAtom R r p q v a u + orderedAtom R r q p v u a =
        triadBracket R.map p q r a u v := by
  simp [orderedAtom, triadBracket, rawRecipient, Vec3.dot_add_right]
  ring

theorem mixedSix_realPairFields (R : MultiplierSymbol)
    (p q r : LatticeVec) (a u v : CVec)
    (hpqr : p + q + r = 0) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (ha : Transverse p a) (hu : Transverse q u) (hv : Transverse r v) :
    mixedSix R (realPairField p a hp ha) (realPairField q u hq hu)
      (realPairField r v hr hv) =
      Complex.I * triadBracket R.map p q r a u v -
        Complex.I * conj (triadBracket R.map p q r a u v) := by
  have hprq : p + r + q = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hpqr
  have hqpr : q + p + r = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hpqr
  have hqrp : q + r + p = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hpqr
  have hrpq : r + p + q = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hpqr
  have hrqp : r + q + p = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hpqr
  unfold mixedSix
  rw [cubicTrilinear_realPairField_reduce R p q r a u v hpqr hp hq hr ha hu hv,
    cubicTrilinear_realPairField_reduce R p r q a v u hprq hp hr hq ha hv hu,
    cubicTrilinear_realPairField_reduce R q p r u a v hqpr hq hp hr hu ha hv,
    cubicTrilinear_realPairField_reduce R q r p u v a hqrp hq hr hp hu hv ha,
    cubicTrilinear_realPairField_reduce R r p q v a u hrpq hr hp hq hv ha hu,
    cubicTrilinear_realPairField_reduce R r q p v u a hrqp hr hq hp hv hu ha]
  rw [← six_orderedAtoms_eq_triadBracket]
  simp only [map_add]
  ring

theorem triadBracket_smul_first
    (R : LatticeVec → CVec →ₗ[ℂ] CVec)
    (p q r : LatticeVec) (a u v : CVec) (c : ℂ) :
    triadBracket R p q r (c • a) u v =
      c * triadBracket R p q r a u v := by
  simp [triadBracket, rawRecipient, Vec3.dot_add_right, smul_smul]
  ring

/-- Sufficiency in Theorem A: every member of the twelve-parameter symmetric
generator family has universal convective cancellation. -/
theorem generator_universalCancellation (A B : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B) :
    UniversalCancellation (generatorSymbol A B) := by
  intro w
  rw [cubicForm_eq_I_mul_tripleSum]
  change Complex.I * tripleSum w.coeff.support
    (orderedInteraction (generatorMap A B) w) = 0
  rw [generator_orderedInteraction_sum_zero A B hA hB w]
  simp

theorem cubicForm_differenceSymbol (R : MultiplierSymbol) (A B : RMatrix)
    (w : TrigField) :
    cubicForm (differenceSymbol R A B) w =
      cubicForm R w - cubicForm (generatorSymbol A B) w := by
  classical
  simp [cubicForm, differenceSymbol, generatorSymbol, Vec3.dot_sub_left]

theorem difference_universalCancellation (R : MultiplierSymbol) (A B : RMatrix)
    (hR : UniversalCancellation R) (hA : A.transpose = A)
    (hB : B.transpose = B) : UniversalCancellation (differenceSymbol R A B) := by
  intro w
  rw [cubicForm_differenceSymbol, hR w,
    generator_universalCancellation A B hA hB w]
  simp

/-! ## Raw-recipient algebra for necessity -/

/-- Algebraic version of the raw recipient map (5.1), over any commutative
ring. -/
def rawRecipientAlgebra {R : Type*} [CommRing R]
    (q r u v : Fin 3 → R) : Fin 3 → R :=
  Vec3.dot u r • v + Vec3.dot v q • u

/-- Rotation by `z` in the plane orthogonal to `z`. -/
def crossRotate {R : Type*} [CommRing R]
    (z x : Fin 3 → R) : Fin 3 → R := Vec3.cross z x

/-- Formula (5.2), with `Z²` represented algebraically by `z · z`.
This identity is valid over an arbitrary commutative ring. -/
theorem rawRecipient_parametrization {R : Type*} [CommRing R]
    (q r : Fin 3 → R) (u₀ v₀ α β : R) :
    let z := Vec3.cross q r
    let J := crossRotate z
    let u := u₀ • z + α • J q
    let v := v₀ • z + β • J r
    rawRecipientAlgebra q r u v =
      Vec3.dot z z • ((α * v₀ - β * u₀) • z + (α * β) • J (r - q)) := by
  dsimp only
  funext i
  fin_cases i <;>
    simp [rawRecipientAlgebra, crossRotate, Vec3.cross, Vec3.dot] <;> ring

/-- Completeness identity for the orthogonal frame
`z, z × d, d` when `z · d = 0`. -/
theorem orthogonal_cross_frame_decomposition {R : Type*} [CommRing R]
    (z d y : Fin 3 → R) (hzd : Vec3.dot z d = 0) :
    (Vec3.dot z z * Vec3.dot d d) • y =
      (Vec3.dot d d * Vec3.dot y z) • z +
      Vec3.dot y (Vec3.cross z d) • Vec3.cross z d +
      (Vec3.dot z z * Vec3.dot y d) • d := by
  funext i
  fin_cases i
  · change (Vec3.dot z z * Vec3.dot d d) * y 0 =
      (Vec3.dot d d * Vec3.dot y z) * z 0 +
      Vec3.dot y (Vec3.cross z d) * Vec3.cross z d 0 +
      (Vec3.dot z z * Vec3.dot y d) * d 0
    simp [Vec3.dot, Vec3.cross] at hzd ⊢
    linear_combination
      (-d 0 * y 0 * z 0 - d 0 * y 1 * z 1 - d 0 * y 2 * z 2 +
        d 1 * y 0 * z 1 - d 1 * y 1 * z 0 + d 2 * y 0 * z 2 -
        d 2 * y 2 * z 0) * hzd
  · change (Vec3.dot z z * Vec3.dot d d) * y 1 =
      (Vec3.dot d d * Vec3.dot y z) * z 1 +
      Vec3.dot y (Vec3.cross z d) * Vec3.cross z d 1 +
      (Vec3.dot z z * Vec3.dot y d) * d 1
    simp [Vec3.dot, Vec3.cross] at hzd ⊢
    linear_combination
      (-d 0 * y 0 * z 1 + d 0 * y 1 * z 0 - d 1 * y 0 * z 0 -
        d 1 * y 1 * z 1 - d 1 * y 2 * z 2 + d 2 * y 1 * z 2 -
        d 2 * y 2 * z 1) * hzd
  · change (Vec3.dot z z * Vec3.dot d d) * y 2 =
      (Vec3.dot d d * Vec3.dot y z) * z 2 +
      Vec3.dot y (Vec3.cross z d) * Vec3.cross z d 2 +
      (Vec3.dot z z * Vec3.dot y d) * d 2
    simp [Vec3.dot, Vec3.cross] at hzd ⊢
    linear_combination
      (-d 0 * y 0 * z 2 + d 0 * y 2 * z 0 - d 1 * y 1 * z 2 +
        d 1 * y 2 * z 1 - d 2 * y 0 * z 0 - d 2 * y 1 * z 1 -
        d 2 * y 2 * z 2) * hzd

/-- Complex collinearity, allowing the zero vector. -/
def ParallelC (u v : CVec) : Prop := ∃ c : ℂ, u = c • v

theorem cross_eq_zero_of_parallel {u v : CVec} (h : ParallelC u v) :
    Vec3.cross u v = 0 := by
  obtain ⟨c, rfl⟩ := h
  rw [Vec3.cross_smul_left, Vec3.cross_self]
  simp

/-- A vector orthogonal to the first two members of a nondegenerate
orthogonal cross frame is parallel to its third member. -/
theorem parallel_of_dot_cross_frame_eq_zero (z d y : CVec)
    (hzd : Vec3.dot z d = 0) (hzz : Vec3.dot z z ≠ 0)
    (hdd : Vec3.dot d d ≠ 0) (hyz : Vec3.dot y z = 0)
    (hycross : Vec3.dot y (Vec3.cross z d) = 0) : ParallelC y d := by
  refine ⟨Vec3.dot y d / Vec3.dot d d, ?_⟩
  have hframe := orthogonal_cross_frame_decomposition z d y hzd
  rw [hyz, hycross] at hframe
  funext i
  have hi := congrFun hframe i
  simp at hi
  change y i = (Vec3.dot y d / Vec3.dot d d) * d i
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hdd).2
  apply mul_left_cancel₀ hzz
  simpa [mul_assoc, mul_comm, mul_left_comm] using hi

/-- Transversality to an arbitrary complex direction. -/
def TransverseTo (q u : CVec) : Prop := Vec3.dot q u = 0

/-- Algebraic core of Lemma 5.2. Orthogonality to every raw recipient forces
the tested output onto the difference line `r-q`. The two nonzero norm
hypotheses are automatic for complexifications of non-collinear real lattice
vectors and are kept explicit here to isolate the linear algebra. -/
theorem raw_image_line (q r y : CVec)
    (hz : Vec3.dot (Vec3.cross q r) (Vec3.cross q r) ≠ 0)
    (hd : Vec3.dot (r - q) (r - q) ≠ 0)
    (horth : ∀ (u v : CVec), TransverseTo q u → TransverseTo r v →
      Vec3.dot y (rawRecipientAlgebra q r u v) = 0) :
    ParallelC y (r - q) := by
  let z := Vec3.cross q r
  let d := r - q
  let J := crossRotate z
  have hzd : Vec3.dot z d = 0 := by
    dsimp [z, d]
    simp [Vec3.dot, Vec3.cross]
    ring
  let u₁ := J q
  let v₁ := z
  have hu₁ : TransverseTo q u₁ := by
    dsimp [TransverseTo, u₁, J, crossRotate, z]
    simp [Vec3.dot, Vec3.cross]
    ring
  have hv₁ : TransverseTo r v₁ := by
    dsimp [TransverseTo, v₁, z]
    simp [Vec3.dot, Vec3.cross]
    ring
  have hrec₁ : rawRecipientAlgebra q r u₁ v₁ = Vec3.dot z z • z := by
    simpa [z, J, u₁, v₁, crossRotate] using
      (rawRecipient_parametrization q r (0 : ℂ) 1 1 0)
  have hyzScaled := horth u₁ v₁ hu₁ hv₁
  rw [hrec₁] at hyzScaled
  have hyz : Vec3.dot y z = 0 := by
    simp only [Vec3.dot_smul_right] at hyzScaled
    exact (mul_eq_zero.mp hyzScaled).resolve_left hz
  let u₂ := J q
  let v₂ := J r
  have hu₂ : TransverseTo q u₂ := by
    dsimp [TransverseTo, u₂, J, crossRotate, z]
    simp [Vec3.dot, Vec3.cross]
    ring
  have hv₂ : TransverseTo r v₂ := by
    dsimp [TransverseTo, v₂, J, crossRotate, z]
    simp [Vec3.dot, Vec3.cross]
    ring
  have hrec₂ : rawRecipientAlgebra q r u₂ v₂ =
      Vec3.dot z z • J d := by
    simpa [z, d, J, u₂, v₂, crossRotate] using
      (rawRecipient_parametrization q r (0 : ℂ) 0 1 1)
  have hycrossScaled := horth u₂ v₂ hu₂ hv₂
  rw [hrec₂] at hycrossScaled
  have hycross : Vec3.dot y (Vec3.cross z d) = 0 := by
    simp only [Vec3.dot_smul_right] at hycrossScaled
    change Vec3.dot z z * Vec3.dot y (Vec3.cross z d) = 0 at hycrossScaled
    exact (mul_eq_zero.mp hycrossScaled).resolve_left hz
  exact parallel_of_dot_cross_frame_eq_zero z d y hzd hz hd hyz hycross

theorem real_dot_self_pos (v : RVec) (hv : v ≠ 0) : 0 < Vec3.dot v v := by
  by_contra hpos
  have hle : Vec3.dot v v ≤ 0 := le_of_not_gt hpos
  have hv₀ : v 0 = 0 := by
    simp [Vec3.dot] at hle
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have hv₁ : v 1 = 0 := by
    simp [Vec3.dot] at hle
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have hv₂ : v 2 = 0 := by
    simp [Vec3.dot] at hle
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  apply hv
  funext i
  fin_cases i <;> assumption

theorem dot_realToComplex_self (v : RVec) :
    Vec3.dot (realToComplexVec v) (realToComplexVec v) =
      (↑(Vec3.dot v v) : ℂ) := by
  simp [Vec3.dot, realToComplexVec]

theorem complexified_real_dot_self_ne_zero (v : RVec) (hv : v ≠ 0) :
    Vec3.dot (realToComplexVec v) (realToComplexVec v) ≠ 0 := by
  rw [dot_realToComplex_self]
  exact_mod_cast (ne_of_gt (real_dot_self_pos v hv))

theorem latticeToComplex_eq_realToComplex (k : LatticeVec) :
    latticeToComplex k = realToComplexVec (latticeToReal k) := by
  funext i
  simp [latticeToComplex, realToComplexVec, latticeToReal]

theorem latticeToReal_sub (q r : LatticeVec) :
    latticeToReal (q - r) = latticeToReal q - latticeToReal r := by
  funext i
  simp [latticeToReal]

/-- Non-collinearity in the real lattice geometry used by the manuscript. -/
def LatticeNonCollinear (q r : LatticeVec) : Prop :=
  Vec3.cross (latticeToReal q) (latticeToReal r) ≠ 0

theorem realToComplexVec_ne_zero {v : RVec} (hv : v ≠ 0) :
    realToComplexVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrFun h i
  simp [realToComplexVec] at hi
  exact hi

theorem lattice_cross_complexification (q r : LatticeVec) :
    Vec3.cross (latticeToComplex q) (latticeToComplex r) =
      realToComplexVec (Vec3.cross (latticeToReal q) (latticeToReal r)) := by
  rw [latticeToComplex_eq_realToComplex, latticeToComplex_eq_realToComplex]
  exact cross_complexification q (latticeToReal r)

theorem lattice_not_parallel_of_noncollinear {q r : LatticeVec}
    (hqr : LatticeNonCollinear q r) :
    ¬ ParallelC (latticeToComplex q) (latticeToComplex r) := by
  intro hparallel
  have hzero := cross_eq_zero_of_parallel hparallel
  rw [lattice_cross_complexification] at hzero
  exact realToComplexVec_ne_zero hqr hzero

theorem lattice_difference_ne_zero_of_noncollinear {q r : LatticeVec}
    (hqr : LatticeNonCollinear q r) : latticeToReal (r - q) ≠ 0 := by
  intro hzero
  have heqReal : latticeToReal r = latticeToReal q := by
    rw [latticeToReal_sub, sub_eq_zero] at hzero
    exact hzero
  have heq : r = q := by
    funext i
    have hi := congrFun heqReal i
    simp [latticeToReal] at hi
    exact hi
  apply hqr
  rw [heq]
  exact Vec3.cross_self _

/-- Lattice form of the raw image-line lemma. Its only geometric assumption
is the manuscript's non-collinearity condition `q × r ≠ 0`. -/
theorem lattice_raw_image_line (q r : LatticeVec) (y : CVec)
    (hqr : LatticeNonCollinear q r)
    (horth : ∀ (u v : CVec), Transverse q u → Transverse r v →
      Vec3.dot y (rawRecipient q r u v) = 0) :
    ParallelC y (latticeToComplex (r - q)) := by
  have hz : Vec3.dot
      (Vec3.cross (latticeToComplex q) (latticeToComplex r))
      (Vec3.cross (latticeToComplex q) (latticeToComplex r)) ≠ 0 := by
    rw [lattice_cross_complexification]
    exact complexified_real_dot_self_ne_zero _ hqr
  have hdReal := lattice_difference_ne_zero_of_noncollinear hqr
  have hd : Vec3.dot (latticeToComplex r - latticeToComplex q)
      (latticeToComplex r - latticeToComplex q) ≠ 0 := by
    rw [latticeToComplex_eq_realToComplex, latticeToComplex_eq_realToComplex]
    have hsub : realToComplexVec (latticeToReal r) - realToComplexVec (latticeToReal q) =
        realToComplexVec (latticeToReal (r - q)) := by
      funext i
      simp [realToComplexVec, latticeToReal]
    rw [hsub]
    exact complexified_real_dot_self_ne_zero _ hdReal
  have hline := raw_image_line (latticeToComplex q) (latticeToComplex r) y hz hd
    (by
      intro u v hu hv
      exact horth u v hu hv)
  rw [latticeToComplex_eq_realToComplex, latticeToReal_sub]
  rw [realToComplexVec_sub]
  rw [latticeToComplex_eq_realToComplex, latticeToComplex_eq_realToComplex] at hline
  exact hline

theorem eq_zero_of_parallel_nonparallel {y d₁ d₂ : CVec}
    (h₁ : ParallelC y d₁) (h₂ : ParallelC y d₂)
    (hnonparallel : ¬ ParallelC d₁ d₂) : y = 0 := by
  by_contra hy
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  have hc₁ne : c₁ ≠ 0 := by
    intro hc
    apply hy
    rw [hc, zero_smul] at hc₁
    exact hc₁
  apply hnonparallel
  refine ⟨c₁⁻¹ * c₂, ?_⟩
  calc
    d₁ = c₁⁻¹ • y := by rw [hc₁]; simp [hc₁ne]
    _ = c₁⁻¹ • (c₂ • d₂) := by rw [hc₂]
    _ = (c₁⁻¹ * c₂) • d₂ := by rw [smul_smul]

/-- The local two-triad determination rule in Lemma 5.2. Two nonparallel
difference lines at the same recipient force its tested output to vanish. -/
theorem two_triad_determination
    (q₁ r₁ q₂ r₂ : LatticeVec) (y : CVec)
    (hnc₁ : LatticeNonCollinear q₁ r₁)
    (hnc₂ : LatticeNonCollinear q₂ r₂)
    (hdirections : ¬ ParallelC (latticeToComplex (r₁ - q₁))
      (latticeToComplex (r₂ - q₂)))
    (horth₁ : ∀ (u v : CVec), Transverse q₁ u → Transverse r₁ v →
      Vec3.dot y (rawRecipient q₁ r₁ u v) = 0)
    (horth₂ : ∀ (u v : CVec), Transverse q₂ u → Transverse r₂ v →
      Vec3.dot y (rawRecipient q₂ r₂ u v) = 0) :
    y = 0 :=
  eq_zero_of_parallel_nonparallel
    (lattice_raw_image_line q₁ r₁ y hnc₁ horth₁)
    (lattice_raw_image_line q₂ r₂ y hnc₂ horth₂)
    hdirections

/-- A symbol block vanishes on its transverse input fiber. -/
def VanishesAt (D : LatticeVec → CVec →ₗ[ℂ] CVec) (k : LatticeVec) : Prop :=
  ∀ v : CVec, Transverse k v → D k v = 0

/-- The local coefficient consequence supplied by phase polarization. -/
def HasTriadCancellation (D : LatticeVec → CVec →ₗ[ℂ] CVec) : Prop :=
  ∀ (p q r : LatticeVec) (a u v : CVec), p + q + r = 0 →
    Transverse p a → Transverse q u → Transverse r v →
      triadBracket D p q r a u v = 0

/-- The nondegenerate triads visible to mean-zero real Fourier fields and
used by both the seed and propagation arguments. -/
def HasActiveTriadCancellation (D : LatticeVec → CVec →ₗ[ℂ] CVec) : Prop :=
  ∀ (p q r : LatticeVec) (a u v : CVec), p + q + r = 0 →
    p ≠ 0 → q ≠ 0 → r ≠ 0 → LatticeNonCollinear q r →
    Transverse p a → Transverse q u → Transverse r v →
      triadBracket D p q r a u v = 0

/-- Phase polarization: universal cancellation on real fields supplies the
complex active-triad identity used by the lattice propagation argument. -/
theorem universal_hasActiveTriadCancellation (R : MultiplierSymbol)
    (hR : UniversalCancellation R) : HasActiveTriadCancellation R.map := by
  intro p q r a u v hpqr hp hq hr _hnc ha hu hv
  let B := triadBracket R.map p q r a u v
  have hima : Transverse p (Complex.I • a) := transverse_smul Complex.I ha
  have hreal := mixedSix_eq_zero_of_universal R hR
    (realPairField p a hp ha) (realPairField q u hq hu)
    (realPairField r v hr hv)
  have himag := mixedSix_eq_zero_of_universal R hR
    (realPairField p (Complex.I • a) hp hima) (realPairField q u hq hu)
    (realPairField r v hr hv)
  rw [mixedSix_realPairFields R p q r a u v hpqr hp hq hr ha hu hv] at hreal
  rw [mixedSix_realPairFields R p q r (Complex.I • a) u v hpqr hp hq hr
    hima hu hv, triadBracket_smul_first] at himag
  change Complex.I * B - Complex.I * conj B = 0 at hreal
  change Complex.I * (Complex.I * B) -
    Complex.I * conj (Complex.I * B) = 0 at himag
  simp only [map_mul, Complex.conj_I] at himag
  have hdiff : B - conj B = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left Complex.I_ne_zero
    simpa [mul_sub] using hreal
  ring_nf at himag
  rw [Complex.I_sq] at himag
  ring_nf at himag
  change B = 0
  linear_combination (1 / 2) * hdiff - (1 / 2) * himag

/-- Reality compatibility, stated for a bare family of linear maps so it can
be applied to a difference symbol during the necessity proof. -/
def RealityCompatibleMap (D : LatticeVec → CVec →ₗ[ℂ] CVec) : Prop :=
  ∀ (k : LatticeVec) (v : CVec), Transverse k v →
    D (-k) (conjVec v) = conjVec (D k v)

theorem difference_realityCompatibleMap (R : MultiplierSymbol) (A B : RMatrix) :
    RealityCompatibleMap (differenceSymbol R A B).map :=
  (differenceSymbol R A B).realityCompatible

theorem hasTriadCancellation_difference
    (R S : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hR : HasTriadCancellation R) (hS : HasTriadCancellation S) :
    HasTriadCancellation (fun k ↦ R k - S k) := by
  intro p q r a u v hpqr ha hu hv
  rw [triadBracket_sub, hR p q r a u v hpqr ha hu hv,
    hS p q r a u v hpqr ha hu hv]
  simp

theorem hasActiveTriadCancellation_of_full
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hD : HasTriadCancellation D) :
    HasActiveTriadCancellation D := by
  intro p q r a u v hpqr _hp _hq _hr _hnc ha hu hv
  exact hD p q r a u v hpqr ha hu hv

theorem hasActiveTriadCancellation_difference
    (R S : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hR : HasActiveTriadCancellation R) (hS : HasActiveTriadCancellation S) :
    HasActiveTriadCancellation (fun k ↦ R k - S k) := by
  intro p q r a u v hpqr hp hq hr hnc ha hu hv
  rw [triadBracket_sub,
    hR p q r a u v hpqr hp hq hr hnc ha hu hv,
    hS p q r a u v hpqr hp hq hr hnc ha hu hv]
  simp

theorem noncollinear_left_ne_zero {q r : LatticeVec}
    (h : LatticeNonCollinear q r) : q ≠ 0 := by
  intro hq
  apply h
  rw [hq]
  funext i
  fin_cases i <;> simp [Vec3.cross, latticeToReal]

theorem noncollinear_right_ne_zero {q r : LatticeVec}
    (h : LatticeNonCollinear q r) : r ≠ 0 := by
  intro hr
  apply h
  rw [hr]
  funext i
  fin_cases i <;> simp [Vec3.cross, latticeToReal]

theorem recipient_ne_zero_of_noncollinear {p q r : LatticeVec}
    (hpqr : p + q + r = 0) (hnc : LatticeNonCollinear q r) : p ≠ 0 := by
  intro hp
  subst p
  have hr : r = -q := by
    have hsum : q + r = 0 := by simpa using hpqr
    calc
      r = -q + (q + r) := by abel
      _ = -q := by rw [hsum]; simp
  apply hnc
  rw [hr]
  funext i
  fin_cases i <;> simp [Vec3.cross, latticeToReal] <;> ring

theorem vanishesAt_neg_of_reality
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hreal : RealityCompatibleMap D)
    (k : LatticeVec) (hk : VanishesAt D k) : VanishesAt D (-k) := by
  intro v hv
  have hv' : Transverse k (conjVec v) := by
    have := transverse_neg_conj (k := -k) (v := v) hv
    simpa using this
  have hr := hreal k (conjVec v) hv'
  rw [conjVec_conjVec] at hr
  rw [hr, hk (conjVec v) hv']
  exact conjVec_zero

theorem vanishesAt_neg_iff_of_reality
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hreal : RealityCompatibleMap D)
    (k : LatticeVec) : VanishesAt D (-k) ↔ VanishesAt D k := by
  constructor
  · intro h
    have := vanishesAt_neg_of_reality D hreal (-k) h
    simpa using this
  · exact vanishesAt_neg_of_reality D hreal k

theorem target_image_line_of_vanishing_parents
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hD : HasActiveTriadCancellation D)
    (p q r : LatticeVec) (hpqr : p + q + r = 0)
    (hnc : LatticeNonCollinear q r) (hq : VanishesAt D q) (hr : VanishesAt D r)
    (a : CVec) (ha : Transverse p a) :
    ParallelC (D p a) (latticeToComplex (r - q)) := by
  apply lattice_raw_image_line q r (D p a) hnc
  intro u v hu hv
  have htriad := hD p q r a u v hpqr
    (recipient_ne_zero_of_noncollinear hpqr hnc)
    (noncollinear_left_ne_zero hnc) (noncollinear_right_ne_zero hnc) hnc ha hu hv
  have hqu := hq u hu
  have hrv := hr v hv
  simp [triadBracket, hqu, hrv, Vec3.dot] at htriad
  exact htriad

/-- Section 7.2's reusable propagation step at a common recipient. -/
theorem target_vanishes_of_two_known_parent_triads
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hD : HasActiveTriadCancellation D)
    (p q₁ r₁ q₂ r₂ : LatticeVec)
    (hsum₁ : p + q₁ + r₁ = 0) (hsum₂ : p + q₂ + r₂ = 0)
    (hnc₁ : LatticeNonCollinear q₁ r₁)
    (hnc₂ : LatticeNonCollinear q₂ r₂)
    (hdirections : ¬ ParallelC (latticeToComplex (r₁ - q₁))
      (latticeToComplex (r₂ - q₂)))
    (hq₁ : VanishesAt D q₁) (hr₁ : VanishesAt D r₁)
    (hq₂ : VanishesAt D q₂) (hr₂ : VanishesAt D r₂) :
    VanishesAt D p := by
  intro a ha
  apply eq_zero_of_parallel_nonparallel
    (target_image_line_of_vanishing_parents D hD p q₁ r₁ hsum₁ hnc₁ hq₁ hr₁ a ha)
    (target_image_line_of_vanishing_parents D hD p q₂ r₂ hsum₂ hnc₂ hq₂ hr₂ a ha)
    hdirections

theorem target_vanishes_of_two_known_parent_triads_lattice
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hD : HasActiveTriadCancellation D)
    (p q₁ r₁ q₂ r₂ : LatticeVec)
    (hsum₁ : p + q₁ + r₁ = 0) (hsum₂ : p + q₂ + r₂ = 0)
    (hnc₁ : LatticeNonCollinear q₁ r₁)
    (hnc₂ : LatticeNonCollinear q₂ r₂)
    (hdirections : LatticeNonCollinear (r₁ - q₁) (r₂ - q₂))
    (hq₁ : VanishesAt D q₁) (hr₁ : VanishesAt D r₁)
    (hq₂ : VanishesAt D q₂) (hr₂ : VanishesAt D r₂) :
    VanishesAt D p := by
  apply target_vanishes_of_two_known_parent_triads D hD p q₁ r₁ q₂ r₂
    hsum₁ hsum₂ hnc₁ hnc₂
  · exact lattice_not_parallel_of_noncollinear hdirections
  · exact hq₁
  · exact hr₁
  · exact hq₂
  · exact hr₂

/-! ## Well-founded lattice propagation -/

/-- The coordinate unit cube used for the finite seed. -/
def InUnitCube (k : LatticeVec) : Prop :=
  ∀ i, (k i).natAbs ≤ 1

/-- A mode lies on a coordinate axis. The zero mode also satisfies this
predicate, but is separately excluded wherever the distinction matters. -/
def IsAxisMode (k : LatticeVec) : Prop :=
  (k 0 = 0 ∧ k 1 = 0) ∨ (k 0 = 0 ∧ k 2 = 0) ∨ (k 1 = 0 ∧ k 2 = 0)

instance (k : LatticeVec) : Decidable (IsAxisMode k) := by
  unfold IsAxisMode
  infer_instance

/-- The well-founded order implicit in Section 7.2: first by the `ℓ¹`
shell, then with non-axis modes before axis modes in the same shell. -/
def latticeL1 (k : LatticeVec) : Nat :=
  (k 0).natAbs + (k 1).natAbs + (k 2).natAbs

def propagationMeasure (k : LatticeVec) : Nat :=
  2 * latticeL1 k +
    if IsAxisMode k then 1 else 0

theorem propagationMeasure_lt_of_l1_lt {q t : LatticeVec}
    (h : latticeL1 q < latticeL1 t) :
    propagationMeasure q < propagationMeasure t := by
  simp only [propagationMeasure]
  split <;> split <;> omega

theorem propagationMeasure_nonaxis_lt_axis {q t : LatticeVec}
    (hl1 : latticeL1 q = latticeL1 t)
    (hq : ¬ IsAxisMode q) (ht : IsAxisMode t) :
    propagationMeasure q < propagationMeasure t := by
  simp [propagationMeasure, hl1, hq, ht]

def latticeVec (x y z : ℤ) : LatticeVec := ![x, y, z]

theorem latticeVec_coordinates (k : LatticeVec) :
    latticeVec (k 0) (k 1) (k 2) = k := by
  funext i
  fin_cases i <;> rfl

theorem natAbs_sub_sign_add_one (x : ℤ) (hx : x ≠ 0) :
    (x - x.sign).natAbs + 1 = x.natAbs := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hs : x.sign = -1 := Int.sign_eq_neg_one_iff_neg.mpr hxneg
    rw [hs]
    have hnx : 0 ≤ -x := by omega
    have hnx1 : 0 ≤ -(x + 1) := by omega
    have heq : x - (-1) = x + 1 := by ring
    rw [heq, ← Int.natAbs_neg x, ← Int.natAbs_neg (x + 1)]
    have h0 := Int.natAbs_of_nonneg hnx
    have h1 := Int.natAbs_of_nonneg hnx1
    omega
  · have hs : x.sign = 1 := Int.sign_eq_one_iff_pos.mpr hxpos
    rw [hs]
    have hx0 : 0 ≤ x := by omega
    have hx1 : 0 ≤ x - 1 := by omega
    have h0 := Int.natAbs_of_nonneg hx0
    have h1 := Int.natAbs_of_nonneg hx1
    omega

theorem sign_ne_zero_of_ne_zero {x : ℤ} (hx : x ≠ 0) : x.sign ≠ 0 := by
  exact fun hs ↦ hx (Int.sign_eq_zero_iff_zero.mp hs)

theorem latticeL1_step_first (x y z : ℤ) (hx : x ≠ 0) :
    latticeL1 (latticeVec (x - x.sign) y z) < latticeL1 (latticeVec x y z) := by
  have h := natAbs_sub_sign_add_one x hx
  simp [latticeL1, latticeVec]
  omega

theorem latticeL1_step_second (x y z : ℤ) (hy : y ≠ 0) :
    latticeL1 (latticeVec x (y - y.sign) z) < latticeL1 (latticeVec x y z) := by
  have h := natAbs_sub_sign_add_one y hy
  simp [latticeL1, latticeVec]
  omega

theorem latticeL1_step_third (x y z : ℤ) (hz : z ≠ 0) :
    latticeL1 (latticeVec x y (z - z.sign)) < latticeL1 (latticeVec x y z) := by
  have h := natAbs_sub_sign_add_one z hz
  simp [latticeL1, latticeVec]
  omega

theorem not_axisMode_of_first_second_ne_zero (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) : ¬ IsAxisMode (latticeVec x y z) := by
  simp [IsAxisMode, latticeVec, hx, hy]

theorem xy_first_parents_noncollinear (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    LatticeNonCollinear (latticeVec (x - x.sign) y z)
      (latticeVec x.sign 0 0) := by
  intro hzero
  have h₂ := congrFun hzero 2
  simp [Vec3.cross, latticeToReal, latticeVec] at h₂
  exact hy (h₂.resolve_right hx)

theorem xy_second_parents_noncollinear (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    LatticeNonCollinear (latticeVec x (y - y.sign) z)
      (latticeVec 0 y.sign 0) := by
  intro hzero
  have h₂ := congrFun hzero 2
  simp [Vec3.cross, latticeToReal, latticeVec] at h₂
  exact hx (h₂.resolve_right hy)

theorem sign_sq_of_ne_zero (x : ℤ) (hx : x ≠ 0) : x.sign * x.sign = 1 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [Int.sign_eq_neg_one_iff_neg.mpr hxneg]
    norm_num
  · rw [Int.sign_eq_one_iff_pos.mpr hxpos]
    norm_num

theorem xy_difference_directions_noncollinear (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hlarge : 2 < x.natAbs + y.natAbs + z.natAbs) :
    LatticeNonCollinear
      (latticeVec x.sign 0 0 - latticeVec (x - x.sign) y z)
      (latticeVec 0 y.sign 0 - latticeVec x (y - y.sign) z) := by
  intro hzero
  by_cases hz : z = 0
  · have h₂ := congrFun hzero 2
    simp [Vec3.cross, latticeToReal, latticeVec, hz] at h₂
    have hsx := sign_sq_of_ne_zero x hx
    have hsy := sign_sq_of_ne_zero y hy
    have habsx := Int.sign_mul_self_eq_natAbs x
    have habsy := Int.sign_mul_self_eq_natAbs y
    have hzabs : z.natAbs = 0 := Int.natAbs_eq_zero.mpr hz
    have hsxR : (x.sign : ℝ) * (x.sign : ℝ) = 1 := by exact_mod_cast hsx
    have hsyR : (y.sign : ℝ) * (y.sign : ℝ) = 1 := by exact_mod_cast hsy
    have habsxR : (x.sign : ℝ) * (x : ℝ) = (x.natAbs : ℝ) := by
      have hcast := congrArg (fun n : ℤ ↦ (n : ℝ)) habsx
      push_cast at hcast
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    have habsyR : (y.sign : ℝ) * (y : ℝ) = (y.natAbs : ℝ) := by
      have hcast := congrArg (fun n : ℤ ↦ (n : ℝ)) habsy
      push_cast at hcast
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    have heq : (4 : ℝ) * x.sign * y.sign - 2 * x.sign * y -
        2 * y.sign * x = 0 := by
      linear_combination h₂
    have heq₁ : (4 : ℝ) * y.sign - 2 * y -
        2 * y.sign * (x.sign * x) = 0 := by
      linear_combination (x.sign : ℝ) * heq -
        ((4 : ℝ) * y.sign - 2 * y) * hsxR
    have heq₂ : (4 : ℝ) - 2 * (x.sign * x) - 2 * (y.sign * y) = 0 := by
      linear_combination (y.sign : ℝ) * heq₁ +
        (2 * (x.sign : ℝ) * x - 4) * hsyR
    have hkey : (4 : ℝ) - 2 * x.natAbs - 2 * y.natAbs = 0 := by
      linear_combination heq₂ + 2 * habsxR + 2 * habsyR
    have habR : (x.natAbs : ℝ) + y.natAbs = 2 := by nlinarith [hkey]
    have habN : x.natAbs + y.natAbs = 2 := by exact_mod_cast habR
    omega
  · have h₀ := congrFun hzero 0
    simp [Vec3.cross, latticeToReal, latticeVec] at h₀
    ring_nf at h₀
    have heq : (y.sign : ℝ) * (z : ℝ) = 0 := by nlinarith [h₀]
    have hsyR : (y.sign : ℝ) ≠ 0 := by
      exact_mod_cast sign_ne_zero_of_ne_zero hy
    have hzR : (z : ℝ) ≠ 0 := by exact_mod_cast hz
    exact (mul_ne_zero hsyR hzR) heq

theorem l1_gt_two_of_not_unitCube_xy (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcube : ¬ InUnitCube (latticeVec x y z)) :
    2 < x.natAbs + y.natAbs + z.natAbs := by
  by_contra hlarge
  apply hcube
  intro i
  have hxpos : 0 < x.natAbs := Int.natAbs_pos.mpr hx
  have hypos : 0 < y.natAbs := Int.natAbs_pos.mpr hy
  fin_cases i <;> (simp [latticeVec]; omega)

theorem latticeVec_ne_zero_of_first_ne {x y z : ℤ} (hx : x ≠ 0) :
    latticeVec x y z ≠ 0 := by
  intro h
  have h₀ := congrFun h 0
  simp [latticeVec] at h₀
  exact hx h₀

theorem latticeVec_ne_zero_of_second_ne {x y z : ℤ} (hy : y ≠ 0) :
    latticeVec x y z ≠ 0 := by
  intro h
  have h₁ := congrFun h 1
  simp [latticeVec] at h₁
  exact hy h₁

/-- All arithmetic and geometry required for one shell-propagation step,
packaged independently of the multiplier. -/
structure PropagationCertificate (t : LatticeVec) where
  q₁ : LatticeVec
  r₁ : LatticeVec
  q₂ : LatticeVec
  r₂ : LatticeVec
  sum₁ : q₁ + r₁ = t
  sum₂ : q₂ + r₂ = t
  q₁_ne : q₁ ≠ 0
  r₁_ne : r₁ ≠ 0
  q₂_ne : q₂ ≠ 0
  r₂_ne : r₂ ≠ 0
  q₁_lt : propagationMeasure q₁ < propagationMeasure t
  r₁_lt : propagationMeasure r₁ < propagationMeasure t
  q₂_lt : propagationMeasure q₂ < propagationMeasure t
  r₂_lt : propagationMeasure r₂ < propagationMeasure t
  noncollinear₁ : LatticeNonCollinear q₁ r₁
  noncollinear₂ : LatticeNonCollinear q₂ r₂
  directions : LatticeNonCollinear (r₁ - q₁) (r₂ - q₂)

def propagationCertificate_xy (x y z : ℤ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hcube : ¬ InUnitCube (latticeVec x y z)) :
    PropagationCertificate (latticeVec x y z) := by
  have hlarge := l1_gt_two_of_not_unitCube_xy x y z hx hy hcube
  refine
    { q₁ := latticeVec (x - x.sign) y z
      r₁ := latticeVec x.sign 0 0
      q₂ := latticeVec x (y - y.sign) z
      r₂ := latticeVec 0 y.sign 0
      sum₁ := ?_
      sum₂ := ?_
      q₁_ne := latticeVec_ne_zero_of_second_ne hy
      r₁_ne := latticeVec_ne_zero_of_first_ne (sign_ne_zero_of_ne_zero hx)
      q₂_ne := latticeVec_ne_zero_of_first_ne hx
      r₂_ne := latticeVec_ne_zero_of_second_ne (sign_ne_zero_of_ne_zero hy)
      q₁_lt := propagationMeasure_lt_of_l1_lt
        (latticeL1_step_first x y z hx)
      r₁_lt := ?_
      q₂_lt := propagationMeasure_lt_of_l1_lt
        (latticeL1_step_second x y z hy)
      r₂_lt := ?_
      noncollinear₁ := xy_first_parents_noncollinear x y z hx hy
      noncollinear₂ := xy_second_parents_noncollinear x y z hx hy
      directions := xy_difference_directions_noncollinear x y z hx hy hlarge }
  · funext i
    fin_cases i <;> simp [latticeVec]
  · funext i
    fin_cases i <;> simp [latticeVec]
  · apply propagationMeasure_lt_of_l1_lt
    have hxpos : 0 < x.natAbs := Int.natAbs_pos.mpr hx
    have hypos : 0 < y.natAbs := Int.natAbs_pos.mpr hy
    simp [latticeL1, latticeVec, Int.natAbs_sign_of_ne_zero hx]
    omega
  · apply propagationMeasure_lt_of_l1_lt
    have hxpos : 0 < x.natAbs := Int.natAbs_pos.mpr hx
    have hypos : 0 < y.natAbs := Int.natAbs_pos.mpr hy
    simp [latticeL1, latticeVec, Int.natAbs_sign_of_ne_zero hy]
    omega

def swapYZ (k : LatticeVec) : LatticeVec := latticeVec (k 0) (k 2) (k 1)

@[simp] theorem swapYZ_latticeVec (x y z : ℤ) :
    swapYZ (latticeVec x y z) = latticeVec x z y := by
  rfl

@[simp] theorem swapYZ_zero : swapYZ 0 = 0 := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem swapYZ_add (q r : LatticeVec) : swapYZ (q + r) = swapYZ q + swapYZ r := by
  funext i
  fin_cases i <;> simp [swapYZ, latticeVec]

@[simp] theorem swapYZ_neg (q : LatticeVec) : swapYZ (-q) = -swapYZ q := by
  funext i
  fin_cases i <;> simp [swapYZ, latticeVec]

@[simp] theorem swapYZ_sub (q r : LatticeVec) : swapYZ (q - r) = swapYZ q - swapYZ r := by
  simp [sub_eq_add_neg]

@[simp] theorem swapYZ_swapYZ (q : LatticeVec) : swapYZ (swapYZ q) = q := by
  funext i
  fin_cases i <;> rfl

theorem swapYZ_ne_zero {q : LatticeVec} (hq : q ≠ 0) : swapYZ q ≠ 0 := by
  intro h
  apply hq
  rw [← swapYZ_swapYZ q, h, swapYZ_zero]

theorem swapYZ_axis_iff (q : LatticeVec) : IsAxisMode (swapYZ q) ↔ IsAxisMode q := by
  simp [IsAxisMode, swapYZ, latticeVec]
  tauto

@[simp] theorem latticeL1_swapYZ (q : LatticeVec) : latticeL1 (swapYZ q) = latticeL1 q := by
  simp [latticeL1, swapYZ, latticeVec]
  omega

@[simp] theorem propagationMeasure_swapYZ (q : LatticeVec) :
    propagationMeasure (swapYZ q) = propagationMeasure q := by
  simp [propagationMeasure, swapYZ_axis_iff]

theorem noncollinear_swapYZ {q r : LatticeVec} (h : LatticeNonCollinear q r) :
    LatticeNonCollinear (swapYZ q) (swapYZ r) := by
  intro hzero
  apply h
  funext i
  have h₀ := congrFun hzero 0
  have h₁ := congrFun hzero 1
  have h₂ := congrFun hzero 2
  fin_cases i <;>
    simp [Vec3.cross, latticeToReal, swapYZ, latticeVec] at h₀ h₁ h₂ ⊢ <;>
    linarith

def PropagationCertificate.permuteYZ {t : LatticeVec}
    (c : PropagationCertificate t) : PropagationCertificate (swapYZ t) where
  q₁ := swapYZ c.q₁
  r₁ := swapYZ c.r₁
  q₂ := swapYZ c.q₂
  r₂ := swapYZ c.r₂
  sum₁ := by rw [← swapYZ_add, c.sum₁]
  sum₂ := by rw [← swapYZ_add, c.sum₂]
  q₁_ne := swapYZ_ne_zero c.q₁_ne
  r₁_ne := swapYZ_ne_zero c.r₁_ne
  q₂_ne := swapYZ_ne_zero c.q₂_ne
  r₂_ne := swapYZ_ne_zero c.r₂_ne
  q₁_lt := by simpa using c.q₁_lt
  r₁_lt := by simpa using c.r₁_lt
  q₂_lt := by simpa using c.q₂_lt
  r₂_lt := by simpa using c.r₂_lt
  noncollinear₁ := noncollinear_swapYZ c.noncollinear₁
  noncollinear₂ := noncollinear_swapYZ c.noncollinear₂
  directions := by
    rw [← swapYZ_sub, ← swapYZ_sub]
    exact noncollinear_swapYZ c.directions

def propagationCertificate_xz (x y z : ℤ)
    (hx : x ≠ 0) (hz : z ≠ 0)
    (hcube : ¬ InUnitCube (latticeVec x y z)) :
    PropagationCertificate (latticeVec x y z) := by
  have hcube' : ¬ InUnitCube (latticeVec x z y) := by
    intro h
    apply hcube
    intro i
    have h' := h
    fin_cases i
    · simpa [latticeVec] using h' 0
    · simpa [latticeVec] using h' 2
    · simpa [latticeVec] using h' 1
  exact (propagationCertificate_xy x z y hx hz hcube').permuteYZ

def swapXY (k : LatticeVec) : LatticeVec := latticeVec (k 1) (k 0) (k 2)

@[simp] theorem swapXY_latticeVec (x y z : ℤ) :
    swapXY (latticeVec x y z) = latticeVec y x z := by
  rfl

@[simp] theorem swapXY_zero : swapXY 0 = 0 := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem swapXY_add (q r : LatticeVec) : swapXY (q + r) = swapXY q + swapXY r := by
  funext i
  fin_cases i <;> simp [swapXY, latticeVec]

@[simp] theorem swapXY_neg (q : LatticeVec) : swapXY (-q) = -swapXY q := by
  funext i
  fin_cases i <;> simp [swapXY, latticeVec]

@[simp] theorem swapXY_sub (q r : LatticeVec) : swapXY (q - r) = swapXY q - swapXY r := by
  simp [sub_eq_add_neg]

@[simp] theorem swapXY_swapXY (q : LatticeVec) : swapXY (swapXY q) = q := by
  funext i
  fin_cases i <;> rfl

theorem swapXY_ne_zero {q : LatticeVec} (hq : q ≠ 0) : swapXY q ≠ 0 := by
  intro h
  apply hq
  rw [← swapXY_swapXY q, h, swapXY_zero]

theorem swapXY_axis_iff (q : LatticeVec) : IsAxisMode (swapXY q) ↔ IsAxisMode q := by
  simp [IsAxisMode, swapXY, latticeVec]
  tauto

@[simp] theorem latticeL1_swapXY (q : LatticeVec) : latticeL1 (swapXY q) = latticeL1 q := by
  simp [latticeL1, swapXY, latticeVec]
  omega

@[simp] theorem propagationMeasure_swapXY (q : LatticeVec) :
    propagationMeasure (swapXY q) = propagationMeasure q := by
  simp [propagationMeasure, swapXY_axis_iff]

theorem noncollinear_swapXY {q r : LatticeVec} (h : LatticeNonCollinear q r) :
    LatticeNonCollinear (swapXY q) (swapXY r) := by
  intro hzero
  apply h
  funext i
  have h₀ := congrFun hzero 0
  have h₁ := congrFun hzero 1
  have h₂ := congrFun hzero 2
  fin_cases i <;>
    simp [Vec3.cross, latticeToReal, swapXY, latticeVec] at h₀ h₁ h₂ ⊢ <;>
    linarith

def PropagationCertificate.permuteXY {t : LatticeVec}
    (c : PropagationCertificate t) : PropagationCertificate (swapXY t) where
  q₁ := swapXY c.q₁
  r₁ := swapXY c.r₁
  q₂ := swapXY c.q₂
  r₂ := swapXY c.r₂
  sum₁ := by rw [← swapXY_add, c.sum₁]
  sum₂ := by rw [← swapXY_add, c.sum₂]
  q₁_ne := swapXY_ne_zero c.q₁_ne
  r₁_ne := swapXY_ne_zero c.r₁_ne
  q₂_ne := swapXY_ne_zero c.q₂_ne
  r₂_ne := swapXY_ne_zero c.r₂_ne
  q₁_lt := by simpa using c.q₁_lt
  r₁_lt := by simpa using c.r₁_lt
  q₂_lt := by simpa using c.q₂_lt
  r₂_lt := by simpa using c.r₂_lt
  noncollinear₁ := noncollinear_swapXY c.noncollinear₁
  noncollinear₂ := noncollinear_swapXY c.noncollinear₂
  directions := by
    rw [← swapXY_sub, ← swapXY_sub]
    exact noncollinear_swapXY c.directions

def propagationCertificate_yz (x y z : ℤ)
    (hy : y ≠ 0) (hz : z ≠ 0)
    (hcube : ¬ InUnitCube (latticeVec x y z)) :
    PropagationCertificate (latticeVec x y z) := by
  have hcube' : ¬ InUnitCube (latticeVec y z x) := by
    intro h
    apply hcube
    intro i
    have h' := h
    fin_cases i
    · simpa [latticeVec] using h' 2
    · simpa [latticeVec] using h' 0
    · simpa [latticeVec] using h' 1
  exact ((propagationCertificate_xy y z x hy hz hcube').permuteYZ).permuteXY

def propagationCertificate_nonaxis (x y z : ℤ)
    (haxis : ¬ IsAxisMode (latticeVec x y z))
    (hcube : ¬ InUnitCube (latticeVec x y z)) :
    PropagationCertificate (latticeVec x y z) := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      apply haxis
      simp [IsAxisMode, latticeVec, hx, hy]
    have hz : z ≠ 0 := by
      intro hz
      apply haxis
      simp [IsAxisMode, latticeVec, hx, hz]
    exact propagationCertificate_yz x y z hy hz hcube
  · by_cases hy : y = 0
    · have hz : z ≠ 0 := by
        intro hz
        apply haxis
        simp [IsAxisMode, latticeVec, hy, hz]
      exact propagationCertificate_xz x y z hx hz hcube
    · exact propagationCertificate_xy x y z hx hy hcube

theorem natAbs_gt_one_of_axis_x_not_unitCube (x : ℤ)
    (hcube : ¬ InUnitCube (latticeVec x 0 0)) : 1 < x.natAbs := by
  by_contra h
  apply hcube
  intro i
  fin_cases i <;> simp [latticeVec] <;> omega

def propagationCertificate_axis_x (x : ℤ) (hx : x ≠ 0)
    (hcube : ¬ InUnitCube (latticeVec x 0 0)) :
    PropagationCertificate (latticeVec x 0 0) := by
  have hlarge := natAbs_gt_one_of_axis_x_not_unitCube x hcube
  have hdec := natAbs_sub_sign_add_one x hx
  have hstep : x - x.sign ≠ 0 := by
    intro hzero
    have := Int.natAbs_eq_zero.mpr hzero
    omega
  refine
    { q₁ := latticeVec (x - x.sign) 1 0
      r₁ := latticeVec x.sign (-1) 0
      q₂ := latticeVec (x - x.sign) 0 1
      r₂ := latticeVec x.sign 0 (-1)
      sum₁ := ?_
      sum₂ := ?_
      q₁_ne := latticeVec_ne_zero_of_first_ne hstep
      r₁_ne := latticeVec_ne_zero_of_first_ne (sign_ne_zero_of_ne_zero hx)
      q₂_ne := latticeVec_ne_zero_of_first_ne hstep
      r₂_ne := latticeVec_ne_zero_of_first_ne (sign_ne_zero_of_ne_zero hx)
      q₁_lt := ?_
      r₁_lt := ?_
      q₂_lt := ?_
      r₂_lt := ?_
      noncollinear₁ := ?_
      noncollinear₂ := ?_
      directions := ?_ }
  · funext i
    fin_cases i <;> simp [latticeVec]
  · funext i
    fin_cases i <;> simp [latticeVec]
  · apply propagationMeasure_nonaxis_lt_axis
    · simp [latticeL1, latticeVec]
      omega
    · simp [IsAxisMode, latticeVec, hstep]
    · simp [IsAxisMode, latticeVec]
  · simp [propagationMeasure, latticeL1, IsAxisMode, latticeVec,
      Int.natAbs_sign_of_ne_zero hx, Int.sign_eq_zero_iff_zero, hx]
    omega
  · apply propagationMeasure_nonaxis_lt_axis
    · simp [latticeL1, latticeVec]
      omega
    · simp [IsAxisMode, latticeVec, hstep]
    · simp [IsAxisMode, latticeVec]
  · simp [propagationMeasure, latticeL1, IsAxisMode, latticeVec,
      Int.natAbs_sign_of_ne_zero hx, Int.sign_eq_zero_iff_zero, hx]
    omega
  · intro hzero
    have h₂ := congrFun hzero 2
    simp [Vec3.cross, latticeToReal, latticeVec] at h₂
    exact hx h₂
  · intro hzero
    have h₁ := congrFun hzero 1
    simp [Vec3.cross, latticeToReal, latticeVec] at h₁
    exact hx h₁
  · intro hzero
    have h₀ := congrFun hzero 0
    norm_num [Vec3.cross, latticeToReal, latticeVec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] at h₀

def propagationCertificate_axis_y (y : ℤ) (hy : y ≠ 0)
    (hcube : ¬ InUnitCube (latticeVec 0 y 0)) :
    PropagationCertificate (latticeVec 0 y 0) := by
  have hcube' : ¬ InUnitCube (latticeVec y 0 0) := by
    intro h
    apply hcube
    intro i
    have h' := h
    fin_cases i
    · simpa [latticeVec] using h' 1
    · simpa [latticeVec] using h' 0
    · simpa [latticeVec] using h' 2
  exact (propagationCertificate_axis_x y hy hcube').permuteXY

def propagationCertificate_axis_z (z : ℤ) (hz : z ≠ 0)
    (hcube : ¬ InUnitCube (latticeVec 0 0 z)) :
    PropagationCertificate (latticeVec 0 0 z) := by
  have hcube' : ¬ InUnitCube (latticeVec z 0 0) := by
    intro h
    apply hcube
    intro i
    have h' := h
    fin_cases i
    · simpa [latticeVec] using h' 1
    · simpa [latticeVec] using h' 2
    · simpa [latticeVec] using h' 0
  exact ((propagationCertificate_axis_x z hz hcube').permuteXY).permuteYZ

def propagationCertificate_axis (x y z : ℤ)
    (hne : latticeVec x y z ≠ 0)
    (haxis : IsAxisMode (latticeVec x y z))
    (hcube : ¬ InUnitCube (latticeVec x y z)) :
    PropagationCertificate (latticeVec x y z) := by
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · have hz : z ≠ 0 := by
        intro hz
        apply hne
        funext i
        fin_cases i <;> simp [latticeVec, hx, hy, hz]
      simpa [hx, hy] using propagationCertificate_axis_z z hz (by
        simpa [hx, hy] using hcube)
    · have hz : z = 0 := by
        simp [IsAxisMode, latticeVec, hx, hy] at haxis
        exact haxis
      simpa [hx, hz] using propagationCertificate_axis_y y hy (by
        simpa [hx, hz] using hcube)
  · have hyz : y = 0 ∧ z = 0 := by
      simp [IsAxisMode, latticeVec, hx] at haxis
      exact haxis
    simpa [hyz.1, hyz.2] using propagationCertificate_axis_x x hx (by
      simpa [hyz.1, hyz.2] using hcube)

/-- The concrete lattice certificate promised in Section 7.2, for every
nonzero mode outside the unit cube. -/
def latticePropagationCertificate (t : LatticeVec) (ht : t ≠ 0)
    (hcube : ¬ InUnitCube t) : PropagationCertificate t := by
  rw [← latticeVec_coordinates t] at ht hcube ⊢
  by_cases haxis : IsAxisMode (latticeVec (t 0) (t 1) (t 2))
  · exact propagationCertificate_axis (t 0) (t 1) (t 2) ht haxis hcube
  · exact propagationCertificate_nonaxis (t 0) (t 1) (t 2) haxis hcube

theorem neg_add_parents_eq_zero {t q r : LatticeVec} (h : q + r = t) :
    -t + q + r = 0 := by
  rw [← h]
  abel

/-- Once the elementary integer certificates are supplied, the local
two-triad lemma propagates zero seed data through the entire lattice. -/
theorem vanishes_everywhere_of_seed_and_propagation
    (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) (hreal : RealityCompatibleMap D)
    (hseed : ∀ k, k ≠ 0 → InUnitCube k → VanishesAt D k)
    (hcert : ∀ t, t ≠ 0 → ¬ InUnitCube t → PropagationCertificate t) :
    ∀ k, k ≠ 0 → VanishesAt D k := by
  intro k hk
  generalize hn : propagationMeasure k = n
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
      by_cases hcube : InUnitCube k
      · exact hseed k hk hcube
      · let c := hcert k hk hcube
        have hq₁lt : propagationMeasure c.q₁ < n := by simpa [← hn] using c.q₁_lt
        have hr₁lt : propagationMeasure c.r₁ < n := by simpa [← hn] using c.r₁_lt
        have hq₂lt : propagationMeasure c.q₂ < n := by simpa [← hn] using c.q₂_lt
        have hr₂lt : propagationMeasure c.r₂ < n := by simpa [← hn] using c.r₂_lt
        have hq₁ : VanishesAt D c.q₁ := ih _ hq₁lt c.q₁ c.q₁_ne rfl
        have hr₁ : VanishesAt D c.r₁ := ih _ hr₁lt c.r₁ c.r₁_ne rfl
        have hq₂ : VanishesAt D c.q₂ := ih _ hq₂lt c.q₂ c.q₂_ne rfl
        have hr₂ : VanishesAt D c.r₂ := ih _ hr₂lt c.r₂ c.r₂_ne rfl
        have hneg : VanishesAt D (-k) :=
          target_vanishes_of_two_known_parent_triads_lattice D htriad (-k)
            c.q₁ c.r₁ c.q₂ c.r₂
            (neg_add_parents_eq_zero c.sum₁)
            (neg_add_parents_eq_zero c.sum₂)
            c.noncollinear₁ c.noncollinear₂ c.directions
            hq₁ hr₁ hq₂ hr₂
        exact (vanishesAt_neg_iff_of_reality D hreal k).mp hneg

/-- Complete Section 7.2 propagation: vanishing on the nonzero coordinate
unit cube forces vanishing on every nonzero lattice fiber. -/
theorem vanishes_everywhere_of_unitCube
    (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) (hreal : RealityCompatibleMap D)
    (hseed : ∀ k, k ≠ 0 → InUnitCube k → VanishesAt D k) :
    ∀ k, k ≠ 0 → VanishesAt D k :=
  vanishes_everywhere_of_seed_and_propagation D htriad hreal hseed
    latticePropagationCertificate

/-! ## Semantic use of the finite seed certificate -/

abbrev SeedParameter := Fin 156 → ℝ

def seedPivotColumn (i : Fin 144) : Fin 156 :=
  ⟨SeedCertificate.selectedColumns.getD i 0,
    SeedCertificate.selectedColumn_lt i⟩

def selectedSeedMatrix : Matrix (Fin 144) (Fin 156) ℝ :=
  fun i j ↦
    ((SeedCertificate.rowsZ.getD
      (SeedCertificate.selectedRows.getD i 0) #[]).getD j 0 : ℝ)

theorem selectedSeedMatrix_minor :
    selectedSeedMatrix.submatrix id seedPivotColumn =
      SeedCertificate.minorMatrixR := by
  set_option maxRecDepth 100000 in
  rfl

theorem selectedSeedMatrix_rank : selectedSeedMatrix.rank = 144 := by
  have hminor : SeedCertificate.minorMatrixR.rank = 144 :=
    Matrix.rank_of_det_ne_zero SeedCertificate.minorMatrixR_det_ne_zero
  have hlower : 144 ≤ selectedSeedMatrix.rank := by
    have hle := Matrix.rank_submatrix_le selectedSeedMatrix id seedPivotColumn
    rw [selectedSeedMatrix_minor, hminor] at hle
    exact hle
  have hupper : selectedSeedMatrix.rank ≤ 144 := by
    simpa using Matrix.rank_le_card_height selectedSeedMatrix
  omega

def selectedSeedConstraints : SeedParameter →ₗ[ℝ] (Fin 144 → ℝ) :=
  selectedSeedMatrix.mulVecLin

theorem selectedSeedConstraints_surjective :
    Function.Surjective selectedSeedConstraints := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  change selectedSeedMatrix.rank = Module.finrank ℝ (Fin 144 → ℝ)
  rw [selectedSeedMatrix_rank]
  simp

theorem selectedSeedKernel_finrank :
    Module.finrank ℝ (LinearMap.ker selectedSeedConstraints) = 12 := by
  have hrange : Module.finrank ℝ (LinearMap.range selectedSeedConstraints) = 144 := by
    rw [LinearMap.range_eq_top.mpr selectedSeedConstraints_surjective]
    simp
  have hrankNull := selectedSeedConstraints.finrank_range_add_finrank_ker
  simp only [Module.finrank_fin_fun, Fintype.card_fin] at hrankNull
  omega

theorem selectedSeedMatrix_eq_rational_cast :
    selectedSeedMatrix =
      SeedCertificate.selectedConstraintFullMatrixQ.map (fun x ↦ (x : ℝ)) := by
  ext i j
  simp [selectedSeedMatrix, SeedCertificate.selectedConstraintFullMatrixQ,
    SeedCertificate.selectedConstraintEntryQ]

def seedGeneratorLinear : (Fin 12 → ℝ) →ₗ[ℝ] SeedParameter :=
  SeedCertificate.generatorMatrixR.mulVecLin

def seedGeneratorSelectedRow (i : Fin 12) : Fin 156 :=
  ⟨SeedCertificate.selectedGeneratorRows.getD i 0, by native_decide +revert⟩

def seedGeneratorSelectedColumn (i : Fin 12) : Fin 12 :=
  ⟨SeedCertificate.selectedGeneratorColumns.getD i 0, by native_decide +revert⟩

theorem seedGeneratorMatrix_minor :
    SeedCertificate.generatorMatrixR.submatrix seedGeneratorSelectedRow
      seedGeneratorSelectedColumn = SeedCertificate.generatorMinorR := by
  set_option maxRecDepth 100000 in
  rfl

theorem seedGeneratorMatrix_rank : SeedCertificate.generatorMatrixR.rank = 12 := by
  have hminor : SeedCertificate.generatorMinorR.rank = 12 :=
    Matrix.rank_of_det_ne_zero SeedCertificate.generatorMinorR_det_ne_zero
  have hlower : 12 ≤ SeedCertificate.generatorMatrixR.rank := by
    have hle := Matrix.rank_submatrix_le SeedCertificate.generatorMatrixR
      seedGeneratorSelectedRow seedGeneratorSelectedColumn
    rw [seedGeneratorMatrix_minor, hminor] at hle
    exact hle
  have hupper : SeedCertificate.generatorMatrixR.rank ≤ 12 := by
    simpa using Matrix.rank_le_card_width SeedCertificate.generatorMatrixR
  omega

theorem selectedSeedMatrix_mul_generatorMatrix :
    selectedSeedMatrix * SeedCertificate.generatorMatrixR = 0 := by
  have hQ := SeedCertificate.selected_constraints_annihilate_generators
  have hcast := congrArg
    (fun M ↦ M.map (Rat.castHom ℝ)) hQ
  rw [selectedSeedMatrix_eq_rational_cast]
  unfold SeedCertificate.generatorMatrixR
  change (SeedCertificate.selectedConstraintFullMatrixQ.map (Rat.castHom ℝ)) *
      (SeedCertificate.generatorMatrixQ.map (Rat.castHom ℝ)) = 0
  rw [← Matrix.map_mul]
  rw [Matrix.map_zero (Rat.castHom ℝ) (Rat.castHom ℝ).map_zero] at hcast
  exact hcast

theorem selectedSeedConstraints_comp_seedGeneratorLinear :
    selectedSeedConstraints.comp seedGeneratorLinear = 0 := by
  apply LinearMap.ext
  intro x
  change Matrix.mulVec selectedSeedMatrix
      (Matrix.mulVec SeedCertificate.generatorMatrixR x) = (0 : Fin 144 → ℝ)
  rw [Matrix.mulVec_mulVec x selectedSeedMatrix SeedCertificate.generatorMatrixR,
    selectedSeedMatrix_mul_generatorMatrix]
  simp

theorem seedGeneratorRange_le_selectedSeedKernel :
    LinearMap.range seedGeneratorLinear ≤ LinearMap.ker selectedSeedConstraints := by
  rw [LinearMap.range_le_ker_iff]
  exact selectedSeedConstraints_comp_seedGeneratorLinear

theorem seedGeneratorRange_finrank :
    Module.finrank ℝ (LinearMap.range seedGeneratorLinear) = 12 := by
  change SeedCertificate.generatorMatrixR.rank = 12
  exact seedGeneratorMatrix_rank

theorem selectedSeedKernel_eq_generatorRange :
    LinearMap.ker selectedSeedConstraints = LinearMap.range seedGeneratorLinear := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq seedGeneratorRange_le_selectedSeedKernel
  rw [seedGeneratorRange_finrank, selectedSeedKernel_finrank]

theorem seed_parameter_is_generator (x : SeedParameter)
    (hx : selectedSeedConstraints x = 0) :
    ∃ g : Fin 12 → ℝ, seedGeneratorLinear g = x := by
  have hxker : x ∈ LinearMap.ker selectedSeedConstraints := hx
  rw [selectedSeedKernel_eq_generatorRange] at hxker
  exact hxker

def latticeOfIVec (x : SeedCertificate.IVec) : LatticeVec :=
  latticeVec x.1 x.2.1 x.2.2

def realOfIVec (x : SeedCertificate.IVec) : RVec :=
  ![(x.1 : ℝ), (x.2.1 : ℝ), (x.2.2 : ℝ)]

@[simp] theorem latticeToReal_latticeOfIVec (x : SeedCertificate.IVec) :
    latticeToReal (latticeOfIVec x) = realOfIVec x := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem latticeToComplex_latticeOfIVec (x : SeedCertificate.IVec) :
    latticeToComplex (latticeOfIVec x) = realToComplexVec (realOfIVec x) := by
  funext i
  fin_cases i <;> rfl

def seedModeIVec (mode : Nat) : SeedCertificate.IVec :=
  SeedCertificate.representatives.getD mode SeedCertificate.zero

def seedFrameIVec (mode input : Nat) : SeedCertificate.IVec :=
  (SeedCertificate.frame (seedModeIVec mode)).getD input SeedCertificate.zero

def explicitSeedFrames : List (SeedCertificate.IVec × SeedCertificate.IVec) :=
  [((0, 1, 0), (-1, 0, 0)), ((0, -1, -1), (-2, 0, 0)),
   ((0, 0, -1), (-1, 0, 0)), ((0, 1, -1), (-2, 0, 0)),
   ((0, -1, 1), (-2, -1, -1)), ((0, 0, 1), (-1, -1, 0)),
   ((0, 1, 1), (-2, -1, 1)), ((0, -1, 0), (-1, 0, -1)),
   ((0, 0, 1), (0, -1, 0)), ((0, 1, 0), (-1, 0, 1)),
   ((0, -1, -1), (-2, 1, -1)), ((0, 0, -1), (-1, 1, 0)),
   ((0, 1, -1), (-2, 1, 1))]

def explicitSeedFrameIVec (mode input : Nat) : SeedCertificate.IVec :=
  let pair := explicitSeedFrames.getD mode (SeedCertificate.zero, SeedCertificate.zero)
  if input = 0 then pair.1 else pair.2

set_option maxRecDepth 8000000 in
/-- Unlike the rank and inverse certificates, this table is small enough to
reduce in the kernel, so it uses `decide` rather than `native_decide`.  That
matters: `seed_frame_decomposition` and the whole of `SeedBridge` depend on it. -/
theorem seedFrameIVec_eq_explicit (mode : Fin 13) (input : Fin 2) :
    seedFrameIVec mode input = explicitSeedFrameIVec mode input := by
  decide +revert

def seedFrameNorm (mode input : Nat) : ℝ :=
  (SeedCertificate.dot (seedFrameIVec mode input) (seedFrameIVec mode input) : ℝ)

def seedMode (mode : Nat) : LatticeVec := latticeOfIVec (seedModeIVec mode)
def seedFrameReal (mode input : Nat) : RVec := realOfIVec (seedFrameIVec mode input)

noncomputable def seedEncoding (D : LatticeVec → CVec →ₗ[ℂ] CVec) : SeedParameter := fun column ↦
  let mode := column.val / 12
  let within := column.val % 12
  let output := within / 4
  let input := (within % 4) / 2
  let part := within % 2
  let value := D (seedMode mode) (realToComplexVec (seedFrameReal mode input))
  let component := value ⟨output, by omega⟩
  (if part = 0 then component.re else component.im) / seedFrameNorm mode input

def generatorACoordinate (g : Fin 12 → ℝ) (b : Fin 6) : ℝ :=
  g ⟨b, by omega⟩

def generatorBCoordinate (g : Fin 12 → ℝ) (b : Fin 6) : ℝ :=
  g ⟨6 + b, by omega⟩

def symmetricMatrixFromSix (x : Fin 6 → ℝ) : RMatrix := fun i j ↦
  ∑ b : Fin 6, x b * (SeedCertificate.symmetricBasisEntry b i j : ℝ)

def generatorAOf (g : Fin 12 → ℝ) : RMatrix :=
  symmetricMatrixFromSix (generatorACoordinate g)

def generatorBOf (g : Fin 12 → ℝ) : RMatrix :=
  symmetricMatrixFromSix (generatorBCoordinate g)

theorem symmetricBasisEntry_comm (b : Fin 6) (i j : Fin 3) :
    SeedCertificate.symmetricBasisEntry b i j =
      SeedCertificate.symmetricBasisEntry b j i := by
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    decide

theorem symmetricMatrixFromSix_symmetric (x : Fin 6 → ℝ) :
    (symmetricMatrixFromSix x).transpose = symmetricMatrixFromSix x := by
  ext i j
  simp only [Matrix.transpose_apply, symmetricMatrixFromSix]
  congr 1
  funext b
  rw [symmetricBasisEntry_comm]

theorem generatorAOf_symmetric (g : Fin 12 → ℝ) :
    (generatorAOf g).transpose = generatorAOf g :=
  symmetricMatrixFromSix_symmetric _

theorem generatorBOf_symmetric (g : Fin 12 → ℝ) :
    (generatorBOf g).transpose = generatorBOf g :=
  symmetricMatrixFromSix_symmetric _

theorem symmetricMatrixFromSix_mulVec_component
    (x : Fin 6 → ℝ) (v : SeedCertificate.IVec) (o : Fin 3) :
    Matrix.mulVec (symmetricMatrixFromSix x) (realOfIVec v) o =
      ∑ b : Fin 6, x b *
        (SeedCertificate.componentZ
          (SeedCertificate.symmetricBasisMulVec b v) o : ℝ) := by
  fin_cases o <;>
    simp [Matrix.mulVec, dotProduct, symmetricMatrixFromSix, realOfIVec,
      SeedCertificate.componentZ, SeedCertificate.symmetricBasisMulVec,
      Fin.sum_univ_succ] <;>
    ring

theorem symmetricMatrixFromSix_crossAnticommutator_component
    (x : Fin 6 → ℝ) (k v : SeedCertificate.IVec) (o : Fin 3) :
    crossAnticommutator (symmetricMatrixFromSix x) (latticeOfIVec k)
        (realOfIVec v) o =
      ∑ b : Fin 6, x b *
        (SeedCertificate.componentZ
          (SeedCertificate.crossAnticommutatorBasis b k v) o : ℝ) := by
  fin_cases o <;>
    simp [crossAnticommutator, Vec3.cross, Matrix.mulVec, dotProduct,
      symmetricMatrixFromSix, latticeOfIVec, latticeToReal, latticeVec,
      realOfIVec, SeedCertificate.componentZ,
      SeedCertificate.crossAnticommutatorBasis, SeedCertificate.add,
      SeedCertificate.cross, SeedCertificate.symmetricBasisMulVec,
      Fin.sum_univ_succ] <;>
    ring

theorem seedEncoding_generator (g : Fin 12 → ℝ) :
    seedEncoding (generatorMap (generatorAOf g) (generatorBOf g)) =
      seedGeneratorLinear g := by
  funext column
  let mode := column.val / 12
  let within := column.val % 12
  let output : Fin 3 := ⟨within / 4, by omega⟩
  let input := (within % 4) / 2
  let part := within % 2
  let k := seedModeIVec mode
  let f := seedFrameIVec mode input
  have hgen := generatorMap_on_real (generatorAOf g) (generatorBOf g)
    (latticeOfIVec k) (realOfIVec f)
  have hcomponent := congrFun hgen output
  have hre :
      (generatorMap (generatorAOf g) (generatorBOf g) (latticeOfIVec k)
        (realToComplexVec (realOfIVec f)) output).re =
        Matrix.mulVec (generatorAOf g) (realOfIVec f) output := by
    rw [hcomponent]
    simp [realToComplexVec]
  have him :
      (generatorMap (generatorAOf g) (generatorBOf g) (latticeOfIVec k)
        (realToComplexVec (realOfIVec f)) output).im =
        crossAnticommutator (generatorBOf g) (latticeOfIVec k)
          (realOfIVec f) output := by
    rw [hcomponent]
    simp [realToComplexVec]
  change (if part = 0 then
      (generatorMap (generatorAOf g) (generatorBOf g) (latticeOfIVec k)
        (realToComplexVec (realOfIVec f)) output).re
    else
      (generatorMap (generatorAOf g) (generatorBOf g) (latticeOfIVec k)
        (realToComplexVec (realOfIVec f)) output).im) /
      (SeedCertificate.dot f f : ℝ) =
    ∑ j : Fin 12,
      (SeedCertificate.generatorCoordinateQ column j : ℝ) * g j
  have hpart : part = 0 ∨ part = 1 := by
    dsimp [part]
    omega
  have hmod4 : within % 4 = column.val % 4 := by
    dsimp [within]
    omega
  rcases hpart with hpart | hpart
  · rw [if_pos hpart, hre,
      show generatorAOf g = symmetricMatrixFromSix (generatorACoordinate g) from rfl,
      symmetricMatrixFromSix_mulVec_component (generatorACoordinate g) f output]
    simp [SeedCertificate.generatorCoordinateQ, mode, within, input, part, hpart,
      k, f, seedFrameIVec, seedModeIVec, hmod4, generatorACoordinate,
      Fin.sum_univ_succ]
    ring
  · rw [if_neg (by omega), him,
      show generatorBOf g = symmetricMatrixFromSix (generatorBCoordinate g) from rfl,
      symmetricMatrixFromSix_crossAnticommutator_component
        (generatorBCoordinate g) k f output]
    simp [SeedCertificate.generatorCoordinateQ, mode, within, input, part, hpart,
      k, f, seedFrameIVec, seedModeIVec, hmod4, generatorBCoordinate,
      Fin.sum_univ_succ]
    ring

def seedFrameComplex (mode input : Nat) : CVec :=
  realToComplexVec (seedFrameReal mode input)

theorem seed_frame_decomposition (mode : Fin 13) (v : CVec)
    (hv : Transverse (seedMode mode) v) :
    v =
      (Vec3.dot v (seedFrameComplex mode 0) / seedFrameNorm mode 0) •
        seedFrameComplex mode 0 +
      (Vec3.dot v (seedFrameComplex mode 1) / seedFrameNorm mode 1) •
        seedFrameComplex mode 1 := by
  simp only [seedFrameComplex, seedFrameReal, seedFrameNorm]
  -- `seedFrameIVec_eq_explicit` is stated for `input : Fin 2`, so its left-hand
  -- side carries a `Fin.val` coercion that does not match the literal `0` and
  -- `1` in the goal.  Discharge the coercion before rewriting.
  have h0 := seedFrameIVec_eq_explicit mode 0
  have h1 := seedFrameIVec_eq_explicit mode 1
  simp only [Fin.val_zero, Fin.val_one] at h0 h1
  rw [h0, h1]
  funext coordinate
  -- After normalization each coordinate goal is the identity
  -- `v i = (projection onto the frame) i`, whose defect is exactly
  -- `(k i / ‖k‖²) * (k ⬝ v)`.  The thirteen seed modes have entries in
  -- `{-1, 0, 1}` and `‖k‖² ∈ {1, 2, 3}`, so the multiplier of `hv` is one of
  -- `0, ±1, ±1/2, ±1/3`.  `ring1` covers the zero multiplier; note that plain
  -- `ring` must not be used here, because on failure it falls back to `ring_nf`
  -- and *succeeds* with the goal still open, which would starve the
  -- alternatives below.
  fin_cases mode <;> fin_cases coordinate <;>
    simp [Transverse, seedMode, seedModeIVec, latticeOfIVec, latticeVec,
      latticeToComplex, realOfIVec, realToComplexVec, Vec3.dot,
      explicitSeedFrameIVec, explicitSeedFrames,
      SeedCertificate.representatives, SeedCertificate.dot] at hv ⊢ <;>
    first
      | linear_combination hv
      | linear_combination -hv
      | linear_combination hv / 2
      | linear_combination -hv / 2
      | linear_combination hv / 3
      | linear_combination -hv / 3
      | ring1

/-- The conclusion of Theorem A on every nonzero transverse Fourier fiber. -/
def HasGeneratorForm (R : MultiplierSymbol) : Prop :=
  ∃ A B : RMatrix,
    A.transpose = A ∧ B.transpose = B ∧
      ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
        R.map k v = generatorMap A B k v

theorem hasGeneratorForm_universalCancellation (R : MultiplierSymbol)
    (hform : HasGeneratorForm R) : UniversalCancellation R := by
  obtain ⟨A, B, hA, hB, hmap⟩ := hform
  intro w
  rw [cubicForm_eq_I_mul_tripleSum]
  have hinteraction : ∀ p q r,
      orderedInteraction R.map w p q r =
        orderedInteraction (generatorMap A B) w p q r := by
    intro p q r
    by_cases hp : p = 0
    · subst p
      have hR0 : R.map 0 (w.coeff 0) = 0 := by
        rw [w.meanZero]
        exact (R.map 0).map_zero
      have hG0 : generatorMap A B 0 (w.coeff 0) = 0 := by
        rw [w.meanZero]
        exact (generatorMap A B 0).map_zero
      simp [orderedInteraction, hR0, hG0]
    · rw [orderedInteraction, orderedInteraction,
        hmap p hp (w.coeff p) (w.divergenceFree p)]
  have hsum : tripleSum w.coeff.support (orderedInteraction R.map w) =
      tripleSum w.coeff.support (orderedInteraction (generatorMap A B) w) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    exact hinteraction p q r
  rw [hsum, generator_orderedInteraction_sum_zero A B hA hB w]
  simp

theorem generator_witnesses_unique (R : MultiplierSymbol)
    (A B A' B' : RMatrix)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hA' : A'.transpose = A') (hB' : B'.transpose = B')
    (h : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
      R.map k v = generatorMap A B k v)
    (h' : ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
      R.map k v = generatorMap A' B' k v) :
    A = A' ∧ B = B' := by
  apply generator_parameters_unique A B A' B' hA hB hA' hB'
  intro k hk v hv
  rw [← h k hk v hv, ← h' k hk v hv]

end FourierMultiplierRigidity
