import FourierMultiplierRigidity.PhysicalSpaceIntegral
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# The classification on a function space of smooth fields

Theorem A and Corollary C are proved on finite Fourier fields.  This module
removes the finiteness: the strain–vorticity functional is extended by an
absolutely convergent series to every real, mean-zero, divergence-free field
on `𝕋³` whose Fourier coefficients decay rapidly (that is, to every smooth
solenoidal field), and the classification is proved there.
-/

namespace FourierMultiplierRigidity.Smooth

open FourierMultiplierRigidity.StrainVorticity

noncomputable section

/-! ## Lattice weights -/

/-- The sup norm of a lattice wavevector. -/
def latticeNorm (k : LatticeVec) : ℕ :=
  Finset.univ.sup fun i => (k i).natAbs

theorem natAbs_le_latticeNorm (k : LatticeVec) (i : Fin 3) :
    (k i).natAbs ≤ latticeNorm k :=
  Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)

@[simp] theorem latticeNorm_neg (k : LatticeVec) : latticeNorm (-k) = latticeNorm k := by
  simp [latticeNorm]

theorem latticeNorm_add_le (k l : LatticeVec) :
    latticeNorm (k + l) ≤ latticeNorm k + latticeNorm l := by
  refine Finset.sup_le fun i _ => ?_
  have h1 := natAbs_le_latticeNorm k i
  have h2 := natAbs_le_latticeNorm l i
  have h3 : ((k + l) i).natAbs ≤ (k i).natAbs + (l i).natAbs := by
    simpa using Int.natAbs_add_le (k i) (l i)
  omega

/-- The polynomial weight `(|k| + 1)^N`. -/
def weight (N : ℕ) (k : LatticeVec) : ℝ := ((latticeNorm k : ℝ) + 1) ^ N

theorem weight_pos (N : ℕ) (k : LatticeVec) : 0 < weight N k := by
  unfold weight
  positivity

theorem weight_nonneg (N : ℕ) (k : LatticeVec) : 0 ≤ weight N k :=
  (weight_pos N k).le

theorem one_le_weight (N : ℕ) (k : LatticeVec) : 1 ≤ weight N k := by
  unfold weight
  refine one_le_pow₀ ?_
  have : (0 : ℝ) ≤ (latticeNorm k : ℝ) := Nat.cast_nonneg _
  linarith

@[simp] theorem weight_one (k : LatticeVec) : weight 1 k = (latticeNorm k : ℝ) + 1 := pow_one _

theorem weight_add (M N : ℕ) (k : LatticeVec) :
    weight (M + N) k = weight M k * weight N k := by
  unfold weight
  exact pow_add _ _ _

/-- The resonant partner of `p` and `q` is controlled by the two of them. -/
theorem weight_one_resonant_le (p q : LatticeVec) :
    weight 1 (-(p + q)) ≤ weight 1 p * weight 1 q := by
  have hle : latticeNorm (-(p + q)) ≤ latticeNorm p + latticeNorm q := by
    rw [latticeNorm_neg]
    exact latticeNorm_add_le p q
  have hcast : ((latticeNorm (-(p + q)) : ℝ)) ≤ (latticeNorm p : ℝ) + (latticeNorm q : ℝ) := by
    exact_mod_cast hle
  have hp : (0 : ℝ) ≤ (latticeNorm p : ℝ) := by positivity
  have hq : (0 : ℝ) ≤ (latticeNorm q : ℝ) := by positivity
  simp only [weight_one]
  nlinarith

/-! ## Elementary norm bounds -/

theorem norm_dot_le (a b : CVec) : ‖Vec3.dot a b‖ ≤ 3 * (‖a‖ * ‖b‖) := by
  have h : ∀ i : Fin 3, ‖a i * b i‖ ≤ ‖a‖ * ‖b‖ := by
    intro i
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b i)
      (norm_nonneg _) (norm_nonneg _)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hsum : ‖a 0 * b 0 + a 1 * b 1 + a 2 * b 2‖ ≤
      ‖a 0 * b 0‖ + ‖a 1 * b 1‖ + ‖a 2 * b 2‖ :=
    le_trans (norm_add_le _ _) (by
      have := norm_add_le (a 0 * b 0) (a 1 * b 1)
      linarith)
  change ‖a 0 * b 0 + a 1 * b 1 + a 2 * b 2‖ ≤ _
  linarith

theorem norm_cross_le (a b : CVec) : ‖Vec3.cross a b‖ ≤ 2 * (‖a‖ * ‖b‖) := by
  have h : ∀ i j : Fin 3, ‖a i * b j‖ ≤ ‖a‖ * ‖b‖ := by
    intro i j
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm a i) (norm_le_pi_norm b j)
      (norm_nonneg _) (norm_nonneg _)
  have key : ∀ i j : Fin 3, ‖a i * b j - a j * b i‖ ≤ 2 * (‖a‖ * ‖b‖) := by
    intro i j
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := h i j
    have h2 := h j i
    linarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  fin_cases i
  · exact key 1 2
  · exact key 2 0
  · exact key 0 1

theorem norm_latticeToComplex_le (k : LatticeVec) :
    ‖latticeToComplex k‖ ≤ (latticeNorm k : ℝ) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have h : ‖((k i : ℤ) : ℂ)‖ = ((k i).natAbs : ℝ) := by
    rw [Complex.norm_intCast]
    simp
  simp only [latticeToComplex]
  rw [h]
  exact_mod_cast natAbs_le_latticeNorm k i

theorem norm_curlSymbol_le (k : LatticeVec) (v : CVec) :
    ‖curlSymbol k v‖ ≤ 2 * ((latticeNorm k : ℝ) * ‖v‖) := by
  unfold curlSymbol
  rw [norm_smul]
  simp only [Complex.norm_I, one_mul]
  refine le_trans (norm_cross_le _ _) ?_
  have h := norm_latticeToComplex_le k
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith

theorem norm_strainInteraction_le (p : LatticeVec) (a b c : CVec) :
    ‖strainInteraction p a b c‖ ≤
      9 * ((latticeNorm p : ℝ) * (‖a‖ * (‖b‖ * ‖c‖))) := by
  have hk := norm_latticeToComplex_le p
  have h1 : ‖Vec3.dot (latticeToComplex p) b‖ ≤ 3 * ((latticeNorm p : ℝ) * ‖b‖) := by
    refine le_trans (norm_dot_le _ _) ?_
    have : (0 : ℝ) ≤ ‖b‖ := norm_nonneg _
    nlinarith
  have h2 : ‖Vec3.dot (latticeToComplex p) c‖ ≤ 3 * ((latticeNorm p : ℝ) * ‖c‖) := by
    refine le_trans (norm_dot_le _ _) ?_
    have : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
    nlinarith
  have h3 : ‖Vec3.dot a c‖ ≤ 3 * (‖a‖ * ‖c‖) := norm_dot_le _ _
  have h4 : ‖Vec3.dot a b‖ ≤ 3 * (‖a‖ * ‖b‖) := norm_dot_le _ _
  have hna : (0 : ℝ) ≤ ‖a‖ := norm_nonneg _
  have hnb : (0 : ℝ) ≤ ‖b‖ := norm_nonneg _
  have hnc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
  have hnp : (0 : ℝ) ≤ (latticeNorm p : ℝ) := by positivity
  unfold strainInteraction
  rw [norm_mul]
  have hI : ‖Complex.I / 2‖ = 1 / 2 := by
    rw [norm_div, Complex.norm_I]
    norm_num
  rw [hI]
  have hsplit : ‖Vec3.dot (latticeToComplex p) b * Vec3.dot a c +
      Vec3.dot (latticeToComplex p) c * Vec3.dot a b‖ ≤
      ‖Vec3.dot (latticeToComplex p) b‖ * ‖Vec3.dot a c‖ +
        ‖Vec3.dot (latticeToComplex p) c‖ * ‖Vec3.dot a b‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
  nlinarith [norm_nonneg (Vec3.dot (latticeToComplex p) b),
    norm_nonneg (Vec3.dot (latticeToComplex p) c),
    norm_nonneg (Vec3.dot a c), norm_nonneg (Vec3.dot a b)]

/-- Every fixed fiber map is bounded; `CVec` is finite-dimensional. -/
theorem exists_linearMap_bound (f : CVec →ₗ[ℂ] CVec) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖f v‖ ≤ C * ‖v‖ := by
  have hc : Continuous f := LinearMap.continuous_of_finiteDimensional f
  refine ⟨‖(⟨f, hc⟩ : CVec →L[ℂ] CVec)‖, norm_nonneg _, fun v => ?_⟩
  exact (⟨f, hc⟩ : CVec →L[ℂ] CVec).le_opNorm v

/-! ## Smooth solenoidal fields -/

/-- A real, mean-zero, divergence-free field on the three-torus whose Fourier
coefficients decay faster than every polynomial — that is, a smooth solenoidal
field, presented by its Fourier coefficients. -/
structure SmoothField where
  coeff : LatticeVec → CVec
  meanZero : coeff 0 = 0
  divergenceFree : ∀ k, Transverse k (coeff k)
  reality : ∀ k, coeff (-k) = conjVec (coeff k)
  decay : ∀ N : ℕ, Summable fun k => weight N k * ‖coeff k‖

/-- Every finite Fourier field is a smooth field. -/
def ofTrig (w : TrigField) : SmoothField where
  coeff := w.coeff
  meanZero := w.meanZero
  divergenceFree := w.divergenceFree
  reality := w.reality
  decay := by
    intro N
    refine summable_of_ne_finset_zero (s := w.coeff.support) fun k hk => ?_
    have hzero : w.coeff k = 0 := by simpa using hk
    simp [hzero]

theorem coeff_summable (u : SmoothField) : Summable fun k => ‖u.coeff k‖ := by
  simpa [weight] using u.decay 0

theorem coeff_norm_le_tsum (u : SmoothField) (k : LatticeVec) :
    ‖u.coeff k‖ ≤ ∑' l, ‖u.coeff l‖ :=
  (coeff_summable u).le_tsum k fun _ _ => norm_nonneg _

/-- The resonant atom of the strain–vorticity functional: the interaction of
the modes `p`, `q` and their resonant partner `-(p+q)`. -/
def svAtom (T : MultiplierSymbol) (a : LatticeVec → CVec)
    (x : LatticeVec × LatticeVec) : ℂ :=
  strainInteraction x.1 (T.map x.1 (a x.1))
    (curlSymbol x.2 (a x.2))
    (curlSymbol (-(x.1 + x.2)) (a (-(x.1 + x.2))))

/-- The strain–vorticity functional of a smooth field, as an absolutely
convergent series over all resonant interactions. -/
def smoothSVForm (T : MultiplierSymbol) (u : SmoothField) : ℂ :=
  ∑' x : LatticeVec × LatticeVec, svAtom T u.coeff x

/-! ## Symbol bounds -/

/-- A polynomial bound for the symbol on the transverse fibers it is tested on. -/
def SymbolBound (T : MultiplierSymbol) : Prop :=
  ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧
    ∀ k v, Transverse k v → ‖T.map k v‖ ≤ C * weight m k * ‖v‖

/-- A symbol of strain-generator form is automatically of polynomial growth,
so the classification needs no separate boundedness hypothesis. -/
theorem symbolBound_of_strainGenerator (T : MultiplierSymbol)
    (h : HasStrainGeneratorForm T) : SymbolBound T := by
  obtain ⟨A, B, _, _, hmap⟩ := h
  obtain ⟨CA, hCA, hA⟩ := exists_linearMap_bound (complexifyMatrix A).mulVecLin
  obtain ⟨CB, hCB, hB⟩ := exists_linearMap_bound (complexifyMatrix B).mulVecLin
  obtain ⟨C0, hC0, h0⟩ := exists_linearMap_bound (T.map 0)
  refine ⟨C0 + 2 * CA + 8 * CB, 2, by linarith, ?_⟩
  intro k v hv
  have hnv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have hKnn : (0 : ℝ) ≤ (latticeNorm k : ℝ) := Nat.cast_nonneg _
  by_cases hk : k = 0
  · subst hk
    have hone : weight 2 (0 : LatticeVec) = 1 := by
      simp [weight, latticeNorm]
    have hb := h0 v
    rw [hone]
    nlinarith [mul_nonneg hCA hnv, mul_nonneg hCB hnv]
  · have hform := hmap k hk v hv
    have hwb : ‖curlSymbol k v‖ ≤ 2 * ((latticeNorm k : ℝ) * ‖v‖) :=
      norm_curlSymbol_le k v
    have hcurlw : ‖curlSymbol k (curlSymbol k v)‖ ≤
        2 * ((latticeNorm k : ℝ) * ‖curlSymbol k v‖) := norm_curlSymbol_le _ _
    have hAw : ‖Matrix.mulVec (complexifyMatrix A) (curlSymbol k v)‖ ≤
        CA * ‖curlSymbol k v‖ := hA _
    have hBcurlw : ‖Matrix.mulVec (complexifyMatrix B) (curlSymbol k (curlSymbol k v))‖ ≤
        CB * ‖curlSymbol k (curlSymbol k v)‖ := hB _
    have hBw : ‖Matrix.mulVec (complexifyMatrix B) (curlSymbol k v)‖ ≤
        CB * ‖curlSymbol k v‖ := hB _
    have hcurlBw : ‖curlSymbol k (Matrix.mulVec (complexifyMatrix B) (curlSymbol k v))‖ ≤
        2 * ((latticeNorm k : ℝ) *
          ‖Matrix.mulVec (complexifyMatrix B) (curlSymbol k v)‖) :=
      norm_curlSymbol_le _ _
    have hexp : T.map k v =
        Matrix.mulVec (complexifyMatrix A) (curlSymbol k v) +
          Matrix.mulVec (complexifyMatrix B) (curlSymbol k (curlSymbol k v)) +
          curlSymbol k (Matrix.mulVec (complexifyMatrix B) (curlSymbol k v)) := by
      rw [hform]
      simp [generatorMap_apply]
    have hsplit : ‖T.map k v‖ ≤
        ‖Matrix.mulVec (complexifyMatrix A) (curlSymbol k v)‖ +
          ‖Matrix.mulVec (complexifyMatrix B) (curlSymbol k (curlSymbol k v))‖ +
          ‖curlSymbol k (Matrix.mulVec (complexifyMatrix B) (curlSymbol k v))‖ := by
      rw [hexp]
      refine le_trans (norm_add_le _ _) ?_
      have := norm_add_le
        (Matrix.mulVec (complexifyMatrix A) (curlSymbol k v))
        (Matrix.mulVec (complexifyMatrix B) (curlSymbol k (curlSymbol k v)))
      linarith
    have c1 : ‖Matrix.mulVec (complexifyMatrix A) (curlSymbol k v)‖ ≤
        2 * CA * ((latticeNorm k : ℝ) * ‖v‖) := by
      have := mul_le_mul_of_nonneg_left hwb hCA
      linarith
    have c2 : ‖Matrix.mulVec (complexifyMatrix B) (curlSymbol k (curlSymbol k v))‖ ≤
        4 * CB * ((latticeNorm k : ℝ) * ((latticeNorm k : ℝ) * ‖v‖)) := by
      have s1 := mul_le_mul_of_nonneg_left hcurlw hCB
      have s2 := mul_le_mul_of_nonneg_left hwb
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hCB) hKnn)
      linarith
    have c3 : ‖curlSymbol k (Matrix.mulVec (complexifyMatrix B) (curlSymbol k v))‖ ≤
        4 * CB * ((latticeNorm k : ℝ) * ((latticeNorm k : ℝ) * ‖v‖)) := by
      have s1 := mul_le_mul_of_nonneg_left hBw
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKnn)
      have s2 := mul_le_mul_of_nonneg_left hwb
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hKnn) hCB)
      linarith
    have hweight2 : weight 2 k = ((latticeNorm k : ℝ) + 1) ^ 2 := rfl
    have hKv : (latticeNorm k : ℝ) * ‖v‖ ≤ ((latticeNorm k : ℝ) + 1) ^ 2 * ‖v‖ := by
      nlinarith [sq_nonneg ((latticeNorm k : ℝ))]
    have hKKv : (latticeNorm k : ℝ) * ((latticeNorm k : ℝ) * ‖v‖) ≤
        ((latticeNorm k : ℝ) + 1) ^ 2 * ‖v‖ := by
      nlinarith [sq_nonneg ((latticeNorm k : ℝ))]
    have hb1 : 2 * CA * ((latticeNorm k : ℝ) * ‖v‖) ≤
        2 * CA * (((latticeNorm k : ℝ) + 1) ^ 2 * ‖v‖) :=
      mul_le_mul_of_nonneg_left hKv (by linarith)
    have hb2 : 4 * CB * ((latticeNorm k : ℝ) * ((latticeNorm k : ℝ) * ‖v‖)) ≤
        4 * CB * (((latticeNorm k : ℝ) + 1) ^ 2 * ‖v‖) :=
      mul_le_mul_of_nonneg_left hKKv (by linarith)
    have hb3 : 0 ≤ C0 * (((latticeNorm k : ℝ) + 1) ^ 2 * ‖v‖) :=
      mul_nonneg hC0 (mul_nonneg (by positivity) hnv)
    rw [hweight2]
    nlinarith

/-! ## Absolute convergence -/

private theorem mul_four_le {a b c d a' b' c' d' : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha' : a ≤ a') (hb' : b ≤ b') (hc' : c ≤ c') (hd' : d ≤ d') :
    a * (b * (c * d)) ≤ a' * (b' * (c' * d')) := by
  have h1 : c * d ≤ c' * d' := mul_le_mul hc' hd' hd (le_trans hc hc')
  have h2 : b * (c * d) ≤ b' * (c' * d') :=
    mul_le_mul hb' h1 (mul_nonneg hc hd) (le_trans hb hb')
  exact mul_le_mul ha' h2 (mul_nonneg hb (mul_nonneg hc hd)) (le_trans ha ha')

set_option maxHeartbeats 1000000 in
/-- The resonant series converges absolutely for every smooth field. -/
theorem summable_svAtom (T : MultiplierSymbol) (hT : SymbolBound T)
    (u : SmoothField) : Summable (svAtom T u.coeff) := by
  obtain ⟨C, m, hC, hbound⟩ := hT
  set M : ℝ := ∑' l, ‖u.coeff l‖ with hMdef
  have hM : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
  have hgs : Summable fun p : LatticeVec =>
      36 * C * M * (weight (m + 2) p * ‖u.coeff p‖) :=
    (u.decay (m + 2)).mul_left _
  have hhs : Summable fun q : LatticeVec => weight 2 q * ‖u.coeff q‖ := u.decay 2
  refine Summable.of_norm_bounded
    (g := fun x : LatticeVec × LatticeVec =>
      (36 * C * M * (weight (m + 2) x.1 * ‖u.coeff x.1‖)) *
        (weight 2 x.2 * ‖u.coeff x.2‖))
    (Summable.mul_of_nonneg hgs hhs
      (fun p => mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36) hC) hM)
        (mul_nonneg (weight_nonneg (m + 2) p) (norm_nonneg _)))
      (fun q => mul_nonneg (weight_nonneg 2 q) (norm_nonneg _)))
    ?_
  rintro ⟨p, q⟩
  have hnp : (0 : ℝ) ≤ (latticeNorm p : ℝ) := Nat.cast_nonneg _
  have hwp : (latticeNorm p : ℝ) ≤ weight 1 p := by
    rw [weight_one]; linarith
  have hwq : (latticeNorm q : ℝ) ≤ weight 1 q := by
    rw [weight_one]; linarith
  have hstrain := norm_strainInteraction_le p (T.map p (u.coeff p))
    (curlSymbol q (u.coeff q)) (curlSymbol (-(p + q)) (u.coeff (-(p + q))))
  have hA : ‖T.map p (u.coeff p)‖ ≤ C * weight m p * ‖u.coeff p‖ :=
    hbound p (u.coeff p) (u.divergenceFree p)
  have hB : ‖curlSymbol q (u.coeff q)‖ ≤ 2 * (weight 1 q * ‖u.coeff q‖) := by
    refine le_trans (norm_curlSymbol_le q (u.coeff q)) ?_
    have : (0 : ℝ) ≤ ‖u.coeff q‖ := norm_nonneg _
    nlinarith
  have hCc : ‖curlSymbol (-(p + q)) (u.coeff (-(p + q)))‖ ≤
      2 * (weight 1 p * weight 1 q * M) := by
    refine le_trans (norm_curlSymbol_le _ _) ?_
    have h1 : (latticeNorm (-(p + q)) : ℝ) ≤ weight 1 p * weight 1 q := by
      have := weight_one_resonant_le p q
      rw [weight_one] at this
      linarith
    have h2 : ‖u.coeff (-(p + q))‖ ≤ M := coeff_norm_le_tsum u _
    have h3 : (0 : ℝ) ≤ (latticeNorm (-(p + q)) : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ‖u.coeff (-(p + q))‖ := norm_nonneg _
    have h5 : (0 : ℝ) ≤ weight 1 p * weight 1 q :=
      mul_nonneg (weight_nonneg 1 p) (weight_nonneg 1 q)
    have := mul_le_mul h1 h2 h4 h5
    linarith
  have hchain := mul_four_le (a := (latticeNorm p : ℝ))
    (b := ‖T.map p (u.coeff p)‖) (c := ‖curlSymbol q (u.coeff q)‖)
    (d := ‖curlSymbol (-(p + q)) (u.coeff (-(p + q)))‖)
    (a' := weight 1 p) (b' := C * weight m p * ‖u.coeff p‖)
    (c' := 2 * (weight 1 q * ‖u.coeff q‖))
    (d' := 2 * (weight 1 p * weight 1 q * M))
    hnp (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hwp hA hB hCc
  have hfinal : 9 * (weight 1 p * ((C * weight m p * ‖u.coeff p‖) *
      ((2 * (weight 1 q * ‖u.coeff q‖)) * (2 * (weight 1 p * weight 1 q * M))))) =
      (36 * C * M * (weight (m + 2) p * ‖u.coeff p‖)) *
        (weight 2 q * ‖u.coeff q‖) := by
    have hp2 : weight (m + 2) p = weight m p * (weight 1 p * weight 1 p) := by
      rw [show m + 2 = m + 1 + 1 from rfl, weight_add, weight_add]
      ring
    have hq2 : weight 2 q = weight 1 q * weight 1 q := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, weight_add]
    rw [hp2, hq2]
    ring
  calc ‖svAtom T u.coeff (p, q)‖
      ≤ 9 * ((latticeNorm p : ℝ) * (‖T.map p (u.coeff p)‖ *
          (‖curlSymbol q (u.coeff q)‖ *
            ‖curlSymbol (-(p + q)) (u.coeff (-(p + q)))‖))) := hstrain
    _ ≤ 9 * (weight 1 p * ((C * weight m p * ‖u.coeff p‖) *
          ((2 * (weight 1 q * ‖u.coeff q‖)) *
            (2 * (weight 1 p * weight 1 q * M))))) := by
        have := hchain
        linarith
    _ = _ := hfinal

/-! ## Agreement with the finite theory -/

private theorem strainInteraction_zero_fst (p : LatticeVec) (b c : CVec) :
    strainInteraction p 0 b c = 0 := by
  simp [strainInteraction, Vec3.dot]

private theorem strainInteraction_zero_snd (p : LatticeVec) (a c : CVec) :
    strainInteraction p a 0 c = 0 := by
  simp [strainInteraction, Vec3.dot]

private theorem strainInteraction_zero_thd (p : LatticeVec) (a b : CVec) :
    strainInteraction p a b 0 = 0 := by
  simp [strainInteraction, Vec3.dot]

@[simp] private theorem curlSymbol_zero' (k : LatticeVec) : curlSymbol k 0 = 0 := by
  simp [curlSymbol]

private theorem svAtom_eq_zero_of_coeff_zero (T : MultiplierSymbol)
    (a : LatticeVec → CVec) (x : LatticeVec × LatticeVec)
    (h : a x.1 = 0 ∨ a x.2 = 0 ∨ a (-(x.1 + x.2)) = 0) : svAtom T a x = 0 := by
  unfold svAtom
  rcases h with h | h | h
  · rw [h, map_zero, strainInteraction_zero_fst]
  · rw [h, curlSymbol_zero', strainInteraction_zero_snd]
  · rw [h, curlSymbol_zero', strainInteraction_zero_thd]

private theorem resonant_iff (p q r : LatticeVec) :
    p + q + r = 0 ↔ r = -(p + q) := by
  constructor
  · intro h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  · intro h
    rw [h]
    abel

/-- On a finite Fourier field the series is the finite resonant sum used by
Corollary C. -/
theorem smoothSVForm_ofTrig (T : MultiplierSymbol) (w : TrigField) :
    smoothSVForm T (ofTrig w) = svCubicForm T w := by
  classical
  have hcollapse : smoothSVForm T (ofTrig w) =
      ∑ x ∈ w.coeff.support ×ˢ w.coeff.support, svAtom T w.coeff x := by
    refine tsum_eq_sum fun x hx => ?_
    refine svAtom_eq_zero_of_coeff_zero T w.coeff x ?_
    by_cases h1 : x.1 ∈ w.coeff.support
    · have h2 : x.2 ∉ w.coeff.support := by
        intro h2
        exact hx (Finset.mem_product.mpr ⟨h1, h2⟩)
      exact Or.inr (Or.inl (by simpa using h2))
    · exact Or.inl (by simpa using h1)
  rw [hcollapse, ← physicalSVCubicForm_eq_svCubicForm, physicalSVCubicForm,
    tripleSum, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have hcond : ∀ r : LatticeVec, physicalStrainAtom T w p q r =
      if r = -(p + q) then
        strainInteraction p (T.map p (w.coeff p)) ((curlField w).coeff q)
          ((curlField w).coeff r)
      else 0 := by
    intro r
    unfold physicalStrainAtom
    by_cases hres : p + q + r = 0
    · rw [if_pos hres, if_pos ((resonant_iff p q r).mp hres)]
    · rw [if_neg hres, if_neg (fun h => hres ((resonant_iff p q r).mpr h))]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ w.coeff.support) => hcond r,
    Finset.sum_ite_eq' w.coeff.support (-(p + q))
      (fun r => strainInteraction p (T.map p (w.coeff p)) ((curlField w).coeff q)
        ((curlField w).coeff r))]
  by_cases hmem : -(p + q) ∈ w.coeff.support
  · rw [if_pos hmem]
    rfl
  · rw [if_neg hmem]
    have hzero : w.coeff (-(p + q)) = 0 := by simpa using hmem
    refine svAtom_eq_zero_of_coeff_zero T w.coeff (p, q) (Or.inr (Or.inr ?_))
    exact hzero

/-! ## Exhaustion by coordinate boxes -/

/-- The coordinate box of radius `N`. -/
def box (N : ℕ) : Finset LatticeVec :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem mem_box_iff (N : ℕ) (k : LatticeVec) :
    k ∈ box N ↔ ∀ i, -(N : ℤ) ≤ k i ∧ k i ≤ (N : ℤ) := by
  simp [box, Fintype.mem_piFinset, Finset.mem_Icc]

theorem zero_mem_box (N : ℕ) : (0 : LatticeVec) ∈ box N := by
  refine (mem_box_iff N 0).mpr fun i => ?_
  simp

theorem neg_mem_box (N : ℕ) (k : LatticeVec) : -k ∈ box N ↔ k ∈ box N := by
  simp only [mem_box_iff, Pi.neg_apply]
  constructor <;> intro h i <;> have := h i <;> omega

theorem box_mono : Monotone box := by
  intro M N hMN k hk
  rw [mem_box_iff] at hk ⊢
  intro i
  have := hk i
  have : (M : ℤ) ≤ (N : ℤ) := by exact_mod_cast hMN
  omega

theorem mem_box_latticeNorm (k : LatticeVec) : k ∈ box (latticeNorm k) := by
  refine (mem_box_iff _ k).mpr fun i => ?_
  have h := natAbs_le_latticeNorm k i
  omega

/-- The finite set of resonant pairs inside the box of radius `N`. -/
def resonantBox (N : ℕ) : Finset (LatticeVec × LatticeVec) :=
  (box N ×ˢ box N).filter fun x => -(x.1 + x.2) ∈ box N

theorem mem_resonantBox_iff (N : ℕ) (x : LatticeVec × LatticeVec) :
    x ∈ resonantBox N ↔
      x.1 ∈ box N ∧ x.2 ∈ box N ∧ -(x.1 + x.2) ∈ box N := by
  simp [resonantBox, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem resonantBox_mono : Monotone resonantBox := by
  intro M N hMN x hx
  rw [mem_resonantBox_iff] at hx ⊢
  exact ⟨box_mono hMN hx.1, box_mono hMN hx.2.1, box_mono hMN hx.2.2⟩

theorem exists_mem_resonantBox (x : LatticeVec × LatticeVec) :
    ∃ N, x ∈ resonantBox N := by
  refine ⟨max (latticeNorm x.1) (max (latticeNorm x.2) (latticeNorm (-(x.1 + x.2)))), ?_⟩
  rw [mem_resonantBox_iff]
  refine ⟨box_mono (le_max_left _ _) (mem_box_latticeNorm _), ?_, ?_⟩
  · exact box_mono (le_trans (le_max_left _ _) (le_max_right _ _)) (mem_box_latticeNorm _)
  · exact box_mono (le_trans (le_max_right _ _) (le_max_right _ _)) (mem_box_latticeNorm _)

/-! ## Truncation -/

/-- The truncation of a smooth field to the coordinate box of radius `N`. -/
def truncate (u : SmoothField) (N : ℕ) : TrigField where
  coeff := Finsupp.onFinset (box N) (fun k => if k ∈ box N then u.coeff k else 0)
    (by
      intro k hk
      by_contra hmem
      rw [if_neg hmem] at hk
      exact hk rfl)
  meanZero := by
    simp [Finsupp.onFinset_apply, zero_mem_box, u.meanZero]
  divergenceFree := by
    intro k
    by_cases hk : k ∈ box N
    · simpa [Finsupp.onFinset_apply, hk] using u.divergenceFree k
    · simp [Finsupp.onFinset_apply, hk, Transverse, Vec3.dot]
  reality := by
    intro k
    by_cases hk : k ∈ box N
    · have hneg : -k ∈ box N := (neg_mem_box N k).mpr hk
      simp only [Finsupp.onFinset_apply, if_pos hk, if_pos hneg]
      exact u.reality k
    · have hneg : -k ∉ box N := fun h => hk ((neg_mem_box N k).mp h)
      simp only [Finsupp.onFinset_apply, if_neg hk, if_neg hneg]
      funext i
      simp [conjVec]

@[simp] theorem truncate_coeff (u : SmoothField) (N : ℕ) (k : LatticeVec) :
    (truncate u N).coeff k = if k ∈ box N then u.coeff k else 0 := rfl

theorem svAtom_truncate (T : MultiplierSymbol) (u : SmoothField) (N : ℕ)
    (x : LatticeVec × LatticeVec) :
    svAtom T (truncate u N).coeff x =
      if x ∈ resonantBox N then svAtom T u.coeff x else 0 := by
  by_cases hx : x ∈ resonantBox N
  · rw [if_pos hx]
    rw [mem_resonantBox_iff] at hx
    unfold svAtom
    rw [truncate_coeff, truncate_coeff, truncate_coeff, if_pos hx.1, if_pos hx.2.1,
      if_pos hx.2.2]
  · rw [if_neg hx]
    rw [mem_resonantBox_iff] at hx
    refine svAtom_eq_zero_of_coeff_zero T (truncate u N).coeff x ?_
    by_cases h1 : x.1 ∈ box N
    · by_cases h2 : x.2 ∈ box N
      · have h3 : -(x.1 + x.2) ∉ box N := fun h3 => hx ⟨h1, h2, h3⟩
        exact Or.inr (Or.inr (by rw [truncate_coeff, if_neg h3]))
      · exact Or.inr (Or.inl (by rw [truncate_coeff, if_neg h2]))
    · exact Or.inl (by rw [truncate_coeff, if_neg h1])

/-- The partial sum over the resonant box is the finite functional of the
truncated field. -/
theorem sum_resonantBox_eq_svCubicForm (T : MultiplierSymbol) (u : SmoothField)
    (N : ℕ) :
    ∑ x ∈ resonantBox N, svAtom T u.coeff x = svCubicForm T (truncate u N) := by
  classical
  have hfin : smoothSVForm T (ofTrig (truncate u N)) =
      ∑ x ∈ resonantBox N, svAtom T u.coeff x := by
    unfold smoothSVForm
    have hcoeff : (ofTrig (truncate u N)).coeff = (truncate u N).coeff := rfl
    rw [hcoeff]
    rw [tsum_congr (svAtom_truncate T u N)]
    rw [tsum_eq_sum (s := resonantBox N) fun x hx => by rw [if_neg hx]]
    exact Finset.sum_congr rfl fun x hx => by rw [if_pos hx]
  rw [← hfin, smoothSVForm_ofTrig]

theorem sum_resonantBox_eq_zero (T : MultiplierSymbol)
    (hcancel : UniversalSVCancellation T) (u : SmoothField) (N : ℕ) :
    ∑ x ∈ resonantBox N, svAtom T u.coeff x = 0 := by
  rw [sum_resonantBox_eq_svCubicForm]
  exact hcancel _

/-! ## The classification on smooth fields -/

/-- Universal cancellation over the whole space of smooth solenoidal fields. -/
def UniversalSmoothSVCancellation (T : MultiplierSymbol) : Prop :=
  ∀ u : SmoothField, smoothSVForm T u = 0

/-- **Density.**  Cancellation on finite Fourier fields propagates to every
smooth solenoidal field, by absolute convergence of the resonant series. -/
theorem smoothSVForm_eq_zero_of_strainGenerator (T : MultiplierSymbol)
    (hgen : HasStrainGeneratorForm T) (u : SmoothField) :
    smoothSVForm T u = 0 := by
  have hsum : Summable (svAtom T u.coeff) :=
    summable_svAtom T (symbolBound_of_strainGenerator T hgen) u
  have hHas : HasSum (svAtom T u.coeff) (smoothSVForm T u) := hsum.hasSum
  have hbox : Filter.Tendsto resonantBox Filter.atTop Filter.atTop :=
    resonantBox_mono.tendsto_atTop_finset exists_mem_resonantBox
  have hlim : Filter.Tendsto
      (fun N => ∑ x ∈ resonantBox N, svAtom T u.coeff x) Filter.atTop
      (nhds (smoothSVForm T u)) :=
    (hHas : Filter.Tendsto _ _ _).comp hbox
  have hzero : ∀ N, ∑ x ∈ resonantBox N, svAtom T u.coeff x = 0 :=
    sum_resonantBox_eq_zero T ((corollaryC T).mpr hgen) u
  have hconst : Filter.Tendsto
      (fun N => ∑ x ∈ resonantBox N, svAtom T u.coeff x) Filter.atTop
      (nhds 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst

/-- **Corollary C on a function space.**  The classification is not an
artifact of the finite-dimensional test class: universal cancellation over all
smooth solenoidal fields on the torus is again exactly the strain-generator
form. -/
theorem corollaryC_smooth (T : MultiplierSymbol) :
    UniversalSmoothSVCancellation T ↔ HasStrainGeneratorForm T := by
  constructor
  · intro h
    refine (corollaryC T).mp fun w => ?_
    rw [← smoothSVForm_ofTrig T w]
    exact h _
  · intro hgen u
    exact smoothSVForm_eq_zero_of_strainGenerator T hgen u

/-- The solenoidal specialization on the same function space. -/
theorem corollaryC_smooth_solenoidal (T : MultiplierSymbol)
    (hsol : HasSolenoidalOutput T) :
    UniversalSmoothSVCancellation T ↔ HasLaplacianCurlForm T := by
  rw [corollaryC_smooth, ← corollaryC, corollaryC_solenoidal T hsol]

/-! ## The physical reading of the extended functional -/

/-- The functional of a smooth field is the limit of the physical-space torus
integrals `∫_{𝕋³} sym ∇(Tu_N) : (ω_N ⊗ ω_N)` of its truncations.  The series is
therefore not a free definition: it is pinned to the physical integral of
`PhysicalSpaceIntegral.lean` along the approximating trigonometric fields. -/
theorem tendsto_torusMean_truncate (T : MultiplierSymbol) (hT : SymbolBound T)
    (u : SmoothField) :
    Filter.Tendsto
      (fun N => Torus.torusMean (strainVorticityDensity T (truncate u N)))
      Filter.atTop (nhds (smoothSVForm T u)) := by
  have hsum : Summable (svAtom T u.coeff) := summable_svAtom T hT u
  have hHas : HasSum (svAtom T u.coeff) (smoothSVForm T u) := hsum.hasSum
  have hbox : Filter.Tendsto resonantBox Filter.atTop Filter.atTop :=
    resonantBox_mono.tendsto_atTop_finset exists_mem_resonantBox
  have hlim : Filter.Tendsto
      (fun N => ∑ x ∈ resonantBox N, svAtom T u.coeff x) Filter.atTop
      (nhds (smoothSVForm T u)) :=
    (hHas : Filter.Tendsto _ _ _).comp hbox
  have hrewrite : ∀ N,
      Torus.torusMean (strainVorticityDensity T (truncate u N)) =
        ∑ x ∈ resonantBox N, svAtom T u.coeff x := by
    intro N
    rw [torusMean_strainVorticityDensity, physicalSVCubicForm_eq_svCubicForm,
      sum_resonantBox_eq_svCubicForm]
  simpa only [hrewrite] using hlim

/-! ## The class is strictly larger than the finite Fourier fields

A shear flow `u(x) = (0, f(x₀), 0)` with a geometrically decaying profile is
smooth, real, mean-zero and divergence-free, and has infinite Fourier support,
so the classification above is not a restatement of the finite theorem. -/

private theorem summable_nat_weight (N : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * ((2 : ℝ)⁻¹) ^ n := by
  have hr : ‖(2 : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos] <;> norm_num
  have hbase : Summable fun m : ℕ => (m : ℝ) ^ N * ((2 : ℝ)⁻¹) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one N hr
  have hshift : Summable ((fun m : ℕ => (m : ℝ) ^ N * ((2 : ℝ)⁻¹) ^ m) ∘ fun n : ℕ => n + 1) :=
    hbase.comp_injective fun a b h => by omega
  refine (hshift.mul_left 2).congr fun n => ?_
  simp only [Function.comp_apply]
  push_cast
  rw [pow_succ]
  ring

private theorem summable_int_weight (N : ℕ) :
    Summable fun n : ℤ => ((n.natAbs : ℝ) + 1) ^ N * ((2 : ℝ)⁻¹) ^ n.natAbs := by
  refine Summable.of_nat_of_neg ?_ ?_ <;>
    simpa using summable_nat_weight N

/-- The wavevectors along the first coordinate axis. -/
private def lineEmbed (n : ℤ) : LatticeVec := ![n, 0, 0]

private theorem lineEmbed_injective : Function.Injective lineEmbed := by
  intro a b h
  simpa [lineEmbed] using congrFun h 0

private theorem latticeNorm_lineEmbed (n : ℤ) :
    latticeNorm (lineEmbed n) = n.natAbs := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := rfl
  rw [latticeNorm, huniv]
  simp [lineEmbed]

private theorem mem_range_lineEmbed (k : LatticeVec) (h1 : k 1 = 0) (h2 : k 2 = 0) :
    k ∈ Set.range lineEmbed := by
  refine ⟨k 0, ?_⟩
  funext i
  fin_cases i
  · rfl
  · simpa [lineEmbed] using h1.symm
  · simpa [lineEmbed] using h2.symm

/-- A real, mean-zero shear profile with geometrically decaying coefficients. -/
private def shearProfile (n : ℤ) : ℂ :=
  if n = 0 then 0 else (((2 : ℝ)⁻¹ ^ n.natAbs : ℝ) : ℂ)

private theorem shearProfile_conj (n : ℤ) :
    shearProfile (-n) = (starRingEnd ℂ) (shearProfile n) := by
  unfold shearProfile
  by_cases h : n = 0
  · simp [h]
  · rw [if_neg h, if_neg (by simpa using h), Int.natAbs_neg]
    exact (Complex.conj_ofReal _).symm

private theorem norm_shearProfile_le (n : ℤ) :
    ‖shearProfile n‖ ≤ ((2 : ℝ)⁻¹) ^ n.natAbs := by
  unfold shearProfile
  by_cases h : n = 0
  · rw [if_pos h]
    simp
  · rw [if_neg h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The Fourier coefficients of the shear field. -/
private def shearCoeff (k : LatticeVec) : CVec :=
  if k 1 = 0 ∧ k 2 = 0 then ![0, shearProfile (k 0), 0] else 0

/-- A smooth solenoidal field that is not a trigonometric polynomial. -/
def shearField : SmoothField where
  coeff := shearCoeff
  meanZero := by
    have hcond : ((0 : LatticeVec) 1 = 0 ∧ (0 : LatticeVec) 2 = 0) := ⟨rfl, rfl⟩
    rw [shearCoeff, if_pos hcond]
    funext i
    fin_cases i <;> simp [shearProfile]
  divergenceFree := by
    intro k
    unfold Transverse shearCoeff
    by_cases hk : k 1 = 0 ∧ k 2 = 0
    · rw [if_pos hk]
      simp [Vec3.dot, latticeToComplex, hk.1]
    · rw [if_neg hk]
      simp [Vec3.dot]
  reality := by
    intro k
    have hiff : ((-k) 1 = 0 ∧ (-k) 2 = 0) ↔ (k 1 = 0 ∧ k 2 = 0) := by
      simp [Pi.neg_apply, neg_eq_zero]
    unfold shearCoeff
    by_cases hk : k 1 = 0 ∧ k 2 = 0
    · rw [if_pos (hiff.mpr hk), if_pos hk]
      funext i
      fin_cases i
      · simp [conjVec]
      · simpa [conjVec] using shearProfile_conj (k 0)
      · simp [conjVec]
    · rw [if_neg (fun h => hk (hiff.mp h)), if_neg hk, conjVec_zero]
  decay := by
    intro N
    have hzero : ∀ x ∉ Set.range lineEmbed, weight N x * ‖shearCoeff x‖ = 0 := by
      intro x hx
      have hcond : ¬(x 1 = 0 ∧ x 2 = 0) := by
        intro h
        exact hx (mem_range_lineEmbed x h.1 h.2)
      rw [shearCoeff, if_neg hcond]
      simp
    refine (Function.Injective.summable_iff lineEmbed_injective hzero).mp ?_
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_int_weight N)
    · exact mul_nonneg (weight_nonneg N _) (norm_nonneg _)
    · have hcond : ((lineEmbed n) 1 = 0 ∧ (lineEmbed n) 2 = 0) := ⟨rfl, rfl⟩
      have hnorm : ‖shearCoeff (lineEmbed n)‖ ≤ ((2 : ℝ)⁻¹) ^ n.natAbs := by
        rw [shearCoeff, if_pos hcond]
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
        fin_cases i
        · simp
        · exact norm_shearProfile_le _
        · simp
      have hw : weight N (lineEmbed n) = ((n.natAbs : ℝ) + 1) ^ N := by
        rw [weight, latticeNorm_lineEmbed]
      simp only [Function.comp_apply, hw]
      exact mul_le_mul_of_nonneg_left hnorm (by positivity)

theorem shearField_support_infinite :
    {k : LatticeVec | shearField.coeff k ≠ 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => lineEmbed ((m : ℤ) + 1)) ?_ ?_
  · intro a b h
    have := lineEmbed_injective h
    omega
  · intro m
    have hcond : ((lineEmbed ((m : ℤ) + 1)) 1 = 0 ∧ (lineEmbed ((m : ℤ) + 1)) 2 = 0) :=
      ⟨rfl, rfl⟩
    have hne : shearProfile ((m : ℤ) + 1) ≠ 0 := by
      rw [shearProfile, if_neg (by omega)]
      simp
    show shearCoeff (lineEmbed ((m : ℤ) + 1)) ≠ 0
    rw [shearCoeff, if_pos hcond]
    intro hzero
    exact hne (by simpa [lineEmbed] using congrFun hzero 1)

/-- The extension is strict: no finite Fourier field has the shear field's
coefficients. -/
theorem shearField_coeff_ne_trig (w : TrigField) :
    shearField.coeff ≠ (w.coeff : LatticeVec → CVec) := by
  intro h
  refine shearField_support_infinite (Set.Finite.subset w.coeff.support.finite_toSet ?_)
  intro k hk
  have hk' : w.coeff k ≠ 0 := by
    rw [← h]
    exact hk
  simpa using hk'

end

end FourierMultiplierRigidity.Smooth
