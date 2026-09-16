import FourierMultiplierRigidity

/-!
# Solenoidal propagation (Lemma 5.3) and Boolean-seed bootstrap

## The one-triad solenoidal determination rule

One unequal-length non-collinear triad suffices to propagate vanishing when
the multiplier has solenoidal output (Lemma 5.3 in the manuscript):

1. `target_image_line_of_vanishing_parents` (root module) gives
   `D(p)a ∈ span(r-q)`.
2. Solenoidal output gives `D(p)a ⊥ p`.
3. `dot_sum_difference` proves `(q+r)·(r-q) = |r|²-|q|²`.
4. When `|q| ≠ |r|`, the direction `r-q` has a nonzero `p`-component,
   so `D(p)a = 0`.

## Bootstrap: Boolean seed → unit cube

Six concrete unequal-length triads (equations (7.1)–(7.2) in the manuscript)
recover the six unit-cube mode classes not in the Boolean seed.  After that,
the existing `vanishes_everywhere_of_unitCube` (two-triad propagation)
carries vanishing to the entire lattice.
-/

namespace FourierMultiplierRigidity

set_option maxRecDepth 4000000

/-! ## Lattice norm-squared -/

def latticeNormSq (k : LatticeVec) : ℤ :=
  k 0 * k 0 + k 1 * k 1 + k 2 * k 2

theorem latticeNormSq_pos {k : LatticeVec} (hk : k ≠ 0) : 0 < latticeNormSq k := by
  unfold latticeNormSq
  by_contra h
  push_neg at h
  have h0 : k 0 = 0 := by
    nlinarith [mul_self_nonneg (k 0), mul_self_nonneg (k 1), mul_self_nonneg (k 2)]
  have h1 : k 1 = 0 := by
    nlinarith [mul_self_nonneg (k 0), mul_self_nonneg (k 1), mul_self_nonneg (k 2)]
  have h2 : k 2 = 0 := by
    nlinarith [mul_self_nonneg (k 0), mul_self_nonneg (k 1), mul_self_nonneg (k 2)]
  exact hk (funext fun i => by fin_cases i <;> assumption)

/-! ## The dot-product identity (q+r)·(r-q) = |r|² - |q|² -/

theorem dot_sum_difference (q r : LatticeVec) :
    Vec3.dot (latticeToComplex (q + r)) (latticeToComplex (r - q)) =
      ((latticeNormSq r - latticeNormSq q : ℤ) : ℂ) := by
  simp only [Vec3.dot, latticeToComplex, latticeNormSq, Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

/-! ## Parallel-plus-transverse forces zero -/

theorem Vec3.dot_neg_left' (u v : CVec) :
    Vec3.dot (-u) v = -Vec3.dot u v := by
  simp [Vec3.dot, Pi.neg_apply]; ring

theorem eq_zero_of_parallel_and_transverse (k d y : CVec)
    (hkd : Vec3.dot k d ≠ 0)
    (hpar : ParallelC y d) (htrans : Vec3.dot k y = 0) : y = 0 := by
  obtain ⟨c, hc⟩ := hpar
  have hdot : c * Vec3.dot k d = 0 := by
    calc c * Vec3.dot k d
        = Vec3.dot k (c • d) := by simp [Vec3.dot]; ring
      _ = Vec3.dot k y := by rw [hc]
      _ = 0 := htrans
  have hc0 : c = 0 := (mul_eq_zero.mp hdot).resolve_right hkd
  rw [hc, hc0, zero_smul]

/-! ## Solenoidal output for bare maps -/

def HasSolenoidalOutputMap (D : LatticeVec → CVec →ₗ[ℂ] CVec) : Prop :=
  ∀ (k : LatticeVec), k ≠ 0 → ∀ (v : CVec), Transverse k v →
    Transverse k (D k v)

theorem hasSolenoidalOutputMap_of_hasSolenoidalOutput (R : MultiplierSymbol)
    (h : HasSolenoidalOutput R) : HasSolenoidalOutputMap R.map :=
  fun k hk v hv => h k hk v hv

/-! ## Lemma 5.3: one-triad solenoidal determination -/

theorem neg_latticeToComplex (k : LatticeVec) :
    latticeToComplex (-k) = -latticeToComplex k := by
  funext i; simp [latticeToComplex]

theorem solenoidal_one_triad_vanishing
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hD : HasActiveTriadCancellation D)
    (hsol : HasSolenoidalOutputMap D)
    (p q r : LatticeVec) (hpqr : p + q + r = 0)
    (hnc : LatticeNonCollinear q r)
    (hq : VanishesAt D q) (hr : VanishesAt D r)
    (huneq : latticeNormSq q ≠ latticeNormSq r) :
    VanishesAt D p := by
  have hp : p ≠ 0 := recipient_ne_zero_of_noncollinear hpqr hnc
  intro a ha
  have hline := target_image_line_of_vanishing_parents D hD p q r hpqr hnc hq hr a ha
  have htrans : Vec3.dot (latticeToComplex p) (D p a) = 0 :=
    hsol p hp a ha
  have hpeq : p = -(q + r) := by
    funext i
    have hi := congrFun hpqr i
    change p i = -(q i + r i)
    simp only [Pi.add_apply, Pi.zero_apply] at hi
    omega
  have hkd : Vec3.dot (latticeToComplex p) (latticeToComplex (r - q)) ≠ 0 := by
    rw [hpeq, neg_latticeToComplex, Vec3.dot_neg_left', dot_sum_difference]
    simp only [ne_eq, neg_eq_zero, Int.cast_eq_zero]
    omega
  exact eq_zero_of_parallel_and_transverse
    (latticeToComplex p) (latticeToComplex (r - q)) (D p a) hkd hline htrans

/-! ## Solenoidal propagation certificate -/

structure SolenoidalPropagationCertificate (t : LatticeVec) where
  q : LatticeVec
  r : LatticeVec
  sum : q + r = t
  noncollinear : LatticeNonCollinear q r
  unequalLengths : latticeNormSq q ≠ latticeNormSq r

theorem solenoidal_propagation_step
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hD : HasActiveTriadCancellation D)
    (hsol : HasSolenoidalOutputMap D) (hreal : RealityCompatibleMap D)
    (t : LatticeVec) (cert : SolenoidalPropagationCertificate t)
    (hq : VanishesAt D cert.q) (hr : VanishesAt D cert.r) :
    VanishesAt D t := by
  have hpqr : (-t) + cert.q + cert.r = 0 := by
    have := cert.sum; funext i; have hi := congrFun this i; simp at hi ⊢; omega
  have hvanish_neg := solenoidal_one_triad_vanishing D hD hsol (-t)
    cert.q cert.r hpqr cert.noncollinear hq hr cert.unequalLengths
  rwa [vanishesAt_neg_iff_of_reality D hreal t] at hvanish_neg

/-! ## Bootstrap: Boolean seed → unit cube

The seven Boolean seed mode classes are
  (1,0,0), (0,1,0), (0,0,1), (1,1,0), (1,0,1), (0,1,1), (1,1,1).

Six unequal-length triads recover the remaining unit-cube classes:

Step 1: (1,-1,-1) = (1,0,0) + (0,-1,-1)   [|q|²=1, |r|²=2]
Step 2: (-1,1,-1) = (0,1,0) + (-1,0,-1)   [|q|²=1, |r|²=2]
Step 3: (-1,-1,1) = (0,0,1) + (-1,-1,0)   [|q|²=1, |r|²=2]
Step 4: (1,-1,0)  = (1,-1,-1) + (0,0,1)   [|q|²=3, |r|²=1]
Step 5: (1,0,-1)  = (1,-1,-1) + (0,1,0)   [|q|²=3, |r|²=1]
Step 6: (0,1,-1)  = (-1,1,-1) + (1,0,0)   [|q|²=3, |r|²=1]
-/

private def step1_cert : SolenoidalPropagationCertificate (latticeVec 1 (-1) (-1)) where
  q := latticeVec 1 0 0
  r := latticeVec 0 (-1) (-1)
  sum := by funext i; fin_cases i <;> simp [latticeVec]
  noncollinear := by
    intro h; simp [LatticeNonCollinear, Vec3.cross, latticeToReal, latticeVec] at h
  unequalLengths := by simp [latticeNormSq, latticeVec]

private def step2_cert : SolenoidalPropagationCertificate (latticeVec (-1) 1 (-1)) where
  q := latticeVec 0 1 0
  r := latticeVec (-1) 0 (-1)
  sum := by funext i; fin_cases i <;> simp [latticeVec]
  noncollinear := by
    intro h; simp [LatticeNonCollinear, Vec3.cross, latticeToReal, latticeVec] at h
  unequalLengths := by simp [latticeNormSq, latticeVec]

private def step3_cert : SolenoidalPropagationCertificate (latticeVec (-1) (-1) 1) where
  q := latticeVec 0 0 1
  r := latticeVec (-1) (-1) 0
  sum := by funext i; fin_cases i <;> simp [latticeVec]
  noncollinear := by
    intro h; simp [LatticeNonCollinear, Vec3.cross, latticeToReal, latticeVec] at h
  unequalLengths := by simp [latticeNormSq, latticeVec]

private def step4_cert : SolenoidalPropagationCertificate (latticeVec 1 (-1) 0) where
  q := latticeVec 1 (-1) (-1)
  r := latticeVec 0 0 1
  sum := by funext i; fin_cases i <;> simp [latticeVec]
  noncollinear := by
    intro h; simp [LatticeNonCollinear, Vec3.cross, latticeToReal, latticeVec] at h
  unequalLengths := by simp [latticeNormSq, latticeVec]

private def step5_cert : SolenoidalPropagationCertificate (latticeVec 1 0 (-1)) where
  q := latticeVec 1 (-1) (-1)
  r := latticeVec 0 1 0
  sum := by funext i; fin_cases i <;> simp [latticeVec]
  noncollinear := by
    intro h; simp [LatticeNonCollinear, Vec3.cross, latticeToReal, latticeVec] at h
  unequalLengths := by simp [latticeNormSq, latticeVec]

private def step6_cert : SolenoidalPropagationCertificate (latticeVec 0 1 (-1)) where
  q := latticeVec (-1) 1 (-1)
  r := latticeVec 1 0 0
  sum := by funext i; fin_cases i <;> simp [latticeVec]
  noncollinear := by
    intro h; simp [LatticeNonCollinear, Vec3.cross, latticeToReal, latticeVec] at h
  unequalLengths := by simp [latticeNormSq, latticeVec]

/-- Vanishing on the seven positive Boolean seed mode classes. -/
def VanishesOnBooleanSeed (D : LatticeVec → CVec →ₗ[ℂ] CVec) : Prop :=
  VanishesAt D (latticeVec 1 0 0) ∧
  VanishesAt D (latticeVec 0 1 0) ∧
  VanishesAt D (latticeVec 0 0 1) ∧
  VanishesAt D (latticeVec 1 1 0) ∧
  VanishesAt D (latticeVec 1 0 1) ∧
  VanishesAt D (latticeVec 0 1 1) ∧
  VanishesAt D (latticeVec 1 1 1)

private theorem neg_latticeVec (a b c : ℤ) :
    -latticeVec a b c = latticeVec (-a) (-b) (-c) := by
  funext i; fin_cases i <;> simp [latticeVec]

/-- From vanishing on the Boolean seed, derive vanishing on their negatives. -/
private theorem vanishes_neg_booleanSeed
    (D : LatticeVec → CVec →ₗ[ℂ] CVec) (hreal : RealityCompatibleMap D)
    (hB : VanishesOnBooleanSeed D) :
    VanishesAt D (latticeVec (-1) 0 0) ∧
    VanishesAt D (latticeVec 0 (-1) 0) ∧
    VanishesAt D (latticeVec 0 0 (-1)) ∧
    VanishesAt D (latticeVec (-1) (-1) 0) ∧
    VanishesAt D (latticeVec (-1) 0 (-1)) ∧
    VanishesAt D (latticeVec 0 (-1) (-1)) ∧
    VanishesAt D (latticeVec (-1) (-1) (-1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [neg_latticeVec, neg_zero] using
      vanishesAt_neg_of_reality D hreal (latticeVec 1 0 0) h1
  · simpa only [neg_latticeVec, neg_zero] using
      vanishesAt_neg_of_reality D hreal (latticeVec 0 1 0) h2
  · simpa only [neg_latticeVec, neg_zero] using
      vanishesAt_neg_of_reality D hreal (latticeVec 0 0 1) h3
  · simpa only [neg_latticeVec, neg_zero] using
      vanishesAt_neg_of_reality D hreal (latticeVec 1 1 0) h4
  · simpa only [neg_latticeVec, neg_zero] using
      vanishesAt_neg_of_reality D hreal (latticeVec 1 0 1) h5
  · simpa only [neg_latticeVec, neg_zero] using
      vanishesAt_neg_of_reality D hreal (latticeVec 0 1 1) h6
  · simpa only [neg_latticeVec, neg_zero] using
      vanishesAt_neg_of_reality D hreal (latticeVec 1 1 1) h7

/-- **Bootstrap theorem.** If `D` has active triad cancellation, solenoidal
output, and reality compatibility, and vanishes on the Boolean seed, then it
vanishes on the entire coordinate unit cube. -/
theorem vanishes_on_unitCube_of_booleanSeed
    (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hD : HasActiveTriadCancellation D)
    (hsol : HasSolenoidalOutputMap D) (hreal : RealityCompatibleMap D)
    (hB : VanishesOnBooleanSeed D) :
    ∀ k, k ≠ 0 → InUnitCube k → VanishesAt D k := by
  have hBcopy := hB
  obtain ⟨he₁, he₂, he₃, he₁₂, he₁₃, he₂₃, he₁₂₃⟩ := hB
  obtain ⟨hne₁, hne₂, hne₃, hne₁₂, hne₁₃, hne₂₃, hne₁₂₃⟩ :=
    vanishes_neg_booleanSeed D hreal hBcopy
  -- Step 1: (1,-1,-1)
  have hstep1 : VanishesAt D (latticeVec 1 (-1) (-1)) :=
    solenoidal_propagation_step D hD hsol hreal _ step1_cert he₁ hne₂₃
  -- Step 2: (-1,1,-1)
  have hstep2 : VanishesAt D (latticeVec (-1) 1 (-1)) :=
    solenoidal_propagation_step D hD hsol hreal _ step2_cert he₂ hne₁₃
  -- Step 3: (-1,-1,1)
  have hstep3 : VanishesAt D (latticeVec (-1) (-1) 1) :=
    solenoidal_propagation_step D hD hsol hreal _ step3_cert he₃ hne₁₂
  -- Step 4: (1,-1,0)
  have hstep4 : VanishesAt D (latticeVec 1 (-1) 0) :=
    solenoidal_propagation_step D hD hsol hreal _ step4_cert hstep1 he₃
  -- Step 5: (1,0,-1)
  have hstep5 : VanishesAt D (latticeVec 1 0 (-1)) :=
    solenoidal_propagation_step D hD hsol hreal _ step5_cert hstep1 he₂
  -- Step 6: (0,1,-1)
  have hstep6 : VanishesAt D (latticeVec 0 1 (-1)) :=
    solenoidal_propagation_step D hD hsol hreal _ step6_cert hstep2 he₁
  -- Negatives of the six new modes
  have hstep1n : VanishesAt D (latticeVec (-1) 1 1) := by
    rw [show latticeVec (-1) 1 1 = -(latticeVec 1 (-1) (-1)) from by
      funext i; fin_cases i <;> simp [latticeVec]]
    exact vanishesAt_neg_of_reality D hreal _ hstep1
  have hstep2n : VanishesAt D (latticeVec 1 (-1) 1) := by
    rw [show latticeVec 1 (-1) 1 = -(latticeVec (-1) 1 (-1)) from by
      funext i; fin_cases i <;> simp [latticeVec]]
    exact vanishesAt_neg_of_reality D hreal _ hstep2
  have hstep3n : VanishesAt D (latticeVec 1 1 (-1)) := by
    rw [show latticeVec 1 1 (-1) = -(latticeVec (-1) (-1) 1) from by
      funext i; fin_cases i <;> simp [latticeVec]]
    exact vanishesAt_neg_of_reality D hreal _ hstep3
  have hstep4n : VanishesAt D (latticeVec (-1) 1 0) := by
    rw [show latticeVec (-1) 1 0 = -(latticeVec 1 (-1) 0) from by
      funext i; fin_cases i <;> simp [latticeVec]]
    exact vanishesAt_neg_of_reality D hreal _ hstep4
  have hstep5n : VanishesAt D (latticeVec (-1) 0 1) := by
    rw [show latticeVec (-1) 0 1 = -(latticeVec 1 0 (-1)) from by
      funext i; fin_cases i <;> simp [latticeVec]]
    exact vanishesAt_neg_of_reality D hreal _ hstep5
  have hstep6n : VanishesAt D (latticeVec 0 (-1) 1) := by
    rw [show latticeVec 0 (-1) 1 = -(latticeVec 0 1 (-1)) from by
      funext i; fin_cases i <;> simp [latticeVec]]
    exact vanishesAt_neg_of_reality D hreal _ hstep6
  -- Now we have VanishesAt for all 26 signed nonzero unit-cube modes.
  -- Dispatch by case analysis.
  intro k hk hcube
  have h0 : k 0 = -1 ∨ k 0 = 0 ∨ k 0 = 1 := by have := hcube 0; omega
  have h1 : k 1 = -1 ∨ k 1 = 0 ∨ k 1 = 1 := by have := hcube 1; omega
  have h2 : k 2 = -1 ∨ k 2 = 0 ∨ k 2 = 1 := by have := hcube 2; omega
  have hne : ¬(k 0 = 0 ∧ k 1 = 0 ∧ k 2 = 0) := by
    rintro ⟨a, b, c⟩; exact hk (funext fun i => by fin_cases i <;> assumption)
  have hlv : k = latticeVec (k 0) (k 1) (k 2) := by
    funext i; fin_cases i <;> rfl
  rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
    rcases h2 with h2 | h2 | h2 <;>
    first
    | exact False.elim (hne ⟨h0, h1, h2⟩)
    | (have heq := hlv
       rw [h0, h1, h2] at heq
       rw [heq]
       assumption)

/-- **Solenoidal vanishing from Boolean seed to everywhere.** Combines the
bootstrap with the existing two-triad lattice propagation. -/
theorem solenoidal_vanishes_everywhere_of_booleanSeed
    (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hD : HasActiveTriadCancellation D)
    (hsol : HasSolenoidalOutputMap D) (hreal : RealityCompatibleMap D)
    (hB : VanishesOnBooleanSeed D) :
    ∀ k, k ≠ 0 → VanishesAt D k :=
  vanishes_everywhere_of_unitCube D hD hreal
    (vanishes_on_unitCube_of_booleanSeed D hD hsol hreal hB)

/-! ## Arbitrary-length unequal-triad orderings (Definition 5.1, general `M`)

The six bootstrap steps above are six *hand-picked* instances of
`solenoidal_propagation_step`, chained by hand.  The manuscript's Definition
5.1 (`unequal-triad ordering`) allows an arbitrary finite sequence of such
steps, of any length `M - 7`, as long as each new target's two parents were
already reached earlier in the sequence (or lie in the Boolean seed).  This
section formalizes that general notion and proves, by induction on the
sequence, that active triad cancellation plus solenoidal output plus
reality compatibility propagates vanishing along *any* valid ordering, not
just the length-six bootstrap.  This is the qualitative determination
property behind Theorem D's geometric observation families: each step of a
valid ordering supplies exactly the transverse-fiber vanishing (i.e. the
concrete triad-supported test-field observations of Lemma 5.3) needed to
reach the next mode, for a symbol space of any size `M`. -/

/-- One step of an unequal-triad ordering: a target together with the data
that its two parents (`cert.q`, `cert.r`) are unequal in length,
non-collinear, and sum to the target. -/
abbrev OrderingStep := Σ t : LatticeVec, SolenoidalPropagationCertificate t

/-- The list of modes known after replaying an ordering starting from
`seed`: each step's target is appended once its parents are already
known. -/
def buildKnown (seed : List LatticeVec) (ordering : List OrderingStep) :
    List LatticeVec :=
  ordering.foldl (fun known step => known ++ [step.1]) seed

@[simp] theorem buildKnown_nil (seed : List LatticeVec) :
    buildKnown seed [] = seed := rfl

@[simp] theorem buildKnown_cons (seed : List LatticeVec) (step : OrderingStep)
    (rest : List OrderingStep) :
    buildKnown seed (step :: rest) = buildKnown (seed ++ [step.1]) rest := rfl

/-- **Validity of an unequal-triad ordering.**  Each step's parents must
already be known — either in the original `seed` or the target of an
earlier step in the sequence. -/
def ValidOrderingFrom (known : List LatticeVec) : List OrderingStep → Prop
  | [] => True
  | step :: rest =>
      step.2.q ∈ known ∧ step.2.r ∈ known ∧
        ValidOrderingFrom (known ++ [step.1]) rest

/-- **General unequal-triad propagation.**  If `D` has active triad
cancellation, solenoidal output and reality compatibility, and vanishes on
every mode of `seed`, then it vanishes on every mode reached by *any* valid
unequal-triad ordering built from `seed`, of any length.  This generalizes
the six hard-coded bootstrap steps above to an arbitrary admissible
ordering, matching Definition 5.1 and Theorem D for general mode-set
size `M`. -/
theorem vanishes_of_validOrdering
    (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hD : HasActiveTriadCancellation D)
    (hsol : HasSolenoidalOutputMap D) (hreal : RealityCompatibleMap D) :
    ∀ (ordering : List OrderingStep) (seed : List LatticeVec),
      (∀ k ∈ seed, VanishesAt D k) → ValidOrderingFrom seed ordering →
      ∀ k ∈ buildKnown seed ordering, VanishesAt D k := by
  intro ordering
  induction ordering with
  | nil => intro seed hseed _ k hk; exact hseed k (by simpa using hk)
  | cons step rest ih =>
    intro seed hseed hvalid
    obtain ⟨hq, hr, hrest⟩ := hvalid
    have hvq : VanishesAt D step.2.q := hseed _ hq
    have hvr : VanishesAt D step.2.r := hseed _ hr
    have hvt : VanishesAt D step.1 :=
      solenoidal_propagation_step D hD hsol hreal step.1 step.2 hvq hvr
    have hseed' : ∀ k ∈ seed ++ [step.1], VanishesAt D k := by
      intro k hk
      rcases List.mem_append.mp hk with h | h
      · exact hseed k h
      · rw [List.mem_singleton] at h; subst h; exact hvt
    simpa [buildKnown_cons] using ih (seed ++ [step.1]) hseed' hrest

/-! ### A concrete step beyond the unit cube

Instantiating `vanishes_of_validOrdering` on the six bootstrap steps
recovers `vanishes_on_unitCube_of_booleanSeed`; the point of the general
theorem is that it also covers modes outside the unit cube.  The following
is one such step: `(2,-1,-1) = (1,-1,-1) + (1,0,0)`, whose parents are
`(1,-1,-1)` (reached by `step1_cert` above) and `(1,0,0)` (a Boolean seed
mode). The two parents have unequal squared length (`3` versus `1`) and are
non-collinear, so this is a valid unequal-triad step reaching a mode with
`ℓ∞`-norm `2`, strictly outside the unit cube. -/

private def step7_cert : SolenoidalPropagationCertificate (latticeVec 2 (-1) (-1)) where
  q := latticeVec 1 (-1) (-1)
  r := latticeVec 1 0 0
  sum := by funext i; fin_cases i <;> simp [latticeVec]
  noncollinear := by
    intro h; simp [LatticeNonCollinear, Vec3.cross, latticeToReal, latticeVec] at h
  unequalLengths := by simp [latticeNormSq, latticeVec]

/-- **One propagation step beyond the unit cube.**  If `D` vanishes on the
Boolean seed and on the first unit-cube bootstrap step (both already
established by `vanishes_on_unitCube_of_booleanSeed`), then it also
vanishes at `(2,-1,-1)`, a mode outside the unit cube. This is a genuine
instance of `vanishes_of_validOrdering` beyond the six hard-coded bootstrap
steps, demonstrating that the general theorem reaches new geometric
observations, not just the ones already hard-coded. -/
theorem vanishes_at_stepBeyondUnitCube
    (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hD : HasActiveTriadCancellation D)
    (hsol : HasSolenoidalOutputMap D) (hreal : RealityCompatibleMap D)
    (hB : VanishesOnBooleanSeed D) :
    VanishesAt D (latticeVec 2 (-1) (-1)) := by
  have hcube := vanishes_on_unitCube_of_booleanSeed D hD hsol hreal hB
  have h1 : VanishesAt D (latticeVec 1 (-1) (-1)) :=
    hcube (latticeVec 1 (-1) (-1)) (by simp [latticeVec])
      (by intro i; fin_cases i <;> simp [latticeVec])
  have h2 : VanishesAt D (latticeVec 1 0 0) :=
    hB.1
  exact solenoidal_propagation_step D hD hsol hreal _ step7_cert h1 h2

end FourierMultiplierRigidity

