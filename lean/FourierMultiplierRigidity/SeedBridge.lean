import FourierMultiplierRigidity

/-!
# The semantic seed bridge

`FourierMultiplierRigidity.lean` proves, kernel-checked, that the thirteen-mode
unit-cube constraint matrix has rank `144`, and that any seed parameter
annihilated by the selected `144` constraints is a generator.  What it does not
prove is that those rows *are* the constraints imposed by the Euler triad
identity on an actual multiplier symbol.  Without that link the rank
computation is a statement about an integer matrix and nothing more.

This file supplies the missing link.  The main result is

* `seedConstraints_of_triadCancellation` — a reality-compatible symbol family
  with active triad cancellation satisfies every selected seed constraint.

The route is:

1. transport of symbol values between a signed mode and its representative,
   using only reality compatibility (`value_re`, `value_im`);
2. expansion of a transverse input in the two-vector seed frame
   (`frame_expansion`), which is where `seed_frame_decomposition` is used;
3. the single-recipient column identity (`recipient_column_sum`): pairing one
   recipient block of a row against the encoding reproduces the real or
   imaginary part of that term of the triad bracket;
4. assembly of the three recipients into a whole row
   (`constraintRowZ_annihilates`), and then over every row of `rowsZ`.

Everything here is kernel-checked: the finite lookup facts about `seed`,
`triads` and `polarizationTriples` are discharged by `decide`, not
`native_decide`.
-/

namespace FourierMultiplierRigidity
open SeedCertificate
open scoped ComplexConjugate
set_option maxRecDepth 4000000

/-! ## Stage 1: reality transport of symbol values -/

@[simp] theorem conjVec_realToComplexVec (f : RVec) :
    conjVec (realToComplexVec f) = realToComplexVec f := by
  funext i; simp [conjVec, realToComplexVec]

theorem reality_value_neg (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (k : LatticeVec) (f : RVec)
    (hf : TransverseR k f) :
    D (-k) (realToComplexVec f) = conjVec (D k (realToComplexVec f)) := by
  have h := hreal k (realToComplexVec f) (transverse_complexification hf)
  rwa [conjVec_realToComplexVec] at h

/-! ## Stage 2: `IVec` arithmetic matches vector-space arithmetic -/

theorem dot_realOfIVec (a b : IVec) :
    Vec3.dot (realOfIVec a) (realOfIVec b) = (SeedCertificate.dot a b : ℝ) := by
  simp [Vec3.dot, realOfIVec, SeedCertificate.dot]

theorem dot_complexOfIVec (a b : IVec) :
    Vec3.dot (realToComplexVec (realOfIVec a)) (realToComplexVec (realOfIVec b)) =
      ((SeedCertificate.dot a b : ℤ) : ℂ) := by
  simp [Vec3.dot, realOfIVec, realToComplexVec, SeedCertificate.dot]

theorem rawRecipient_of_rawZ (q r u v : IVec) :
    rawRecipient (latticeOfIVec q) (latticeOfIVec r)
        (realToComplexVec (realOfIVec u)) (realToComplexVec (realOfIVec v)) =
      realToComplexVec (realOfIVec (rawZ q r u v)) := by
  funext i
  fin_cases i <;>
    simp [rawRecipient, rawZ, addZ, smulZ, dotZ, castVecZ, realOfIVec,
      realToComplexVec, latticeToComplex_latticeOfIVec, Vec3.dot]

theorem latticeOfIVec_neg (k : IVec) :
    latticeOfIVec (neg k) = -latticeOfIVec k := by
  funext i
  fin_cases i <;> simp [latticeOfIVec, latticeVec, neg]

theorem dot_neg_left (a b : IVec) :
    SeedCertificate.dot (neg a) b = -SeedCertificate.dot a b := by
  simp [SeedCertificate.dot, neg]; ring

theorem dot_realToComplexVec_re (z : CVec) (W : RVec) :
    (Vec3.dot z (realToComplexVec W)).re =
      (z 0).re * W 0 + (z 1).re * W 1 + (z 2).re * W 2 := by
  simp [Vec3.dot, realToComplexVec, Complex.add_re, Complex.mul_re]

theorem dot_realToComplexVec_im (z : CVec) (W : RVec) :
    (Vec3.dot z (realToComplexVec W)).im =
      (z 0).im * W 0 + (z 1).im * W 1 + (z 2).im * W 2 := by
  simp [Vec3.dot, realToComplexVec, Complex.add_im, Complex.mul_im]

/-! ## Stage 3: finite seed lookup facts, kernel-checked -/

theorem seed_modeIndex_lt : ∀ k ∈ seed, modeIndex k < 13 := by decide
theorem seed_rep_eq_getD :
    ∀ k ∈ seed, representatives.getD (modeIndex k) zero = representative k := by decide
theorem seed_eq_rep_or_neg :
    ∀ k ∈ seed, k = representative k ∨ k = neg (representative k) := by decide

theorem seed_frame_transverse : ∀ m ∈ List.range 13, ∀ i ∈ List.range 2,
      SeedCertificate.dot (seedModeIVec m) (seedFrameIVec m i) = 0 := by
  decide

/-! ## Stage 4: column bookkeeping -/

def colEquiv : Fin 13 × Fin 12 ≃ Fin 156 where
  toFun p := ⟨12 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun j := (⟨j.val / 12, by have := j.isLt; omega⟩, ⟨j.val % 12, by omega⟩)
  left_inv := by rintro ⟨⟨m, hm⟩, ⟨w, hw⟩⟩; ext <;> simp <;> omega
  right_inv := by rintro ⟨j, hj⟩; ext; simp; omega

theorem sum_fin156_split (F : Fin 156 → ℝ) :
    ∑ j : Fin 156, F j = ∑ m : Fin 13, ∑ w : Fin 12, F (colEquiv (m, w)) := by
  rw [← Equiv.sum_comp colEquiv F, Fintype.sum_prod_type]

@[simp] theorem colEquiv_mode (m : Fin 13) (w : Fin 12) :
    (colEquiv (m, w)).val / 12 = m.val := by
  have hw := w.isLt
  show (12 * m.val + w.val) / 12 = m.val
  omega

@[simp] theorem colEquiv_within (m : Fin 13) (w : Fin 12) :
    (colEquiv (m, w)).val % 12 = w.val := by
  have hw := w.isLt
  show (12 * m.val + w.val) % 12 = w.val
  omega

/-! ## Stage 5: expansion of a transverse input in the seed frame -/

noncomputable def frameCoord (x : IVec) (m i : Nat) : ℝ :=
  (SeedCertificate.dot x (seedFrameIVec m i) : ℝ) / seedFrameNorm m i

noncomputable def blockValue (D : LatticeVec → CVec →ₗ[ℂ] CVec) (m i : Nat) : CVec :=
  D (seedMode m) (realToComplexVec (seedFrameReal m i))

theorem seedMode_modeIndex (k : IVec) (hk : k ∈ seed) :
    seedMode (modeIndex k) = latticeOfIVec (representative k) := by
  unfold seedMode seedModeIVec
  rw [seed_rep_eq_getD k hk]

theorem transverse_of_dot_zero (k x : IVec) (h : SeedCertificate.dot k x = 0) :
    Transverse (latticeOfIVec k) (realToComplexVec (realOfIVec x)) := by
  unfold Transverse
  rw [latticeToComplex_latticeOfIVec, dot_complexOfIVec, h]
  simp

theorem frame_expansion (k : IVec) (hk : k ∈ seed) (x : IVec)
    (hx : SeedCertificate.dot k x = 0) :
    realToComplexVec (realOfIVec x) =
      ((frameCoord x (modeIndex k) 0 : ℝ) : ℂ) •
          realToComplexVec (seedFrameReal (modeIndex k) 0) +
      ((frameCoord x (modeIndex k) 1 : ℝ) : ℂ) •
          realToComplexVec (seedFrameReal (modeIndex k) 1) := by
  have hrep : SeedCertificate.dot (representative k) x = 0 := by
    rcases seed_eq_rep_or_neg k hk with h | h
    · rw [← h]; exact hx
    · have h2 : SeedCertificate.dot (neg (representative k)) x = 0 := by rw [← h]; exact hx
      rw [dot_neg_left] at h2
      linarith
  have htr : Transverse (seedMode (modeIndex k)) (realToComplexVec (realOfIVec x)) := by
    rw [seedMode_modeIndex k hk]
    exact transverse_of_dot_zero _ _ hrep
  have hdec := seed_frame_decomposition ⟨modeIndex k, seed_modeIndex_lt k hk⟩
    (realToComplexVec (realOfIVec x)) htr
  simp only [seedFrameComplex] at hdec
  rw [hdec]
  congr 1 <;>
  · congr 1
    rw [seedFrameReal, dot_complexOfIVec]
    unfold frameCoord seedFrameNorm
    push_cast
    ring

/-! ## Stage 6: real and imaginary components of a symbol value -/

/-- Every seed mode is either its own representative, or strictly the negative
of it; never both. -/
theorem seed_rep_dichotomy : ∀ k ∈ seed,
    k = representative k ∨ (k ≠ representative k ∧ k = neg (representative k)) := by
  decide

noncomputable def seedSign (k : IVec) : ℝ :=
  if k = representative k then 1 else -1

theorem transverseR_seedFrame (m i : Nat) (hm : m < 13) (hi : i < 2) :
    TransverseR (seedMode m) (seedFrameReal m i) := by
  unfold TransverseR seedMode seedFrameReal
  rw [latticeToReal_latticeOfIVec, dot_realOfIVec,
    seed_frame_transverse m (List.mem_range.mpr hm) i (List.mem_range.mpr hi)]
  simp

/-- The block at a signed seed mode is the representative block, conjugated
when the mode is the negative of its representative. -/
theorem value_frame_eq (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (k : IVec) (hk : k ∈ seed) (i : Nat) (hi : i < 2) :
    D (latticeOfIVec k) (realToComplexVec (seedFrameReal (modeIndex k) i)) =
      if k = representative k then blockValue D (modeIndex k) i
      else conjVec (blockValue D (modeIndex k) i) := by
  have hm := seed_modeIndex_lt k hk
  have hmode := seedMode_modeIndex k hk
  rcases seed_rep_dichotomy k hk with h | ⟨hne, h⟩
  · rw [if_pos h]
    unfold blockValue
    have hpos : latticeOfIVec k = seedMode (modeIndex k) := by
      rw [hmode]; conv_lhs => rw [h]
    rw [hpos]
  · rw [if_neg hne]
    have hneg : latticeOfIVec k = -(seedMode (modeIndex k)) := by
      rw [hmode]
      conv_lhs => rw [h]
      rw [latticeOfIVec_neg]
    rw [hneg]
    exact reality_value_neg D hreal _ _ (transverseR_seedFrame _ i hm hi)

theorem value_re (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (k : IVec) (hk : k ∈ seed) (x : IVec)
    (hx : SeedCertificate.dot k x = 0) (o : Fin 3) :
    (D (latticeOfIVec k) (realToComplexVec (realOfIVec x)) o).re =
      frameCoord x (modeIndex k) 0 * (blockValue D (modeIndex k) 0 o).re +
      frameCoord x (modeIndex k) 1 * (blockValue D (modeIndex k) 1 o).re := by
  rw [frame_expansion k hk x hx, map_add, map_smul, map_smul,
    value_frame_eq D hreal k hk 0 (by norm_num),
    value_frame_eq D hreal k hk 1 (by norm_num)]
  by_cases h : k = representative k
  · simp only [if_pos h]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re,
      ]
  · simp only [if_neg h]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re,
      conjVec]

theorem value_im (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (k : IVec) (hk : k ∈ seed) (x : IVec)
    (hx : SeedCertificate.dot k x = 0) (o : Fin 3) :
    (D (latticeOfIVec k) (realToComplexVec (realOfIVec x)) o).im =
      seedSign k *
        (frameCoord x (modeIndex k) 0 * (blockValue D (modeIndex k) 0 o).im +
         frameCoord x (modeIndex k) 1 * (blockValue D (modeIndex k) 1 o).im) := by
  rw [frame_expansion k hk x hx, map_add, map_smul, map_smul,
    value_frame_eq D hreal k hk 0 (by norm_num),
    value_frame_eq D hreal k hk 1 (by norm_num)]
  unfold seedSign
  by_cases h : k = representative k
  · simp only [if_pos h]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im,
      ]
  · simp only [if_neg h]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im,
      conjVec]
    ring

/-! ## Stage 7: the single-recipient column sum -/

theorem constraintRowZ_entry (p q r a u v : IVec) (b : Bool) (j : Fin 156) :
    (constraintRowZ p q r a u v b).getD j.val 0 =
      if (j.val % 2 = 1) = (b = true) then bracketCoefficientZ p q r a u v j.val else 0 := by
  unfold constraintRowZ
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [j.isLt]

theorem colEquiv_parity (m : Fin 13) (w : Fin 12) :
    (colEquiv (m, w)).val % 2 = w.val % 2 := by
  show (12 * m.val + w.val) % 2 = w.val % 2
  omega

theorem frame_getD_eq (k : IVec) (hk : k ∈ seed) (i : Nat) :
    (frame (representative k)).getD i zero = seedFrameIVec (modeIndex k) i := by
  unfold seedFrameIVec seedModeIVec
  rw [seed_rep_eq_getD k hk]

@[simp] theorem componentZ_zero (W : IVec) :
    ((componentZ W 0 : Int) : ℝ) = realOfIVec W 0 := by simp [componentZ, realOfIVec]
@[simp] theorem componentZ_one (W : IVec) :
    ((componentZ W 1 : Int) : ℝ) = realOfIVec W 1 := by simp [componentZ, realOfIVec]
@[simp] theorem componentZ_two (W : IVec) :
    ((componentZ W 2 : Int) : ℝ) = realOfIVec W 2 := by simp [componentZ, realOfIVec]

/-- The recipient coefficient at the representative mode, in frame terms. -/
theorem recipientCoefficientZ_at (k x W : IVec) (hk : k ∈ seed)
    (o i part : Nat) :
    ((recipientCoefficientZ k x W (modeIndex k) o i part : Int) : ℝ) =
      (SeedCertificate.dot x (seedFrameIVec (modeIndex k) i) : ℝ)
        * ((componentZ W o : Int) : ℝ)
        * (if part = 0 then 1 else seedSign k) := by
  unfold recipientCoefficientZ
  rw [if_pos rfl]
  simp only [frame_getD_eq k hk i]
  unfold seedSign
  by_cases hp : part = 0
  · simp only [if_pos hp]
    push_cast
    ring
  · simp only [if_neg hp]
    by_cases hr : k = representative k
    · simp only [if_pos hr]
      push_cast
      ring
    · simp only [if_neg hr]
      push_cast
      ring

/-- `seedEncoding` read off a split column. -/
theorem seedEncoding_col (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (m : Fin 13) (w : Fin 12) (o : Fin 3) (ho : o.val = w.val / 4) :
    seedEncoding D (colEquiv (m, w)) =
      (if w.val % 2 = 0 then (blockValue D m.val ((w.val % 4) / 2) o).re
       else (blockValue D m.val ((w.val % 4) / 2) o).im)
        / seedFrameNorm m.val ((w.val % 4) / 2) := by
  unfold seedEncoding blockValue
  simp only [colEquiv_mode, colEquiv_within]
  have hfin : (⟨w.val / 4, by have := w.isLt; omega⟩ : Fin 3) = o := by
    ext; simpa using ho.symm
  rw [hfin]

/-- The twelve columns of one mode split as (output, input, part). -/
def wEquiv : Fin 3 × Fin 2 × Fin 2 ≃ Fin 12 where
  toFun t := ⟨4 * t.1.val + 2 * t.2.1.val + t.2.2.val, by
    have := t.1.isLt; have := t.2.1.isLt; have := t.2.2.isLt; omega⟩
  invFun w := (⟨w.val / 4, by have := w.isLt; omega⟩,
               ⟨(w.val % 4) / 2, by omega⟩, ⟨w.val % 2, by omega⟩)
  left_inv := by
    rintro ⟨⟨o, ho⟩, ⟨i, hi⟩, ⟨s, hs⟩⟩
    ext <;> simp <;> omega
  right_inv := by
    rintro ⟨w, hw⟩
    ext; simp; omega

@[simp] theorem wEquiv_div (o : Fin 3) (i s : Fin 2) :
    (wEquiv (o, i, s)).val / 4 = o.val := by
  have := i.isLt; have := s.isLt
  show (4 * o.val + 2 * i.val + s.val) / 4 = o.val
  omega

@[simp] theorem wEquiv_mid (o : Fin 3) (i s : Fin 2) :
    ((wEquiv (o, i, s)).val % 4) / 2 = i.val := by
  have := i.isLt; have := s.isLt
  show (4 * o.val + 2 * i.val + s.val) % 4 / 2 = i.val
  omega

@[simp] theorem wEquiv_parity (o : Fin 3) (i s : Fin 2) :
    (wEquiv (o, i, s)).val % 2 = s.val := by
  have := s.isLt
  show (4 * o.val + 2 * i.val + s.val) % 2 = s.val
  omega

theorem sum_fin12_split (F : Fin 12 → ℝ) :
    ∑ w : Fin 12, F w =
      ∑ o : Fin 3, ∑ i : Fin 2, ∑ s : Fin 2, F (wEquiv (o, i, s)) := by
  rw [← Equiv.sum_comp wEquiv F]
  simp only [Fintype.sum_prod_type]

theorem seedEncoding_col' (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (m : Fin 13) (o : Fin 3) (i s : Fin 2) :
    seedEncoding D (colEquiv (m, wEquiv (o, i, s))) =
      (if s.val = 0 then (blockValue D m.val i.val o).re
       else (blockValue D m.val i.val o).im) / seedFrameNorm m.val i.val := by
  rw [seedEncoding_col D m (wEquiv (o, i, s)) o (by simp)]
  simp

/-- **The single-recipient column identity.**  Pairing one recipient block of a
constraint row against the seed encoding reproduces the real (or imaginary)
part of that term of the triad bracket. -/
theorem recipient_column_sum (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (k x W : IVec) (hk : k ∈ seed)
    (hx : SeedCertificate.dot k x = 0) (b : Bool) :
    ∑ j : Fin 156,
        (if (j.val % 2 = 1) = (b = true) then
          ((recipientCoefficientZ k x W (j.val / 12) ((j.val % 12) / 4)
              (((j.val % 12) % 4) / 2) (j.val % 2) : Int) : ℝ)
         else 0) * seedEncoding D j
      = if b then
          (Vec3.dot (D (latticeOfIVec k) (realToComplexVec (realOfIVec x)))
            (realToComplexVec (realOfIVec W))).im
        else
          (Vec3.dot (D (latticeOfIVec k) (realToComplexVec (realOfIVec x)))
            (realToComplexVec (realOfIVec W))).re := by
  have hm := seed_modeIndex_lt k hk
  rw [sum_fin156_split, Finset.sum_eq_single (⟨modeIndex k, hm⟩ : Fin 13) ?hzero ?hmem]
  case hmem => intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  case hzero =>
    intro m' _ hne
    apply Finset.sum_eq_zero
    intro w _
    have hmm : ¬ (modeIndex k = m'.val) := fun hc => hne (Fin.ext hc.symm)
    simp only [colEquiv_mode, recipientCoefficientZ, if_neg hmm]
    simp
  rw [sum_fin12_split]
  simp only [colEquiv_mode, colEquiv_within, colEquiv_parity,
    wEquiv_div, wEquiv_mid, wEquiv_parity]
  rw [dot_realToComplexVec_re, dot_realToComplexVec_im]
  simp only [recipientCoefficientZ_at k x W hk]
  simp only [seedEncoding_col' D ⟨modeIndex k, hm⟩]
  cases b
  · -- real part
    simp only [Fin.sum_univ_three, Fin.sum_univ_two]
    rw [value_re D hreal k hk x hx 0, value_re D hreal k hk x hx 1,
        value_re D hreal k hk x hx 2]
    unfold frameCoord
    norm_num [componentZ_zero, componentZ_one, componentZ_two]
    ring
  · -- imaginary part
    simp only [if_true, Fin.sum_univ_three, Fin.sum_univ_two]
    rw [value_im D hreal k hk x hx 0, value_im D hreal k hk x hx 1,
        value_im D hreal k hk x hx 2]
    unfold frameCoord
    norm_num [componentZ_zero, componentZ_one, componentZ_two]
    ring

/-! ## Stage 8: `IVec`-level hypotheses transported to lattice hypotheses -/

theorem latticeOfIVec_ne_zero {k : IVec} (hk : k ≠ zero) : latticeOfIVec k ≠ 0 := by
  intro h
  apply hk
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [latticeOfIVec, latticeVec] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem latticeOfIVec_add_eq_zero {p q r : IVec} (h : add (add p q) r = zero) :
    latticeOfIVec p + latticeOfIVec q + latticeOfIVec r = 0 := by
  have h0 := congrArg Prod.fst h
  have h1 := congrArg (fun t => t.2.1) h
  have h2 := congrArg (fun t => t.2.2) h
  simp [add, zero] at h0 h1 h2
  funext i
  fin_cases i <;> simp [latticeOfIVec, latticeVec] <;> omega

theorem cross_realOfIVec (a b : IVec) :
    Vec3.cross (realOfIVec a) (realOfIVec b) =
      realOfIVec (SeedCertificate.cross a b) := by
  funext i
  fin_cases i <;> simp [Vec3.cross, realOfIVec, SeedCertificate.cross]

theorem noncollinear_of_cross_ne_zero {q r : IVec} (h : cross q r ≠ zero) :
    LatticeNonCollinear (latticeOfIVec q) (latticeOfIVec r) := by
  unfold LatticeNonCollinear
  rw [latticeToReal_latticeOfIVec, latticeToReal_latticeOfIVec, cross_realOfIVec]
  intro hc
  apply h
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [realOfIVec] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-! ## Stage 9: a whole constraint row annihilates the seed encoding -/

theorem mod12_mod2 (n : Nat) : n % 12 % 2 = n % 2 :=
  Nat.mod_mod_of_dvd n (by norm_num)

/-- **The seed bridge, one row at a time.**  Every constraint row of the
unit-cube matrix is a genuine consequence of the triad identity: pairing it
against the seed encoding of a symbol with active triad cancellation gives
zero. -/
theorem constraintRowZ_annihilates (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (htriad : HasActiveTriadCancellation D)
    (p q r a u v : IVec)
    (hp : p ∈ seed) (hq : q ∈ seed) (hr : r ∈ seed)
    (hpz : p ≠ zero) (hqz : q ≠ zero) (hrz : r ≠ zero)
    (hsum : add (add p q) r = zero) (hnc : cross q r ≠ zero)
    (hpa : SeedCertificate.dot p a = 0)
    (hqu : SeedCertificate.dot q u = 0)
    (hrv : SeedCertificate.dot r v = 0) (b : Bool) :
    ∑ j : Fin 156,
        ((constraintRowZ p q r a u v b).getD j.val 0 : ℝ) * seedEncoding D j = 0 := by
  have hbr := htriad (latticeOfIVec p) (latticeOfIVec q) (latticeOfIVec r)
      (realToComplexVec (realOfIVec a)) (realToComplexVec (realOfIVec u))
      (realToComplexVec (realOfIVec v))
      (latticeOfIVec_add_eq_zero hsum)
      (latticeOfIVec_ne_zero hpz) (latticeOfIVec_ne_zero hqz) (latticeOfIVec_ne_zero hrz)
      (noncollinear_of_cross_ne_zero hnc)
      (transverse_of_dot_zero p a hpa) (transverse_of_dot_zero q u hqu)
      (transverse_of_dot_zero r v hrv)
  have hrow : ∀ j : Fin 156,
      ((constraintRowZ p q r a u v b).getD j.val 0 : ℝ) * seedEncoding D j =
        (if (j.val % 2 = 1) = (b = true) then
            ((recipientCoefficientZ p a (rawZ q r u v) (j.val / 12) ((j.val % 12) / 4)
                (((j.val % 12) % 4) / 2) (j.val % 2) : Int) : ℝ) else 0) * seedEncoding D j +
        (if (j.val % 2 = 1) = (b = true) then
            ((recipientCoefficientZ q u (rawZ r p v a) (j.val / 12) ((j.val % 12) / 4)
                (((j.val % 12) % 4) / 2) (j.val % 2) : Int) : ℝ) else 0) * seedEncoding D j +
        (if (j.val % 2 = 1) = (b = true) then
            ((recipientCoefficientZ r v (rawZ p q a u) (j.val / 12) ((j.val % 12) / 4)
                (((j.val % 12) % 4) / 2) (j.val % 2) : Int) : ℝ) else 0) * seedEncoding D j := by
    intro j
    rw [constraintRowZ_entry]
    unfold bracketCoefficientZ
    simp only [mod12_mod2]
    by_cases hc : (j.val % 2 = 1) = (b = true)
    · simp only [if_pos hc]
      push_cast
      ring
    · simp only [if_neg hc]
      ring
  simp only [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    recipient_column_sum D hreal p a (rawZ q r u v) hp hpa b,
    recipient_column_sum D hreal q u (rawZ r p v a) hq hqu b,
    recipient_column_sum D hreal r v (rawZ p q a u) hr hrv b]
  unfold triadBracket at hbr
  rw [rawRecipient_of_rawZ, rawRecipient_of_rawZ, rawRecipient_of_rawZ] at hbr
  cases b
  · have hre := congrArg Complex.re hbr
    simpa using hre
  · have him := congrArg Complex.im hbr
    simpa using him

/-! ## Stage 10: every row of the seed matrix annihilates the encoding -/

theorem triads_facts : ∀ t ∈ triads,
    t.1 ∈ seed ∧ t.2.1 ∈ seed ∧ t.2.2 ∈ seed ∧
    t.1 ≠ zero ∧ t.2.1 ≠ zero ∧ t.2.2 ≠ zero ∧
    add (add t.1 t.2.1) t.2.2 = zero ∧ cross t.2.1 t.2.2 ≠ zero := by decide

theorem triad_polarization_facts : ∀ t ∈ triads,
    ∀ x ∈ polarizationTriples t.1 t.2.1 t.2.2,
      SeedCertificate.dot t.1 x.1 = 0 ∧ SeedCertificate.dot t.2.1 x.2.1 = 0 ∧
      SeedCertificate.dot t.2.2 x.2.2 = 0 := by decide

theorem rowsZ_annihilates (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (htriad : HasActiveTriadCancellation D)
    (row : ZRow) (hrow : row ∈ rowsZ) :
    ∑ j : Fin 156, ((row.getD j.val 0 : ℝ)) * seedEncoding D j = 0 := by
  unfold rowsZ at hrow
  rw [List.mem_flatMap] at hrow
  obtain ⟨t, ht, hrow⟩ := hrow
  rw [List.mem_flatMap] at hrow
  obtain ⟨x, hx, hrow⟩ := hrow
  obtain ⟨hs1, hs2, hs3, hz1, hz2, hz3, hsum, hnc⟩ := triads_facts t ht
  obtain ⟨hd1, hd2, hd3⟩ := triad_polarization_facts t ht x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with h | h <;> subst h <;>
    exact constraintRowZ_annihilates D hreal htriad _ _ _ _ _ _
      hs1 hs2 hs3 hz1 hz2 hz3 hsum hnc hd1 hd2 hd3 _

theorem rowsZ_getD_annihilates (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (htriad : HasActiveTriadCancellation D)
    (n : Nat) :
    ∑ j : Fin 156, ((rowsZ.getD n #[]).getD j.val 0 : ℝ) * seedEncoding D j = 0 := by
  by_cases h : n < rowsZ.length
  · have hmem : rowsZ.getD n #[] ∈ rowsZ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      exact List.getElem_mem h
    exact rowsZ_annihilates D hreal htriad _ hmem
  · have hnil : rowsZ.getD n #[] = #[] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hnil]
    simp

/-- **The semantic seed bridge.**  A reality-compatible symbol family with
active triad cancellation satisfies every selected constraint of the
thirteen-mode unit-cube matrix.  This is what ties the kernel-checked rank
computation to the actual Euler triad identity. -/
theorem seedConstraints_of_triadCancellation (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (htriad : HasActiveTriadCancellation D) :
    selectedSeedConstraints (seedEncoding D) = 0 := by
  funext i
  simp only [selectedSeedConstraints, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Pi.zero_apply, selectedSeedMatrix]
  exact rowsZ_getD_annihilates D hreal htriad _

end FourierMultiplierRigidity
