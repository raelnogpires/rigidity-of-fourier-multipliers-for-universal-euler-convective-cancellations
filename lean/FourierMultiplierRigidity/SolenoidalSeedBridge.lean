import FourierMultiplierRigidity.SolenoidalSeedCertificate
import FourierMultiplierRigidity.SeedCertificate
import FourierMultiplierRigidity.SolenoidalPropagation
import FourierMultiplierRigidity.SeedBridge

/-!
# Physical provenance of the Hermitian Boolean-seed rows (data layer)

`SolenoidalSeedCertificate.lean` presents a `26 × 28` integer matrix and
certifies its rank and nullity.  Until now the statement that those rows *are*
the constraints imposed by the Euler triad identity on explicit test fields
rested on an external program, `verify_solenoidal_seed_semantics.py`, which
reconstructs the rows in Python and compares them with the Lean source text.

This module internalizes the data half of that bridge.  For each row it records
the triad, the three integer polarizations and the three phases that produce
it, recomputes the row inside Lean from that data, and checks the result
against `booleanSeedMatrixZ` — kernel-checked by `decide`, with no appeal to
the Python source parser.

The test field attached to a triad `(p, q, r)` with `p + q + r = 0`,
polarizations `a ⊥ p`, `u ⊥ q`, `v ⊥ r` and phases in `{1, i}` has Fourier
amplitudes `phase • polarization` at `p, q, r` and their conjugates at the
negatives.  Its Euler cubic form is a real linear functional of the Hermitian
seed parameters; `numeratorEntry` computes that functional's coefficients,
cleared of the frame denominators carried by `denomAt`.

What remains for the semantic half (a later stage) is the identity
`⟨row, encoding D⟩ = triadBracket D …`, which turns these coefficients into a
statement about symbols rather than about integers.
-/

namespace FourierMultiplierRigidity.SolenoidalSeedBridge

open FourierMultiplierRigidity.SeedCertificate
open FourierMultiplierRigidity.SolenoidalSeedCertificate

/-! ## Gaussian integer arithmetic -/

/-- A Gaussian integer as a real/imaginary pair. -/
abbrev GZ := Int × Int

def gadd (x y : GZ) : GZ := (x.1 + y.1, x.2 + y.2)
def gsub (x y : GZ) : GZ := (x.1 - y.1, x.2 - y.2)
def gmul (x y : GZ) : GZ := (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def gneg (x : GZ) : GZ := (-x.1, -x.2)
def gconj (x : GZ) : GZ := (x.1, -x.2)
def gI : GZ := (0, 1)
def gOf (n : Int) : GZ := (n, 0)

/-- A vector of Gaussian integers. -/
abbrev GVec := GZ × GZ × GZ

def gOfIVec (k : IVec) : GVec := (gOf k.1, gOf k.2.1, gOf k.2.2)
def gconjVec (w : GVec) : GVec := (gconj w.1, gconj w.2.1, gconj w.2.2)
def gsmulVec (c : GZ) (w : GVec) : GVec := (gmul c w.1, gmul c w.2.1, gmul c w.2.2)

/-- Pairing of a Gaussian vector with an integer vector. -/
def gdotI (w : GVec) (k : IVec) : GZ :=
  gadd (gmul w.1 (gOf k.1)) (gadd (gmul w.2.1 (gOf k.2.1)) (gmul w.2.2 (gOf k.2.2)))

/-! ## Triad data -/

/-- A triad, three transverse integer polarizations, and three phases in
`{1, i}` (`false` is `1`, `true` is `i`). -/
structure TriadDatum where
  p : IVec
  q : IVec
  r : IVec
  a : IVec
  u : IVec
  v : IVec
  php : Bool
  phq : Bool
  phr : Bool
deriving DecidableEq, Inhabited

/-- The seven unoriented Boolean seed modes, in the column order of
`booleanSeedMatrixZ`. -/
def booleanReps : List IVec :=
  [(0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]

def phaseOf (b : Bool) : GZ := if b then gI else gOf 1

/-- The six signed Fourier amplitudes of the triad-supported test field. -/
def modesOf (t : TriadDatum) : List (IVec × GVec) :=
  let ap := gsmulVec (phaseOf t.php) (gOfIVec t.a)
  let aq := gsmulVec (phaseOf t.phq) (gOfIVec t.u)
  let ar := gsmulVec (phaseOf t.phr) (gOfIVec t.v)
  [(t.p, ap), (neg t.p, gconjVec ap),
   (t.q, aq), (neg t.q, gconjVec aq),
   (t.r, ar), (neg t.r, gconjVec ar)]

/-- Index of the Hermitian parameter block of a signed mode. -/
def blockIndex (k : IVec) : Nat := booleanReps.idxOf (representative k)

/-- The resonant ordered triples of signed modes of a test field. -/
def resonantTriples (ms : List (IVec × GVec)) :
    List ((IVec × GVec) × (IVec × GVec) × (IVec × GVec)) :=
  ms.flatMap fun P => ms.flatMap fun Q => ms.filterMap fun R =>
    if add (add P.1 Q.1) R.1 = zero then some (P, Q, R) else none

/-- The contribution of one resonant triple to one column, with the frame
denominators of `denomAt` cleared. -/
def tripleEntry (P Q R : IVec × GVec) (j : Nat) : GZ :=
  if j / 4 ≠ blockIndex P.1 then (0, 0) else
    let rep := representative P.1
    let f0 := (frame rep).getD 0 zero
    let f1 := (frame rep).getD 1 zero
    let x1 := gdotI P.2 f0
    let x2 := gdotI P.2 f1
    let deriv := gmul gI (gdotI Q.2 R.1)
    let nonlinear := gsmulVec deriv R.2
    let y1 := gdotI nonlinear f0
    let y2 := gdotI nonlinear f1
    match j % 4 with
    | 0 => gmul y1 x1
    | 1 => gmul y2 x2
    | 2 => gadd (gmul y1 x2) (gmul y2 x1)
    | _ =>
      let skew := gmul gI (gsub (gmul y1 x2) (gmul y2 x1))
      if P.1 = rep then skew else gneg skew

/-- The numerator of one column of the constraint row of a test field. -/
def numeratorEntry (t : TriadDatum) (j : Nat) : GZ :=
  ((resonantTriples (modesOf t)).map (fun x => tripleEntry x.1 x.2.1 x.2.2 j)).sum

/-- The frame denominator carried by one column. -/
def denomAt (j : Nat) : Int :=
  let rep := booleanReps.getD (j / 4) zero
  let f0 := (frame rep).getD 0 zero
  let f1 := (frame rep).getD 1 zero
  let n0 := dot f0 f0
  let n1 := dot f1 f1
  match j % 4 with
  | 0 => n0 * n0
  | 1 => n1 * n1
  | _ => n0 * n1

def booleanProvenance : List TriadDatum := [
  ⟨(-1, -1, -1), (0, 0, 1), (1, 1, 0), (0, -1, 1), (0, 1, 0), (0, 0, -1), false, false, false⟩,
  ⟨(-1, -1, -1), (0, 0, 1), (1, 1, 0), (0, -1, 1), (0, 1, 0), (0, 0, -1), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 0, 1), (1, 1, 0), (0, -1, 1), (0, 1, 0), (1, -1, 0), false, false, false⟩,
  ⟨(-1, -1, -1), (0, 0, 1), (1, 1, 0), (0, -1, 1), (0, 1, 0), (1, -1, 0), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 0, 1), (1, 1, 0), (0, -1, 1), (-1, 0, 0), (0, 0, -1), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 0, 1), (1, 1, 0), (0, -1, 1), (-1, 0, 0), (1, -1, 0), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 0, 1), (1, 1, 0), (1, 0, -1), (0, 1, 0), (0, 0, -1), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 0), (1, 0, 1), (0, -1, 1), (0, 0, -1), (0, 1, 0), false, false, false⟩,
  ⟨(-1, -1, -1), (0, 1, 0), (1, 0, 1), (0, -1, 1), (0, 0, -1), (0, 1, 0), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 0), (1, 0, 1), (0, -1, 1), (0, 0, -1), (-1, 0, 1), false, false, false⟩,
  ⟨(-1, -1, -1), (0, 1, 0), (1, 0, 1), (0, -1, 1), (0, 0, -1), (-1, 0, 1), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 0), (1, 0, 1), (0, -1, 1), (1, 0, 0), (0, 1, 0), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 0), (1, 0, 1), (0, -1, 1), (1, 0, 0), (-1, 0, 1), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 0), (1, 0, 1), (1, 0, -1), (0, 0, -1), (0, 1, 0), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 1), (1, 0, 0), (0, -1, 1), (0, 1, -1), (0, 0, 1), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 1), (1, 0, 0), (0, -1, 1), (-1, 0, 0), (0, 0, 1), false, false, false⟩,
  ⟨(-1, -1, -1), (0, 1, 1), (1, 0, 0), (0, -1, 1), (-1, 0, 0), (0, 0, 1), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 1), (1, 0, 0), (0, -1, 1), (-1, 0, 0), (0, -1, 0), false, false, true⟩,
  ⟨(-1, -1, -1), (0, 1, 1), (1, 0, 0), (1, 0, -1), (0, 1, -1), (0, 0, 1), false, false, false⟩,
  ⟨(-1, -1, -1), (0, 1, 1), (1, 0, 0), (1, 0, -1), (-1, 0, 0), (0, 0, 1), false, false, true⟩,
  ⟨(-1, -1, 0), (0, 1, 0), (1, 0, 0), (0, 0, 1), (0, 0, -1), (0, -1, 0), false, false, true⟩,
  ⟨(-1, -1, 0), (0, 1, 0), (1, 0, 0), (0, 0, 1), (1, 0, 0), (0, 0, 1), false, false, true⟩,
  ⟨(-1, -1, 0), (0, 1, 0), (1, 0, 0), (0, 0, 1), (1, 0, 0), (0, -1, 0), false, false, true⟩,
  ⟨(-1, -1, 0), (0, 1, 0), (1, 0, 0), (-1, 1, 0), (0, 0, -1), (0, -1, 0), false, false, true⟩,
  ⟨(-1, -1, 0), (0, 1, 0), (1, 0, 0), (-1, 1, 0), (1, 0, 0), (0, -1, 0), false, false, true⟩,
  ⟨(-1, 0, -1), (0, 0, 1), (1, 0, 0), (0, -1, 0), (0, 1, 0), (0, 0, 1), false, false, true⟩
]

def booleanScales : List Int :=
  [3, 3, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 3, 3, 3, 1, 6, 1, 1, 1, 1, 1, 1]

/-! ## The rows of the certificate are the rows of these test fields -/

/-- One column of one row agrees with the recomputed test-field coefficient,
after clearing the frame denominator by the recorded integer scale. -/
def columnMatches (i j : Nat) : Bool :=
  let t := booleanProvenance.getD i default
  let num := numeratorEntry t j
  let lhs := (booleanScales.getD i 1) * num.1
  let rhs := ((booleanSeedMatrixZ.getD i #[]).getD j 0) * denomAt j
  num.2 == 0 && lhs == rhs

def rowMatches (i : Nat) : Bool := (List.range 28).all (columnMatches i)

def allRowsMatch : Bool := (List.range 26).all rowMatches

/-- **The certificate rows are physical.**  Every row of the `26 × 28`
Hermitian Boolean-seed matrix is the Euler constraint row of the explicit
triad-supported test field recorded in `booleanProvenance`, up to the recorded
integer scale and the frame denominators.  The imaginary part of every
recomputed coefficient vanishes, as it must for a real constraint.

This is discharged by `decide`, so it is kernel-checked: it replaces the
external Python reconstruction for the matrix data. -/
theorem booleanSeedMatrix_rows_are_physical : allRowsMatch = true := by decide

theorem rowMatches_of_lt {i : Nat} (hi : i < 26) : rowMatches i = true :=
  List.all_eq_true.mp booleanSeedMatrix_rows_are_physical i (List.mem_range.mpr hi)

theorem columnMatches_of_lt {i j : Nat} (hi : i < 26) (hj : j < 28) :
    columnMatches i j = true :=
  List.all_eq_true.mp (rowMatches_of_lt hi) j (List.mem_range.mpr hj)

/-- Entrywise form, stated for the typed matrix actually used by the rank and
nullity certificates: every entry is the corresponding test-field coefficient,
and every recomputed coefficient is real. -/
theorem booleanSeedMatrixTypedZ_physical (i : Fin 26) (j : Fin 28) :
    (numeratorEntry (booleanProvenance.getD i.val default) j.val).2 = 0 ∧
      (booleanScales.getD i.val 1) *
          (numeratorEntry (booleanProvenance.getD i.val default) j.val).1 =
        booleanSeedMatrixTypedZ i j * denomAt j.val := by
  have h := columnMatches_of_lt i.isLt j.isLt
  unfold columnMatches at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

/-! ## The Hermitian parameters of a symbol

`booleanEncoding D` is the real `28`-vector the certificate rows are paired
against: for each Boolean representative `m` with seed frame `f₀, f₁`, the four
numbers `⟨D(m)f₀,f₀⟩`, `⟨D(m)f₁,f₁⟩`, `Re⟨D(m)f₁,f₀⟩`, `Im⟨D(m)f₁,f₀⟩`.  The
pairing is the complex bilinear `Vec3.dot`, unnormalized; the frame norms are
carried by `denomAt` instead. -/

/-- Index of a Boolean representative among the thirteen unit-cube modes. -/
def boolModeNat (t : Nat) : Nat := SeedCertificate.modeIndex (booleanReps.getD t zero)

theorem boolModeNat_lt (t : Fin 7) : boolModeNat t.val < 13 := by
  fin_cases t <;> decide

/-- The Boolean representative as a seed mode index. -/
def boolMode (t : Fin 7) : Fin 13 := ⟨boolModeNat t.val, boolModeNat_lt t⟩

/-- The Hermitian parameter `α i k = ⟨D(m) f_k, f_i⟩` at a Boolean mode. -/
noncomputable def boolAlpha (D : LatticeVec → CVec →ₗ[ℂ] CVec) (t : Fin 7)
    (i k : Nat) : ℂ :=
  Vec3.dot (D (seedMode (boolMode t)) (seedFrameComplex (boolMode t) k))
    (seedFrameComplex (boolMode t) i)

/-- The four real parameters of one Hermitian block. -/
noncomputable def boolEntry (D : LatticeVec → CVec →ₗ[ℂ] CVec) (t : Fin 7)
    (u : Nat) : ℝ :=
  match u with
  | 0 => (boolAlpha D t 0 0).re
  | 1 => (boolAlpha D t 1 1).re
  | 2 => (boolAlpha D t 0 1).re
  | _ => (boolAlpha D t 0 1).im

/-- The twenty-eight real Hermitian seed parameters of a symbol. -/
noncomputable def booleanEncoding (D : LatticeVec → CVec →ₗ[ℂ] CVec) (j : Fin 28) : ℝ :=
  boolEntry D ⟨j.val / 4, by have := j.isLt; omega⟩ (j.val % 4)

/-! ## The recipient block identity -/

/-- Pairing a transverse vector against anything is determined by its two frame
coordinates. -/
theorem dot_frame_expansion (m : Fin 13) (z y : CVec)
    (hz : Transverse (seedMode m) z) :
    Vec3.dot z y =
      (Vec3.dot z (seedFrameComplex m 0) / seedFrameNorm m 0) *
          Vec3.dot (seedFrameComplex m 0) y +
        (Vec3.dot z (seedFrameComplex m 1) / seedFrameNorm m 1) *
          Vec3.dot (seedFrameComplex m 1) y := by
  conv_lhs => rw [seed_frame_decomposition m z hz]
  simp [Vec3.dot_smul_left]

/-- **The recipient block identity.**  For a symbol with solenoidal output the
pairing `⟨D(m)x, y⟩` is the Hermitian parameter matrix at `m` contracted with
the frame coordinates of `x` and of `y`.  This is the step that turns a row of
integers into a statement about a symbol. -/
theorem dot_symbol_expansion (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hsol : HasSolenoidalOutputMap D) (t : Fin 7) (x y : CVec)
    (hmode : seedMode (boolMode t) ≠ 0)
    (hx : Transverse (seedMode (boolMode t)) x) :
    Vec3.dot (D (seedMode (boolMode t)) x) y =
      boolAlpha D t 0 0 *
          (Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
          (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0) +
        boolAlpha D t 0 1 *
          (Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
          (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0) +
        boolAlpha D t 1 0 *
          (Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
          (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1) +
        boolAlpha D t 1 1 *
          (Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
          (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1) := by
  classical
  set m := boolMode t
  have hf0 : Transverse (seedMode m) (seedFrameComplex m 0) :=
    transverse_complexification (transverseR_seedFrame m.val 0 m.isLt (by norm_num))
  have hf1 : Transverse (seedMode m) (seedFrameComplex m 1) :=
    transverse_complexification (transverseR_seedFrame m.val 1 m.isLt (by norm_num))
  -- expand the input in the frame, then push `D` through
  have hxexp := seed_frame_decomposition m x hx
  have hDx : D (seedMode m) x =
      (Vec3.dot x (seedFrameComplex m 0) / seedFrameNorm m 0) •
          D (seedMode m) (seedFrameComplex m 0) +
        (Vec3.dot x (seedFrameComplex m 1) / seedFrameNorm m 1) •
          D (seedMode m) (seedFrameComplex m 1) := by
    conv_lhs => rw [hxexp]
    simp
  -- each image is transverse, so expand it in the frame as well
  have h0 := dot_frame_expansion m (D (seedMode m) (seedFrameComplex m 0)) y
    (hsol _ hmode _ hf0)
  have h1 := dot_frame_expansion m (D (seedMode m) (seedFrameComplex m 1)) y
    (hsol _ hmode _ hf1)
  rw [hDx]
  simp only [Vec3.dot_add_left, Vec3.dot_smul_left, h0, h1, boolAlpha]
  ring

/-! ## Hermitian symmetry

The Boolean seed certifies a *Hermitian* reality-compatible solenoidal
multiplier, but the development so far never named that class.  The relevant
statement, in the real frame pairing the rows use, is that the fiber map is
self-adjoint: `⟨D(k)x, y⟩ = conj ⟨D(k)y, x⟩` on real transverse inputs.  This
is exactly what makes the `2 × 2` parameter matrix `α` Hermitian, hence
describable by the four real numbers of `booleanEncoding`. -/

/-- Self-adjointness of a symbol on its transverse fiber. -/
def HasHermitianFiber (D : LatticeVec → CVec →ₗ[ℂ] CVec) : Prop :=
  ∀ (k : LatticeVec), k ≠ 0 → ∀ (x y : RVec), TransverseR k x → TransverseR k y →
    Vec3.dot (D k (realToComplexVec x)) (realToComplexVec y) =
      (starRingEnd ℂ) (Vec3.dot (D k (realToComplexVec y)) (realToComplexVec x))

theorem latticeOfIVec_ne_zero {x : IVec} (h : x ≠ zero) : latticeOfIVec x ≠ 0 := by
  intro hz
  apply h
  obtain ⟨a, b, c⟩ := x
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  have h2 := congrFun hz 2
  simp [latticeOfIVec, latticeVec] at h0 h1 h2
  simp [zero, h0, h1, h2]

theorem boolMode_ne_zero (t : Fin 7) : seedMode (boolMode t) ≠ 0 :=
  latticeOfIVec_ne_zero (by fin_cases t <;> decide)

/-- The parameter matrix at a Boolean mode is Hermitian. -/
theorem boolAlpha_conj (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hherm : HasHermitianFiber D) (t : Fin 7) (i k : Nat) (hi : i < 2)
    (hk : k < 2) :
    boolAlpha D t i k = (starRingEnd ℂ) (boolAlpha D t k i) := by
  unfold boolAlpha seedFrameComplex
  exact hherm _ (boolMode_ne_zero t) _ _
    (transverseR_seedFrame _ k (boolMode t).isLt hk)
    (transverseR_seedFrame _ i (boolMode t).isLt hi)

/-- The diagonal parameters are real. -/
theorem boolAlpha_diag_re (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hherm : HasHermitianFiber D) (t : Fin 7) (i : Nat) (hi : i < 2) :
    boolAlpha D t i i = ((boolAlpha D t i i).re : ℂ) := by
  have h := boolAlpha_conj D hherm t i i hi hi
  exact (Complex.conj_eq_iff_re.mp h.symm).symm

/-- The Hermitian recombination of a `2 × 2` block into four real parameters. -/
private theorem hermitian_combine (a00 a11 a01 X0 X1 Y0 Y1 : ℂ)
    (h00 : a00 = ((a00.re : ℝ) : ℂ)) (h11 : a11 = ((a11.re : ℝ) : ℂ)) :
    a00 * X0 * Y0 + a01 * X1 * Y0 + (starRingEnd ℂ) a01 * X0 * Y1 + a11 * X1 * Y1 =
      (a00.re : ℂ) * (X0 * Y0) + (a11.re : ℂ) * (X1 * Y1) +
        (a01.re : ℂ) * (X1 * Y0 + X0 * Y1) +
        Complex.I * (a01.im : ℂ) * (X1 * Y0 - X0 * Y1) := by
  have hA : a01 = (a01.re : ℂ) + Complex.I * (a01.im : ℂ) := by
    apply Complex.ext <;> simp
  have hB : (starRingEnd ℂ) a01 = (a01.re : ℂ) - Complex.I * (a01.im : ℂ) := by
    apply Complex.ext <;> simp
  linear_combination (X0 * Y0) * h00 + (X1 * Y1) * h11 + (X1 * Y0) * hA + (X0 * Y1) * hB

/-- **The Hermitian block identity.**  For a Hermitian solenoidal symbol the
pairing `⟨D(m)x, y⟩` is built from the four *real* parameters of
`booleanEncoding`, in exactly the combination the certificate rows use. -/
theorem dot_symbol_hermitian (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hsol : HasSolenoidalOutputMap D) (hherm : HasHermitianFiber D) (t : Fin 7)
    (x y : CVec) (hx : Transverse (seedMode (boolMode t)) x) :
    Vec3.dot (D (seedMode (boolMode t)) x) y =
      (boolAlpha D t 0 0).re *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
            (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0)) +
        (boolAlpha D t 1 1).re *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
            (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1)) +
        (boolAlpha D t 0 1).re *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
              (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0) +
            (Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
              (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1)) +
        Complex.I * (boolAlpha D t 0 1).im *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
              (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0) -
            (Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
              (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1)) := by
  have hexp := dot_symbol_expansion D hsol t x y (boolMode_ne_zero t) hx
  have h10 : boolAlpha D t 1 0 = (starRingEnd ℂ) (boolAlpha D t 0 1) :=
    boolAlpha_conj D hherm t 1 0 (by norm_num) (by norm_num)
  rw [hexp, h10]
  exact hermitian_combine _ _ _ _ _ _ _
    (boolAlpha_diag_re D hherm t 0 (by norm_num))
    (boolAlpha_diag_re D hherm t 1 (by norm_num))

/-! ## Reality transport to the negative mode

A row's block belongs to the *representative* mode, so a triple whose first
member is the negative of its representative must be expressed through the same
four parameters.  Reality compatibility does that, and flips the sign of the
`Im α₀₁` column — which is precisely the orientation sign carried by
`tripleEntry`. -/

theorem dot_conjVec (u v : CVec) :
    Vec3.dot (conjVec u) v = (starRingEnd ℂ) (Vec3.dot u (conjVec v)) := by
  simp [Vec3.dot, conjVec]

theorem transverse_conjVec {k : LatticeVec} {v : CVec} (h : Transverse k v) :
    Transverse k (conjVec v) := by
  have := congrArg (starRingEnd ℂ) h
  simpa [Transverse, Vec3.dot, conjVec, latticeToComplex] using this

/-- **The block identity at a negated mode.**  The same four real parameters
describe the block at `-m`, with the imaginary column negated. -/
theorem dot_symbol_hermitian_neg (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hsol : HasSolenoidalOutputMap D) (hherm : HasHermitianFiber D)
    (hreal : RealityCompatibleMap D) (t : Fin 7) (x y : CVec)
    (hx : Transverse (seedMode (boolMode t)) x) :
    Vec3.dot (D (-(seedMode (boolMode t))) x) y =
      (boolAlpha D t 0 0).re *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
            (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0)) +
        (boolAlpha D t 1 1).re *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
            (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1)) +
        (boolAlpha D t 0 1).re *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
              (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0) +
            (Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
              (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1)) -
        Complex.I * (boolAlpha D t 0 1).im *
          ((Vec3.dot x (seedFrameComplex (boolMode t) 1) / seedFrameNorm (boolMode t) 1) *
              (Vec3.dot (seedFrameComplex (boolMode t) 0) y / seedFrameNorm (boolMode t) 0) -
            (Vec3.dot x (seedFrameComplex (boolMode t) 0) / seedFrameNorm (boolMode t) 0) *
              (Vec3.dot (seedFrameComplex (boolMode t) 1) y / seedFrameNorm (boolMode t) 1)) := by
  classical
  set m := seedMode (boolMode t) with hm
  -- transport the block at `-m` to the block at `m`
  have hxc : Transverse m (conjVec x) := transverse_conjVec hx
  have hstep : D (-m) x = conjVec (D m (conjVec x)) := by
    have h := hreal m (conjVec x) hxc
    simpa using h
  rw [hstep, dot_conjVec, dot_symbol_hermitian D hsol hherm t (conjVec x) (conjVec y) hxc]
  -- the frame vectors are real, so conjugation only conjugates the coordinates
  have hf0 : conjVec (seedFrameComplex (boolMode t) 0) = seedFrameComplex (boolMode t) 0 :=
    conjVec_realToComplexVec _
  have hf1 : conjVec (seedFrameComplex (boolMode t) 1) = seedFrameComplex (boolMode t) 1 :=
    conjVec_realToComplexVec _
  have hn0 : ((seedFrameNorm (boolMode t) 0 : ℝ) : ℂ) =
      (starRingEnd ℂ) ((seedFrameNorm (boolMode t) 0 : ℝ) : ℂ) := by simp
  have hn1 : ((seedFrameNorm (boolMode t) 1 : ℝ) : ℂ) =
      (starRingEnd ℂ) ((seedFrameNorm (boolMode t) 1 : ℝ) : ℂ) := by simp
  have e0 : Vec3.dot (conjVec x) (seedFrameComplex (boolMode t) 0) =
      (starRingEnd ℂ) (Vec3.dot x (seedFrameComplex (boolMode t) 0)) := by
    rw [dot_conjVec, hf0]
  have e1 : Vec3.dot (conjVec x) (seedFrameComplex (boolMode t) 1) =
      (starRingEnd ℂ) (Vec3.dot x (seedFrameComplex (boolMode t) 1)) := by
    rw [dot_conjVec, hf1]
  have g0 : Vec3.dot (seedFrameComplex (boolMode t) 0) (conjVec y) =
      (starRingEnd ℂ) (Vec3.dot (seedFrameComplex (boolMode t) 0) y) := by
    rw [Vec3.dot_comm, dot_conjVec, Vec3.dot_comm, hf0]
  have g1 : Vec3.dot (seedFrameComplex (boolMode t) 1) (conjVec y) =
      (starRingEnd ℂ) (Vec3.dot (seedFrameComplex (boolMode t) 1) y) := by
    rw [Vec3.dot_comm, dot_conjVec, Vec3.dot_comm, hf1]
  rw [e0, e1, g0, g1]
  simp only [map_add, map_sub, map_mul, map_div₀, Complex.conj_conj,
    Complex.conj_I, Complex.conj_ofReal]
  ring

/-! ## Column bookkeeping and complexification -/

def colEquiv28 : Fin 7 × Fin 4 ≃ Fin 28 where
  toFun p := ⟨4 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun j := (⟨j.val / 4, by have := j.isLt; omega⟩, ⟨j.val % 4, by omega⟩)
  left_inv := by rintro ⟨⟨m, hm⟩, ⟨w, hw⟩⟩; ext <;> simp <;> omega
  right_inv := by rintro ⟨j, hj⟩; ext; simp; omega

theorem sum_fin28_split (F : Fin 28 → ℂ) :
    ∑ j : Fin 28, F j = ∑ t : Fin 7, ∑ u : Fin 4, F (colEquiv28 (t, u)) := by
  rw [← Equiv.sum_comp colEquiv28 F, Fintype.sum_prod_type]

@[simp] theorem colEquiv28_block (t : Fin 7) (u : Fin 4) :
    (colEquiv28 (t, u)).val / 4 = t.val := by
  have hu := u.isLt
  show (4 * t.val + u.val) / 4 = t.val
  omega

@[simp] theorem colEquiv28_within (t : Fin 7) (u : Fin 4) :
    (colEquiv28 (t, u)).val % 4 = u.val := by
  have hu := u.isLt
  show (4 * t.val + u.val) % 4 = u.val
  omega

/-- A Gaussian integer as a complex number. -/
def cOfGZ (z : GZ) : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)

/-- A Gaussian vector as a complex vector. -/
def cOfGVec (w : GVec) : CVec := ![cOfGZ w.1, cOfGZ w.2.1, cOfGZ w.2.2]

/-- An integer vector as a complex vector. -/
def cOfIVec (k : IVec) : CVec := realToComplexVec (realOfIVec k)

@[simp] theorem cOfGZ_zero : cOfGZ 0 = 0 := by simp [cOfGZ]

@[simp] theorem cOfGZ_gOf (n : Int) : cOfGZ (gOf n) = (n : ℂ) := by
  simp [cOfGZ, gOf]

theorem cOfGZ_add (x y : GZ) : cOfGZ (gadd x y) = cOfGZ x + cOfGZ y := by
  simp [cOfGZ, gadd]
  ring

theorem cOfGZ_mul (x y : GZ) : cOfGZ (gmul x y) = cOfGZ x * cOfGZ y := by
  simp only [cOfGZ, gmul]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem cOfGZ_sub (x y : GZ) : cOfGZ (gsub x y) = cOfGZ x - cOfGZ y := by
  simp [cOfGZ, gsub]
  ring

theorem cOfGZ_neg (x : GZ) : cOfGZ (gneg x) = -cOfGZ x := by
  simp [cOfGZ, gneg]
  ring

@[simp] theorem cOfGZ_I : cOfGZ gI = Complex.I := by simp [cOfGZ, gI]

theorem cOfGZ_sum (l : List GZ) : cOfGZ l.sum = (l.map cOfGZ).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have hadd : (a + t.sum : GZ) = gadd a t.sum := rfl
    simp [hadd, cOfGZ_add, ih]

/-- The Gaussian pairing is the complex pairing after complexification. -/
theorem cOfGZ_gdotI (w : GVec) (k : IVec) :
    cOfGZ (gdotI w k) = Vec3.dot (cOfGVec w) (cOfIVec k) := by
  simp only [gdotI, cOfGZ_add, cOfGZ_mul, cOfGZ_gOf]
  simp [Vec3.dot, cOfGVec, cOfIVec, realToComplexVec, realOfIVec]
  ring

theorem cOfGVec_gsmulVec (c : GZ) (w : GVec) :
    cOfGVec (gsmulVec c w) = cOfGZ c • cOfGVec w := by
  funext i
  fin_cases i <;> simp [cOfGVec, gsmulVec, cOfGZ_mul]

/-! ## From a column sum to the symbol pairing -/

theorem seedModeIVec_boolMode (t : Fin 7) :
    seedModeIVec (boolMode t) = booleanReps.getD t.val zero := by
  fin_cases t <;> decide

theorem seedFrameIVec_boolMode (t : Fin 7) (i : Nat) :
    seedFrameIVec (boolMode t) i =
      (frame (booleanReps.getD t.val zero)).getD i zero := by
  rw [seedFrameIVec, seedModeIVec_boolMode]

theorem seedFrameComplex_boolMode (t : Fin 7) (i : Nat) :
    seedFrameComplex (boolMode t) i =
      cOfIVec ((frame (booleanReps.getD t.val zero)).getD i zero) := by
  rw [seedFrameComplex, seedFrameReal, seedFrameIVec_boolMode]
  rfl

theorem seedFrameNorm_boolMode (t : Fin 7) (i : Nat) :
    seedFrameNorm (boolMode t) i =
      ((dot ((frame (booleanReps.getD t.val zero)).getD i zero)
        ((frame (booleanReps.getD t.val zero)).getD i zero) : Int) : ℝ) := by
  rw [seedFrameNorm, seedFrameIVec_boolMode]

@[simp] theorem booleanEncoding_col (D : LatticeVec → CVec →ₗ[ℂ] CVec) (t : Fin 7)
    (u : Fin 4) : booleanEncoding D (colEquiv28 (t, u)) = boolEntry D t u.val := by
  unfold booleanEncoding
  congr 1
  · exact Fin.ext (by simp)
  · simp

theorem tripleEntry_off_block (P Q R : IVec × GVec) (j : Nat)
    (h : j / 4 ≠ blockIndex P.1) : tripleEntry P Q R j = (0, 0) := by
  simp [tripleEntry, h]

theorem tripleEntry_col (P Q R : IVec × GVec) (t : Fin 7) (u : Fin 4)
    (hblock : blockIndex P.1 = t.val) :
    tripleEntry P Q R (colEquiv28 (t, u)).val =
      (let rep := representative P.1
       let f0 := (frame rep).getD 0 zero
       let f1 := (frame rep).getD 1 zero
       let x1 := gdotI P.2 f0
       let x2 := gdotI P.2 f1
       let deriv := gmul gI (gdotI Q.2 R.1)
       let nonlinear := gsmulVec deriv R.2
       let y1 := gdotI nonlinear f0
       let y2 := gdotI nonlinear f1
       match u.val with
       | 0 => gmul y1 x1
       | 1 => gmul y2 x2
       | 2 => gadd (gmul y1 x2) (gmul y2 x1)
       | _ =>
         let skew := gmul gI (gsub (gmul y1 x2) (gmul y2 x1))
         if P.1 = rep then skew else gneg skew) := by
  unfold tripleEntry
  rw [if_neg (by rw [colEquiv28_block, hblock]; exact fun h => h rfl),
    colEquiv28_within]

theorem denomAt_col (t : Fin 7) (u : Fin 4) :
    denomAt (colEquiv28 (t, u)).val =
      (let rep := booleanReps.getD t.val zero
       let n0 := dot ((frame rep).getD 0 zero) ((frame rep).getD 0 zero)
       let n1 := dot ((frame rep).getD 1 zero) ((frame rep).getD 1 zero)
       match u.val with
       | 0 => n0 * n0
       | 1 => n1 * n1
       | _ => n0 * n1) := by
  unfold denomAt
  rw [colEquiv28_block, colEquiv28_within]

private theorem column_assembly (a00 a11 a01re a01im X0 X1 Y0 Y1 n0 n1 : ℂ)
    (h0 : n0 ≠ 0) (h1 : n1 ≠ 0) :
    (Y0 * X0) / (n0 * n0) * a00 + (Y1 * X1) / (n1 * n1) * a11 +
        (Y0 * X1 + Y1 * X0) / (n0 * n1) * a01re +
        (Complex.I * (Y0 * X1 - Y1 * X0)) / (n0 * n1) * a01im =
      a00 * ((X0 / n0) * (Y0 / n0)) + a11 * ((X1 / n1) * (Y1 / n1)) +
        a01re * ((X1 / n1) * (Y0 / n0) + (X0 / n0) * (Y1 / n1)) +
        Complex.I * a01im * ((X1 / n1) * (Y0 / n0) - (X0 / n0) * (Y1 / n1)) := by
  field_simp

private theorem column_assembly_neg (a00 a11 a01re a01im X0 X1 Y0 Y1 n0 n1 : ℂ)
    (h0 : n0 ≠ 0) (h1 : n1 ≠ 0) :
    (Y0 * X0) / (n0 * n0) * a00 + (Y1 * X1) / (n1 * n1) * a11 +
        (Y0 * X1 + Y1 * X0) / (n0 * n1) * a01re +
        (-(Complex.I * (Y0 * X1 - Y1 * X0))) / (n0 * n1) * a01im =
      a00 * ((X0 / n0) * (Y0 / n0)) + a11 * ((X1 / n1) * (Y1 / n1)) +
        a01re * ((X1 / n1) * (Y0 / n0) + (X0 / n0) * (Y1 / n1)) -
        Complex.I * a01im * ((X1 / n1) * (Y0 / n0) - (X0 / n0) * (Y1 / n1)) := by
  field_simp
  ring

theorem frameNorm_ne_zero (t : Fin 7) (i : Fin 2) :
    (dot ((frame (booleanReps.getD t.val zero)).getD i.val zero)
      ((frame (booleanReps.getD t.val zero)).getD i.val zero) : Int) ≠ 0 := by
  fin_cases t <;> fin_cases i <;> decide

/-- The pairing of one resonant triple of a test field against the symbol. -/
noncomputable def triplePairing (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (P Q R : IVec × GVec) : ℂ :=
  Complex.I * Vec3.dot (cOfGVec Q.2) (cOfIVec R.1) *
    Vec3.dot (D (latticeOfIVec P.1) (cOfGVec P.2)) (cOfGVec R.2)

/-- The column sum of one resonant triple against the Hermitian encoding is the
symbol pairing of that triple.  This is the step that makes the integer row a
statement about `D`. -/
theorem triple_column_sum (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hsol : HasSolenoidalOutputMap D) (hherm : HasHermitianFiber D)
    (t : Fin 7) (P Q R : IVec × GVec)
    (hblock : blockIndex P.1 = t.val)
    (hrep : representative P.1 = booleanReps.getD t.val zero)
    (hx : Transverse (seedMode (boolMode t)) (cOfGVec P.2))
    (hpos : P.1 = representative P.1)
    (hPm : latticeOfIVec P.1 = seedMode (boolMode t)) :
    ∑ j : Fin 28,
        (cOfGZ (tripleEntry P Q R j.val) / ((denomAt j.val : Int) : ℂ)) *
          ((booleanEncoding D j : ℝ) : ℂ) =
      triplePairing D P Q R := by
  classical
  rw [sum_fin28_split]
  rw [Finset.sum_eq_single_of_mem t (Finset.mem_univ t)]
  · have hpos' : P.1 = booleanReps.getD t.val zero := hpos.trans hrep
    rw [Fin.sum_univ_four]
    rw [tripleEntry_col P Q R t 0 hblock, tripleEntry_col P Q R t 1 hblock,
      tripleEntry_col P Q R t 2 hblock, tripleEntry_col P Q R t 3 hblock,
      denomAt_col t 0, denomAt_col t 1, denomAt_col t 2, denomAt_col t 3]
    simp only [show ((0 : Fin 4) : Nat) = 0 from rfl, show ((1 : Fin 4) : Nat) = 1 from rfl,
      show ((2 : Fin 4) : Nat) = 2 from rfl, show ((3 : Fin 4) : Nat) = 3 from rfl,
      booleanEncoding_col, boolEntry, hrep, if_pos hpos']
    set f0 := (frame (booleanReps.getD t.val zero)).getD 0 zero with hf0def
    set f1 := (frame (booleanReps.getD t.val zero)).getD 1 zero with hf1def
    set deriv := gmul gI (gdotI Q.2 R.1) with hderiv
    set nl := gsmulVec deriv R.2 with hnl
    have hn0 : ((dot f0 f0 : Int) : ℂ) ≠ 0 := by
      exact_mod_cast (Int.cast_ne_zero (α := ℂ)).mpr (frameNorm_ne_zero t 0)
    have hn1 : ((dot f1 f1 : Int) : ℂ) ≠ 0 := by
      exact_mod_cast (Int.cast_ne_zero (α := ℂ)).mpr (frameNorm_ne_zero t 1)
    have hX0 : cOfGZ (gdotI P.2 f0) = Vec3.dot (cOfGVec P.2) (cOfIVec f0) := cOfGZ_gdotI _ _
    have hX1 : cOfGZ (gdotI P.2 f1) = Vec3.dot (cOfGVec P.2) (cOfIVec f1) := cOfGZ_gdotI _ _
    have hY0 : cOfGZ (gdotI nl f0) = Vec3.dot (cOfGVec nl) (cOfIVec f0) := cOfGZ_gdotI _ _
    have hY1 : cOfGZ (gdotI nl f1) = Vec3.dot (cOfGVec nl) (cOfIVec f1) := cOfGZ_gdotI _ _
    simp only [cOfGZ_mul, cOfGZ_add, cOfGZ_sub, cOfGZ_I, hX0, hX1, hY0, hY1,
      Int.cast_mul]
    rw [column_assembly _ _ _ _ _ _ _ _ _ _ hn0 hn1]
    -- the four-parameter block identity, in the frame of this mode
    have hframe0 : seedFrameComplex (boolMode t) 0 = cOfIVec f0 := by
      rw [seedFrameComplex_boolMode, hf0def]
    have hframe1 : seedFrameComplex (boolMode t) 1 = cOfIVec f1 := by
      rw [seedFrameComplex_boolMode, hf1def]
    have hnorm0 : ((seedFrameNorm (boolMode t) 0 : ℝ) : ℂ) = ((dot f0 f0 : Int) : ℂ) := by
      rw [seedFrameNorm_boolMode, hf0def]
      push_cast
      ring
    have hnorm1 : ((seedFrameNorm (boolMode t) 1 : ℝ) : ℂ) = ((dot f1 f1 : Int) : ℂ) := by
      rw [seedFrameNorm_boolMode, hf1def]
      push_cast
      ring
    have hmain := dot_symbol_hermitian D hsol hherm t (cOfGVec P.2) (cOfGVec nl) hx
    rw [hframe0, hframe1, hnorm0, hnorm1] at hmain
    rw [Vec3.dot_comm (cOfIVec f0) (cOfGVec nl), Vec3.dot_comm (cOfIVec f1) (cOfGVec nl)]
      at hmain
    rw [← hmain, hnl, cOfGVec_gsmulVec, Vec3.dot_smul_right, hderiv]
    unfold triplePairing
    rw [hPm, cOfGZ_mul, cOfGZ_I, cOfGZ_gdotI]
  · intro t' _ hne
    refine Finset.sum_eq_zero fun u _ => ?_
    have hz : tripleEntry P Q R (colEquiv28 (t', u)).val = (0, 0) := by
      refine tripleEntry_off_block P Q R _ ?_
      rw [colEquiv28_block, hblock]
      exact fun h => hne (Fin.ext h)
    rw [hz]
    simp [cOfGZ]

/-- The same identity when the triple's first mode is the negative of its
representative: the block is transported by reality and the imaginary column
changes sign, which is the orientation factor carried by `tripleEntry`. -/
theorem triple_column_sum_neg (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hsol : HasSolenoidalOutputMap D) (hherm : HasHermitianFiber D)
    (hreal : RealityCompatibleMap D) (t : Fin 7) (P Q R : IVec × GVec)
    (hblock : blockIndex P.1 = t.val)
    (hrep : representative P.1 = booleanReps.getD t.val zero)
    (hx : Transverse (seedMode (boolMode t)) (cOfGVec P.2))
    (hneg : P.1 ≠ representative P.1)
    (hPm : latticeOfIVec P.1 = -(seedMode (boolMode t))) :
    ∑ j : Fin 28,
        (cOfGZ (tripleEntry P Q R j.val) / ((denomAt j.val : Int) : ℂ)) *
          ((booleanEncoding D j : ℝ) : ℂ) =
      triplePairing D P Q R := by
  classical
  rw [sum_fin28_split]
  rw [Finset.sum_eq_single_of_mem t (Finset.mem_univ t)]
  · have hneg' : P.1 ≠ booleanReps.getD t.val zero := fun h => hneg (h.trans hrep.symm)
    rw [Fin.sum_univ_four]
    rw [tripleEntry_col P Q R t 0 hblock, tripleEntry_col P Q R t 1 hblock,
      tripleEntry_col P Q R t 2 hblock, tripleEntry_col P Q R t 3 hblock,
      denomAt_col t 0, denomAt_col t 1, denomAt_col t 2, denomAt_col t 3]
    simp only [show ((0 : Fin 4) : Nat) = 0 from rfl, show ((1 : Fin 4) : Nat) = 1 from rfl,
      show ((2 : Fin 4) : Nat) = 2 from rfl, show ((3 : Fin 4) : Nat) = 3 from rfl,
      booleanEncoding_col, boolEntry, hrep, if_neg hneg']
    set f0 := (frame (booleanReps.getD t.val zero)).getD 0 zero with hf0def
    set f1 := (frame (booleanReps.getD t.val zero)).getD 1 zero with hf1def
    set deriv := gmul gI (gdotI Q.2 R.1) with hderiv
    set nl := gsmulVec deriv R.2 with hnl
    have hn0 : ((dot f0 f0 : Int) : ℂ) ≠ 0 := by
      exact_mod_cast (Int.cast_ne_zero (α := ℂ)).mpr (frameNorm_ne_zero t 0)
    have hn1 : ((dot f1 f1 : Int) : ℂ) ≠ 0 := by
      exact_mod_cast (Int.cast_ne_zero (α := ℂ)).mpr (frameNorm_ne_zero t 1)
    have hX0 : cOfGZ (gdotI P.2 f0) = Vec3.dot (cOfGVec P.2) (cOfIVec f0) := cOfGZ_gdotI _ _
    have hX1 : cOfGZ (gdotI P.2 f1) = Vec3.dot (cOfGVec P.2) (cOfIVec f1) := cOfGZ_gdotI _ _
    have hY0 : cOfGZ (gdotI nl f0) = Vec3.dot (cOfGVec nl) (cOfIVec f0) := cOfGZ_gdotI _ _
    have hY1 : cOfGZ (gdotI nl f1) = Vec3.dot (cOfGVec nl) (cOfIVec f1) := cOfGZ_gdotI _ _
    simp only [cOfGZ_mul, cOfGZ_add, cOfGZ_sub, cOfGZ_I, cOfGZ_neg, hX0, hX1, hY0, hY1,
      Int.cast_mul]
    rw [column_assembly_neg _ _ _ _ _ _ _ _ _ _ hn0 hn1]
    -- the four-parameter block identity, in the frame of this mode
    have hframe0 : seedFrameComplex (boolMode t) 0 = cOfIVec f0 := by
      rw [seedFrameComplex_boolMode, hf0def]
    have hframe1 : seedFrameComplex (boolMode t) 1 = cOfIVec f1 := by
      rw [seedFrameComplex_boolMode, hf1def]
    have hnorm0 : ((seedFrameNorm (boolMode t) 0 : ℝ) : ℂ) = ((dot f0 f0 : Int) : ℂ) := by
      rw [seedFrameNorm_boolMode, hf0def]
      push_cast
      ring
    have hnorm1 : ((seedFrameNorm (boolMode t) 1 : ℝ) : ℂ) = ((dot f1 f1 : Int) : ℂ) := by
      rw [seedFrameNorm_boolMode, hf1def]
      push_cast
      ring
    have hmain := dot_symbol_hermitian_neg D hsol hherm hreal t (cOfGVec P.2) (cOfGVec nl) hx
    rw [hframe0, hframe1, hnorm0, hnorm1] at hmain
    rw [Vec3.dot_comm (cOfIVec f0) (cOfGVec nl), Vec3.dot_comm (cOfIVec f1) (cOfGVec nl)]
      at hmain
    rw [← hmain, hnl, cOfGVec_gsmulVec, Vec3.dot_smul_right, hderiv]
    unfold triplePairing
    rw [hPm, cOfGZ_mul, cOfGZ_I, cOfGZ_gdotI]
  · intro t' _ hne
    refine Finset.sum_eq_zero fun u _ => ?_
    have hz : tripleEntry P Q R (colEquiv28 (t', u)).val = (0, 0) := by
      refine tripleEntry_off_block P Q R _ ?_
      rw [colEquiv28_block, hblock]
      exact fun h => hne (Fin.ext h)
    rw [hz]
    simp [cOfGZ]

/-! ## Summing the triples of one test field -/

private theorem list_sum_div_mul (l : List ℂ) (d e : ℂ) :
    l.sum / d * e = (l.map (fun z => z / d * e)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [add_div, add_mul, ih]

private theorem sum_list_swap {α : Type*} (l : List α) (f : α → Fin 28 → ℂ) :
    ∑ j : Fin 28, (l.map (fun x => f x j)).sum =
      (l.map (fun x => ∑ j : Fin 28, f x j)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [Finset.sum_add_distrib, ih]

/-- The row of a test field, paired against the Hermitian encoding. -/
noncomputable def rowPairing (D : LatticeVec → CVec →ₗ[ℂ] CVec) (dat : TriadDatum) : ℂ :=
  ∑ j : Fin 28, (cOfGZ (numeratorEntry dat j.val) / ((denomAt j.val : Int) : ℂ)) *
    ((booleanEncoding D j : ℝ) : ℂ)

/-- The same test field, paired triple by triple against the symbol. -/
noncomputable def testPairing (D : LatticeVec → CVec →ₗ[ℂ] CVec) (dat : TriadDatum) : ℂ :=
  ((resonantTriples (modesOf dat)).map
    (fun x => triplePairing D x.1 x.2.1 x.2.2)).sum

/-- Given the per-triple identity, the whole row pairing is the sum of the
triple pairings. -/
theorem rowPairing_eq_testPairing (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (dat : TriadDatum)
    (h : ∀ x ∈ resonantTriples (modesOf dat),
      ∑ j : Fin 28,
          (cOfGZ (tripleEntry x.1 x.2.1 x.2.2 j.val) / ((denomAt j.val : Int) : ℂ)) *
            ((booleanEncoding D j : ℝ) : ℂ) = triplePairing D x.1 x.2.1 x.2.2) :
    rowPairing D dat = testPairing D dat := by
  unfold rowPairing testPairing
  have hcol : ∀ j : Fin 28,
      (cOfGZ (numeratorEntry dat j.val) / ((denomAt j.val : Int) : ℂ)) *
          ((booleanEncoding D j : ℝ) : ℂ) =
        ((resonantTriples (modesOf dat)).map (fun x =>
          (cOfGZ (tripleEntry x.1 x.2.1 x.2.2 j.val) / ((denomAt j.val : Int) : ℂ)) *
            ((booleanEncoding D j : ℝ) : ℂ))).sum := by
    intro j
    unfold numeratorEntry
    rw [cOfGZ_sum, List.map_map, list_sum_div_mul, List.map_map]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hcol j]
  rw [sum_list_swap]
  exact congrArg List.sum (List.map_congr_left h)

/-! ## The six permutations of a triad -/

theorem cOfIVec_eq_latticeToComplex (k : IVec) :
    cOfIVec k = latticeToComplex (latticeOfIVec k) := by
  funext i
  fin_cases i <;>
    simp [cOfIVec, realToComplexVec, realOfIVec, latticeToComplex, latticeOfIVec,
      latticeVec]

/-- The six orderings of one resonant triad assemble into the triad bracket. -/
theorem six_perm_sum (D : LatticeVec → CVec →ₗ[ℂ] CVec) (p q r : IVec)
    (a u v : GVec) :
    triplePairing D (p, a) (q, u) (r, v) + triplePairing D (p, a) (r, v) (q, u) +
        (triplePairing D (q, u) (p, a) (r, v) + triplePairing D (q, u) (r, v) (p, a)) +
        (triplePairing D (r, v) (p, a) (q, u) + triplePairing D (r, v) (q, u) (p, a)) =
      Complex.I * triadBracket D (latticeOfIVec p) (latticeOfIVec q) (latticeOfIVec r)
        (cOfGVec a) (cOfGVec u) (cOfGVec v) := by
  unfold triplePairing triadBracket rawRecipient
  simp only [cOfIVec_eq_latticeToComplex, Vec3.dot_add_right, Vec3.dot_smul_right]
  ring

/-! ## The twelve resonant triples of a test field

The six signed modes of a triad-supported field carry exactly two resonant
triads — the triad itself and its negative — and `resonantTriples` enumerates
their twelve orderings in a fixed pattern, the same for every datum. -/

/-- The twelve orderings, in the order `resonantTriples` produces them. -/
def expectedTriples (dat : TriadDatum) :
    List ((IVec × GVec) × (IVec × GVec) × (IVec × GVec)) :=
  let ms := modesOf dat
  let P := ms.getD 0 default
  let P' := ms.getD 1 default
  let Q := ms.getD 2 default
  let Q' := ms.getD 3 default
  let R := ms.getD 4 default
  let R' := ms.getD 5 default
  [(P, Q, R), (P, R, Q), (P', Q', R'), (P', R', Q'),
   (Q, P, R), (Q, R, P), (Q', P', R'), (Q', R', P'),
   (R, P, Q), (R, Q, P), (R', P', Q'), (R', Q', P')]

theorem resonantTriples_eq_expected_all :
    (booleanProvenance.all fun dat =>
      resonantTriples (modesOf dat) == expectedTriples dat) = true := by
  decide

theorem resonantTriples_eq_expected {dat : TriadDatum}
    (h : dat ∈ booleanProvenance) :
    resonantTriples (modesOf dat) = expectedTriples dat := by
  have hall := List.all_eq_true.mp resonantTriples_eq_expected_all dat h
  exact eq_of_beq hall

/-- The twelve triple pairings assemble into the two triad brackets. -/
theorem testPairing_eq_brackets (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    {dat : TriadDatum} (h : dat ∈ booleanProvenance) :
    testPairing D dat =
      Complex.I * triadBracket D (latticeOfIVec dat.p) (latticeOfIVec dat.q)
          (latticeOfIVec dat.r)
          (cOfGVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a)))
          (cOfGVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u)))
          (cOfGVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v))) +
        Complex.I * triadBracket D (latticeOfIVec (neg dat.p))
          (latticeOfIVec (neg dat.q)) (latticeOfIVec (neg dat.r))
          (cOfGVec (gconjVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a))))
          (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u))))
          (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v)))) := by
  unfold testPairing
  rw [resonantTriples_eq_expected h]
  rw [← six_perm_sum D dat.p dat.q dat.r, ← six_perm_sum D (neg dat.p) (neg dat.q)
    (neg dat.r)]
  simp only [expectedTriples, modesOf, List.map, List.sum_cons, List.sum_nil,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  ring

/-! ## The triad hypotheses of each datum

Everything `HasActiveTriadCancellation` asks of a datum — resonance, three
nonzero modes, non-collinearity, and transversality of the three polarizations —
is a decidable statement about the recorded integers. -/

theorem latticeOfIVec_add (a b : IVec) :
    latticeOfIVec (add a b) = latticeOfIVec a + latticeOfIVec b := by
  funext i
  fin_cases i <;> simp [latticeOfIVec, latticeVec, add]

theorem realOfIVec_ne_zero {x : IVec} (h : x ≠ zero) : realOfIVec x ≠ 0 := by
  intro hz
  apply h
  obtain ⟨a, b, c⟩ := x
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  have h2 := congrFun hz 2
  simp [realOfIVec] at h0 h1 h2
  simp [zero, h0, h1, h2]

theorem cross_realOfIVec (a b : IVec) :
    Vec3.cross (realOfIVec a) (realOfIVec b) = realOfIVec (cross a b) := by
  funext i
  fin_cases i <;>
    simp [Vec3.cross, realOfIVec, SeedCertificate.cross]

theorem cOfGVec_gOfIVec (k : IVec) : cOfGVec (gOfIVec k) = cOfIVec k := by
  funext i
  fin_cases i <;> simp [cOfGVec, gOfIVec, cOfIVec, realToComplexVec, realOfIVec, cOfGZ, gOf]

/-- Transversality of a phased polarization, from the integer orthogonality. -/
theorem transverse_amp {k pol : IVec} (h : dot k pol = 0) (b : Bool) :
    Transverse (latticeOfIVec k) (cOfGVec (gsmulVec (phaseOf b) (gOfIVec pol))) := by
  rw [cOfGVec_gsmulVec, cOfGVec_gOfIVec]
  refine transverse_smul _ ?_
  show Vec3.dot (latticeToComplex (latticeOfIVec k)) (cOfIVec pol) = 0
  rw [cOfIVec_eq_latticeToComplex]
  have hdot : Vec3.dot (latticeToComplex (latticeOfIVec k))
      (latticeToComplex (latticeOfIVec pol)) = ((dot k pol : Int) : ℂ) := by
    simp [Vec3.dot, latticeToComplex, latticeOfIVec, latticeVec, SeedCertificate.dot]
  rw [hdot, h]
  simp

/-- The decidable content of the triad hypotheses. -/
def datumOK (dat : TriadDatum) : Bool :=
  (add (add dat.p dat.q) dat.r == zero) && (dat.p != zero) && (dat.q != zero) &&
    (dat.r != zero) && (cross dat.q dat.r != zero) &&
    (dot dat.p dat.a == 0) && (dot dat.q dat.u == 0) && (dot dat.r dat.v == 0)

theorem datumOK_all : booleanProvenance.all datumOK = true := by decide

theorem datumOK_of_mem {dat : TriadDatum} (h : dat ∈ booleanProvenance) :
    datumOK dat = true := List.all_eq_true.mp datumOK_all dat h

@[simp] theorem latticeOfIVec_zero : latticeOfIVec zero = 0 := by
  funext i
  fin_cases i <;> simp [latticeOfIVec, latticeVec, zero]

theorem cOfGVec_gconjVec (w : GVec) : cOfGVec (gconjVec w) = conjVec (cOfGVec w) := by
  funext i
  fin_cases i <;> simp [cOfGVec, gconjVec, conjVec, cOfGZ, gconj]

theorem transverse_amp_conj {k pol : IVec} (h : dot k pol = 0) (b : Bool) :
    Transverse (latticeOfIVec (neg k))
      (cOfGVec (gconjVec (gsmulVec (phaseOf b) (gOfIVec pol)))) := by
  rw [latticeOfIVec_neg, cOfGVec_gconjVec]
  exact transverse_neg_conj (transverse_amp h b)

/-- Negating an integer triad preserves the resonance relation. -/
theorem neg_resonance {p q r : IVec} (h : add (add p q) r = zero) :
    add (add (neg p) (neg q)) (neg r) = zero := by
  simp only [add, neg, zero, Prod.mk.injEq] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by omega, by omega, by omega⟩

/-- The cross product is invariant under negating both arguments. -/
theorem cross_neg_neg (q r : IVec) : cross (neg q) (neg r) = cross q r := by
  simp only [SeedCertificate.cross, neg, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem neg_ne_zero_IVec {x : IVec} (h : x ≠ zero) : neg x ≠ zero := by
  intro hz
  apply h
  obtain ⟨a, b, c⟩ := x
  simp [neg, zero] at hz ⊢
  omega

/-- Both triad brackets of a recorded datum vanish under active triad
cancellation: the positive triad, and its negative. -/
theorem bracket_pos_zero (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) {dat : TriadDatum}
    (h : dat ∈ booleanProvenance) :
    triadBracket D (latticeOfIVec dat.p) (latticeOfIVec dat.q) (latticeOfIVec dat.r)
      (cOfGVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a)))
      (cOfGVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u)))
      (cOfGVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v))) = 0 := by
  have hok := datumOK_of_mem h
  simp only [datumOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hres, hp⟩, hq⟩, hr⟩, hcross⟩, ha⟩, hu⟩, hv⟩ := hok
  refine htriad _ _ _ _ _ _ ?_ (latticeOfIVec_ne_zero hp) (latticeOfIVec_ne_zero hq)
    (latticeOfIVec_ne_zero hr) ?_ (transverse_amp ha _) (transverse_amp hu _)
    (transverse_amp hv _)
  · rw [← latticeOfIVec_add, ← latticeOfIVec_add, hres, latticeOfIVec_zero]
  · show Vec3.cross (latticeToReal (latticeOfIVec dat.q))
      (latticeToReal (latticeOfIVec dat.r)) ≠ 0
    rw [latticeToReal_latticeOfIVec, latticeToReal_latticeOfIVec, cross_realOfIVec]
    exact realOfIVec_ne_zero hcross

theorem bracket_neg_zero (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) {dat : TriadDatum}
    (h : dat ∈ booleanProvenance) :
    triadBracket D (latticeOfIVec (neg dat.p)) (latticeOfIVec (neg dat.q))
      (latticeOfIVec (neg dat.r))
      (cOfGVec (gconjVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a))))
      (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u))))
      (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v)))) = 0 := by
  have hok := datumOK_of_mem h
  simp only [datumOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hres, hp⟩, hq⟩, hr⟩, hcross⟩, ha⟩, hu⟩, hv⟩ := hok
  refine htriad _ _ _ _ _ _ ?_ (latticeOfIVec_ne_zero (neg_ne_zero_IVec hp))
    (latticeOfIVec_ne_zero (neg_ne_zero_IVec hq))
    (latticeOfIVec_ne_zero (neg_ne_zero_IVec hr)) ?_ (transverse_amp_conj ha _)
    (transverse_amp_conj hu _) (transverse_amp_conj hv _)
  · rw [← latticeOfIVec_add, ← latticeOfIVec_add, neg_resonance hres,
      latticeOfIVec_zero]
  · show Vec3.cross (latticeToReal (latticeOfIVec (neg dat.q)))
      (latticeToReal (latticeOfIVec (neg dat.r))) ≠ 0
    rw [latticeToReal_latticeOfIVec, latticeToReal_latticeOfIVec, cross_realOfIVec]
    refine realOfIVec_ne_zero ?_
    rw [cross_neg_neg]
    exact hcross

/-! ## The row of every recorded test field annihilates every admissible symbol

Each of the twelve resonant triples of a test field contributes one column sum,
and `mode_column_sum` turns that column sum into a symbol pairing.  Summing the
twelve gives the two triad brackets of the field, and active triad cancellation
kills both. -/

theorem transverse_neg_iff {k : LatticeVec} {v : CVec} :
    Transverse (-k) v ↔ Transverse k v := by
  have hk : latticeToComplex (-k) = -latticeToComplex k := by
    funext i
    simp [latticeToComplex]
  have hd : Vec3.dot (-latticeToComplex k) v = -Vec3.dot (latticeToComplex k) v := by
    simp [Vec3.dot]
    ring
  unfold Transverse
  rw [hk, hd, neg_eq_zero]

theorem neg_neg_IVec (k : IVec) : neg (neg k) = k := by
  obtain ⟨a, b, c⟩ := k
  simp [neg]

theorem representative_cases (k : IVec) :
    representative k = k ∨ representative k = neg k := by
  unfold SeedCertificate.representative
  split_ifs <;> simp

/-- The block bookkeeping of one signed mode: its unoriented representative is
the Boolean representative recorded at the block index. -/
def modeOK (k : IVec) : Bool :=
  decide (blockIndex k < 7) && (representative k == booleanReps.getD (blockIndex k) zero)

def datumModesOK (dat : TriadDatum) : Bool := (modesOf dat).all fun x => modeOK x.1

theorem datumModesOK_all : booleanProvenance.all datumModesOK = true := by decide

/-- **One resonant triple, one symbol pairing.**  Whichever orientation the
leading mode has, its column sum against the Hermitian encoding is the symbol
pairing of the triple. -/
theorem mode_column_sum (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hsol : HasSolenoidalOutputMap D) (hherm : HasHermitianFiber D)
    (hreal : RealityCompatibleMap D) (P Q R : IVec × GVec)
    (hmode : modeOK P.1 = true)
    (hx : Transverse (latticeOfIVec P.1) (cOfGVec P.2)) :
    ∑ j : Fin 28,
        (cOfGZ (tripleEntry P Q R j.val) / ((denomAt j.val : Int) : ℂ)) *
          ((booleanEncoding D j : ℝ) : ℂ) =
      triplePairing D P Q R := by
  simp only [modeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmode
  obtain ⟨hlt, hrep⟩ := hmode
  set t : Fin 7 := ⟨blockIndex P.1, hlt⟩ with htdef
  have hblock : blockIndex P.1 = t.val := rfl
  have hM : seedMode (boolMode t) = latticeOfIVec (booleanReps.getD t.val zero) := by
    rw [seedMode, seedModeIVec_boolMode]
  by_cases hpos : P.1 = representative P.1
  · have hPm : latticeOfIVec P.1 = seedMode (boolMode t) := by
      rw [hM]
      exact congrArg latticeOfIVec (hpos.trans hrep)
    exact triple_column_sum D hsol hherm t P Q R hblock hrep (hPm ▸ hx) hpos hPm
  · have hneg : representative P.1 = neg P.1 :=
      (representative_cases P.1).resolve_left fun hc => hpos hc.symm
    have hPneg : P.1 = neg (booleanReps.getD t.val zero) := by
      rw [← hrep, hneg, neg_neg_IVec]
    have hPm : latticeOfIVec P.1 = -(seedMode (boolMode t)) := by
      rw [hM, hPneg, latticeOfIVec_neg]
    exact triple_column_sum_neg D hsol hherm hreal t P Q R hblock hrep
      (transverse_neg_iff.mp (hPm ▸ hx)) hpos hPm

theorem mem_resonantTriples_fst {ms : List (IVec × GVec)}
    {x : (IVec × GVec) × (IVec × GVec) × (IVec × GVec)}
    (h : x ∈ resonantTriples ms) : x.1 ∈ ms := by
  unfold resonantTriples at h
  rw [List.mem_flatMap] at h
  obtain ⟨P, hP, h⟩ := h
  rw [List.mem_flatMap] at h
  obtain ⟨Q, -, h⟩ := h
  rw [List.mem_filterMap] at h
  obtain ⟨R, -, h⟩ := h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  rw [← h]
  exact hP

/-- Every signed mode of a recorded test field is transverse to its own
wavevector: the field is divergence free. -/
theorem modesOf_transverse {dat : TriadDatum} (h : dat ∈ booleanProvenance)
    {x : IVec × GVec} (hx : x ∈ modesOf dat) :
    Transverse (latticeOfIVec x.1) (cOfGVec x.2) := by
  have hok := datumOK_of_mem h
  simp only [datumOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, ha⟩, hu⟩, hv⟩ := hok
  simp only [modesOf, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact transverse_amp ha _
  · exact transverse_amp_conj ha _
  · exact transverse_amp hu _
  · exact transverse_amp_conj hu _
  · exact transverse_amp hv _
  · exact transverse_amp_conj hv _

/-- **The physical rows annihilate the Hermitian encoding.**  For every recorded
triad datum, the Euler constraint row of its test field, paired against the
twenty-eight Hermitian seed parameters of any solenoidal, Hermitian,
reality-compatible symbol with active triad cancellation, vanishes.

This is the kernel counterpart of the external exact check: the certificate rows
are not merely integers that happen to annihilate the encoding, they are the
constraint rows of explicit divergence-free test fields, and they vanish because
the triad brackets of those fields vanish. -/
theorem rowPairing_zero (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hsol : HasSolenoidalOutputMap D) (hherm : HasHermitianFiber D)
    (hreal : RealityCompatibleMap D) (htriad : HasActiveTriadCancellation D)
    {dat : TriadDatum} (h : dat ∈ booleanProvenance) :
    rowPairing D dat = 0 := by
  have hmodes := List.all_eq_true.mp datumModesOK_all dat h
  have hcol : ∀ x ∈ resonantTriples (modesOf dat),
      ∑ j : Fin 28,
          (cOfGZ (tripleEntry x.1 x.2.1 x.2.2 j.val) / ((denomAt j.val : Int) : ℂ)) *
            ((booleanEncoding D j : ℝ) : ℂ) = triplePairing D x.1 x.2.1 x.2.2 := by
    intro x hx
    have hm := mem_resonantTriples_fst hx
    exact mode_column_sum D hsol hherm hreal x.1 x.2.1 x.2.2
      (List.all_eq_true.mp hmodes x.1 hm) (modesOf_transverse h hm)
  rw [rowPairing_eq_testPairing D dat hcol, testPairing_eq_brackets D h,
    bracket_pos_zero D htriad h, bracket_neg_zero D htriad h]
  ring

end FourierMultiplierRigidity.SolenoidalSeedBridge
