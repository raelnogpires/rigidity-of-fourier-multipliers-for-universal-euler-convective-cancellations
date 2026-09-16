import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Boolean seed rank certificate (Hermitian solenoidal)

The manuscript asserts that the seven-mode Boolean seed — mode classes `(1,0,0)`, `(0,1,0)`, `(0,0,1)`,
`(1,1,0)`, `(1,0,1)`, `(0,1,1)`, `(1,1,1)` — determines a Hermitian
reality-compatible solenoidal multiplier up to a two-dimensional kernel
(energy and helicity).

Each unoriented mode carries four real parameters (a 2×2 Hermitian matrix in
a transverse orthonormal frame), giving 4 × 7 = 28 unknowns total.  The cubic
Euler cancellation identity on all non-collinear triads inside the fourteen
signed seed modes supplies 592 real scalar equations; 26 are independent,
leaving a kernel of dimension 2.

This file:
1. presents the 26 × 28 denominator-free integer constraint matrix;
2. reduces it modulo the prime 101;
3. extracts a 26 × 26 minor and verifies its right inverse entry-by-entry via
   `native_decide`, establishing rank ≥ 26;
4. verifies that the energy and helicity parameter vectors lie in the kernel,
   establishing that the two known invariants account for the entire nullity.

The row data of that reconstruction is internalized in
`SolenoidalSeedBridge.lean`: it records the triad, transverse polarizations and
phases behind each row, recomputes the row inside Lean, and checks it against
the matrix below by `decide`.  What remains external is the semantic identity —
that these coefficients are the Euler triad bracket of an actual symbol — which
`SeedBridge.lean` supplies in the unrestricted case.  The exact program
`verification/verify_solenoidal_seed_semantics.py` remains as an independent
audit.  The distinction is recorded explicitly in `lean/README.md`.
-/

namespace FourierMultiplierRigidity.SolenoidalSeedCertificate

instance : Fact (Nat.Prime 101) := ⟨by decide⟩
abbrev F := ZMod 101
abbrev BRow := Array F
abbrev BZRow := Array Int

/-! ## The 26 × 28 integer constraint matrix

Each column block of four corresponds to one of the seven Boolean seed
representatives, ordered lexicographically:
  (0,0,1), (0,1,0), (0,1,1), (1,0,0), (1,0,1), (1,1,0), (1,1,1).
Within each block the four Hermitian parameters are:
  α₁₁, α₂₂, Re α₁₂, Im α₁₂
in the transverse frame computed by `SeedCertificate.frame`. -/

def booleanSeedMatrixZ : List BZRow := [
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, -2],
  #[6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, -6, 0, 0, 0, -2, 0],
  #[0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -1],
  #[-2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, -1, 0, -1, 0],
  #[0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, -3, 0, -1, 0],
  #[0, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 1, 0, 1, 0],
  #[0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, -1, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, -2],
  #[0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, -6, 0, 0, 0, 0, 0, 0, 0, -2, 0],
  #[0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -1],
  #[0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, 0, 0, 0, 1, 0, -1, 0],
  #[0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 3, 0, -1, 0],
  #[0, 0, 0, 0, 0, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 1, 0],
  #[0, 0, 0, 0, 6, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, -1, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, -6, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, -6, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, -1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 6, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 1, 2, 0],
  #[0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]

/-! ## Modular reduction and row-echelon rank -/

def castBZRow (row : BZRow) : BRow := Array.map (fun z : Int => (z : F)) row

def booleanSeedMatrixF : List BRow := booleanSeedMatrixZ.map castBZRow

def firstPivotB (row : BRow) : Option Nat :=
  (List.range row.size).find? fun j => row[j]! ≠ 0

def addScaledB (x : F) (source target : BRow) : BRow :=
  Array.ofFn fun j : Fin 28 => target[j.val]! - x * source[j.val]!

def reduceBasisB (basis : List (Nat × BRow)) (source : BRow) : BRow :=
  basis.foldl (fun row entry =>
    let x := row[entry.1]!
    if x = 0 then row else addScaledB x entry.2 row) source

def insertBasisB (basis : List (Nat × BRow)) (source : BRow) : List (Nat × BRow) :=
  let row := reduceBasisB basis source
  match firstPivotB row with
  | none => basis
  | some pivot =>
      let normalized := row.map (· * (row[pivot]!)⁻¹)
      basis ++ [(pivot, normalized)]

def rowRankB (matrix : List BRow) : Nat :=
  (matrix.foldl insertBasisB []).length

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- The Boolean seed constraint matrix has rank 26 modulo 101. -/
theorem booleanSeed_rank : rowRankB booleanSeedMatrixF = 26 := by
  native_decide

/-! ## Pivot selection and minor extraction -/

structure BTrackedPivot where
  pivot : Nat
  source : Nat
  row : BRow

def reduceBTracked (basis : List BTrackedPivot) (source : BRow) : BRow :=
  basis.foldl (fun row entry =>
    let x := row[entry.pivot]!
    if x = 0 then row else addScaledB x entry.row row) source

def insertBTracked (basis : List BTrackedPivot) (entry : BRow × Nat) :
    List BTrackedPivot :=
  let row := reduceBTracked basis entry.1
  match firstPivotB row with
  | none => basis
  | some pivot =>
      let normalized := row.map (· * (row[pivot]!)⁻¹)
      basis ++ [{ pivot := pivot, source := entry.2, row := normalized }]

def booleanTrackedPivots : List BTrackedPivot :=
  booleanSeedMatrixF.zipIdx.foldl insertBTracked []

def selectedBooleanRows : List Nat := booleanTrackedPivots.map (·.source)
def selectedBooleanCols : List Nat := booleanTrackedPivots.map (·.pivot)

theorem booleanSelected_counts :
    selectedBooleanRows.length = 26 ∧ selectedBooleanCols.length = 26 := by
  native_decide

/-! ## 26 × 26 minor and its inverse -/

def booleanMinorEntryF (i j : Nat) : F :=
  ((booleanSeedMatrixF.getD (selectedBooleanRows.getD i 0) #[]).getD
    (selectedBooleanCols.getD j 0) 0)

def booleanAugmented : Array BRow :=
  Array.ofFn fun i : Fin 26 => Array.ofFn fun j : Fin 52 =>
    if j.val < 26 then booleanMinorEntryF i j
    else if j.val - 26 = i.val then 1 else 0

def booleanGJStep (matrix : Array BRow) (i : Nat) : Array BRow :=
  let source := matrix[i]!
  let pivotInv := (source[i]!)⁻¹
  let pivotRow : BRow := Array.ofFn fun j : Fin 52 => pivotInv * source[j.val]!
  Array.ofFn fun rowIndex : Fin 26 =>
    if rowIndex.val = i then pivotRow
    else
      let factor := (matrix[rowIndex.val]!)[i]!
      Array.ofFn fun j : Fin 52 =>
        (matrix[rowIndex.val]!)[j.val]! - factor * pivotRow[j.val]!

def booleanReduced : Array BRow :=
  (List.range 26).foldl booleanGJStep booleanAugmented

def booleanInverseEntryF (i j : Nat) : F :=
  (booleanReduced[i]!).getD (26 + j) 0

def booleanMinorTimesInverse (i j : Nat) : F :=
  ∑ k : Fin 26, booleanMinorEntryF i k * booleanInverseEntryF k j

/-- The 26 × 26 minor has a right inverse modulo 101. -/
theorem booleanMinor_has_right_inverse :
    ∀ i j : Fin 26,
      booleanMinorTimesInverse i j = if i = j then 1 else 0 := by
  native_decide

def booleanMinorMatrixF : Matrix (Fin 26) (Fin 26) F :=
  fun i j => booleanMinorEntryF i j

def booleanInverseMatrixF : Matrix (Fin 26) (Fin 26) F :=
  fun i j => booleanInverseEntryF i j

theorem booleanMinorMatrixF_mul_inverse :
    booleanMinorMatrixF * booleanInverseMatrixF = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  exact booleanMinor_has_right_inverse i j

theorem booleanMinorMatrixF_det_ne_zero : booleanMinorMatrixF.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det booleanMinorMatrixF_mul_inverse
  simp [Matrix.det_mul, hzero] at hdet

/-! ## Lift to ℤ and ℝ -/

def booleanMinorEntryZ (i j : Nat) : Int :=
  ((booleanSeedMatrixZ.getD (selectedBooleanRows.getD i 0) #[]).getD
    (selectedBooleanCols.getD j 0) 0)

def booleanMinorMatrixZ : Matrix (Fin 26) (Fin 26) Int :=
  fun i j => booleanMinorEntryZ i j

theorem booleanMinorMatrixF_is_integer_reduction :
    booleanMinorMatrixZ.map (fun z => (z : F)) = booleanMinorMatrixF := by
  native_decide

theorem booleanMinorMatrixZ_det_ne_zero : booleanMinorMatrixZ.det ≠ 0 := by
  intro hzero
  apply booleanMinorMatrixF_det_ne_zero
  rw [← booleanMinorMatrixF_is_integer_reduction, ← Int.cast_det, hzero]
  simp

def booleanMinorMatrixR : Matrix (Fin 26) (Fin 26) ℝ :=
  booleanMinorMatrixZ.map fun z => (z : ℝ)

theorem booleanMinorMatrixR_det_ne_zero : booleanMinorMatrixR.det ≠ 0 := by
  unfold booleanMinorMatrixR
  rw [← Int.cast_det]
  exact_mod_cast booleanMinorMatrixZ_det_ne_zero

/-! ## The complete `26 × 28` Hermitian seed matrix -/

/-- The full integer seed matrix, now exposed as a typed matrix rather than
only as an array used by the rank program. -/
def booleanSeedMatrixTypedZ : Matrix (Fin 26) (Fin 28) Int :=
  fun i j ↦ (booleanSeedMatrixZ.getD i.val #[]).getD j.val 0

/-- The real matrix of the twenty-six selected Boolean-seed rows.  Their row
data is recomputed from explicit triad-supported field tests in
`SolenoidalSeedBridge.lean`; the symbol-level identity behind those tests is
still the external verifier named in the module documentation. -/
def booleanSeedMatrixR : Matrix (Fin 26) (Fin 28) ℝ :=
  booleanSeedMatrixTypedZ.map fun z ↦ (z : ℝ)

private theorem selectedBooleanRows_lt :
    ∀ i : Fin 26, selectedBooleanRows.getD i.val 0 < 26 := by
  native_decide

private theorem selectedBooleanCols_lt :
    ∀ j : Fin 26, selectedBooleanCols.getD j.val 0 < 28 := by
  native_decide

private def selectedBooleanRowFin (i : Fin 26) : Fin 26 :=
  ⟨selectedBooleanRows.getD i.val 0, selectedBooleanRows_lt i⟩

private def selectedBooleanColFin (j : Fin 26) : Fin 28 :=
  ⟨selectedBooleanCols.getD j.val 0, selectedBooleanCols_lt j⟩

theorem booleanMinor_is_submatrix :
    booleanSeedMatrixR.submatrix selectedBooleanRowFin selectedBooleanColFin =
      booleanMinorMatrixR := by
  rfl

/-- The actual Boolean-seed evaluation matrix has full row rank.  The proof
uses the certified nonsingular `26 × 26` minor above. -/
theorem booleanSeedMatrixR_rank : booleanSeedMatrixR.rank = 26 := by
  have hminor : booleanMinorMatrixR.rank = 26 := by
    simpa using Matrix.rank_of_det_ne_zero booleanMinorMatrixR_det_ne_zero
  have hlo : booleanMinorMatrixR.rank ≤ booleanSeedMatrixR.rank := by
    rw [← booleanMinor_is_submatrix]
    exact Matrix.rank_submatrix_le _ _ _
  have hhi : booleanSeedMatrixR.rank ≤ 26 := Matrix.rank_le_height _
  omega

/-- The twenty-six actual seed evaluations leave exactly the expected
two-dimensional energy--helicity kernel. -/
theorem booleanSeedMatrixR_nullity :
    Module.finrank ℝ (LinearMap.ker booleanSeedMatrixR.mulVecLin) = 2 := by
  have hdim : booleanSeedMatrixR.rank +
      Module.finrank ℝ (LinearMap.ker booleanSeedMatrixR.mulVecLin) = 28 := by
    simpa [Matrix.rank] using
      booleanSeedMatrixR.mulVecLin.finrank_range_add_finrank_ker
  rw [booleanSeedMatrixR_rank] at hdim
  omega

/-! ## Kernel verification: energy and helicity annihilate the matrix -/

def energyVecZ : Array Int := #[1, 1, 0, 0, 1, 1, 0, 0, 2, 4, 0, 0,
  1, 1, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 2, 6, 0, 0]

def helicityVecZ : Array Int := #[0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -4,
  0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, -6]

def dotRowZ (row : BZRow) (v : Array Int) : Int :=
  (Array.zipWith (· * ·) row v).foldl (· + ·) 0

/-- Energy lies in the kernel of the Boolean seed constraint matrix. -/
theorem energy_in_kernel :
    ∀ row ∈ booleanSeedMatrixZ, dotRowZ row energyVecZ = 0 := by
  native_decide

/-- Helicity lies in the kernel of the Boolean seed constraint matrix. -/
theorem helicity_in_kernel :
    ∀ row ∈ booleanSeedMatrixZ, dotRowZ row helicityVecZ = 0 := by
  native_decide

/-- A separating-coordinate check, not a formal linear-independence theorem. -/
theorem energy_helicity_separating_coordinate :
    energyVecZ[3]! = 0 ∧ helicityVecZ[3]! ≠ 0 := by
  native_decide

end FourierMultiplierRigidity.SolenoidalSeedCertificate
