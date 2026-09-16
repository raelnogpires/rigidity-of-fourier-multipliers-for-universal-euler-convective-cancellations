import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Kernel-checked finite seed certificate

This file reconstructs the unrestricted-output unit-cube constraint matrix
from its lattice geometry and computes its rank over the prime field
`ZMod 1000003`.  It does not import a rank reported by Python.
-/

namespace FourierMultiplierRigidity.SeedCertificate

abbrev IVec := Int × Int × Int
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

abbrev F := ZMod 101
abbrev FVec := F × F × F
abbrev Row := Array F
abbrev ZVec := Int × Int × Int
abbrev ZRow := Array Int

def add (a b : IVec) : IVec := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def neg (a : IVec) : IVec := (-a.1, -a.2.1, -a.2.2)
def sub (a b : IVec) : IVec := add a (neg b)

def cross (a b : IVec) : IVec :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
   a.2.2 * b.1 - a.1 * b.2.2,
   a.1 * b.2.1 - a.2.1 * b.1)

def dot (a b : IVec) : Int :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def zero : IVec := (0, 0, 0)
def axes : List IVec := [(1, 0, 0), (0, 1, 0), (0, 0, 1)]

def seed : List IVec :=
  [-1, 0, 1].flatMap fun x ↦
    [-1, 0, 1].flatMap fun y ↦
      [-1, 0, 1].filterMap fun z ↦
        if (x, y, z) = zero then none else some (x, y, z)

def representative (k : IVec) : IVec :=
  if k.1 > 0 then k else if k.1 < 0 then neg k
  else if k.2.1 > 0 then k else if k.2.1 < 0 then neg k
  else if k.2.2 > 0 then k else neg k

def representatives : List IVec :=
  [(0, 0, 1), (0, 1, -1), (0, 1, 0), (0, 1, 1),
   (1, -1, -1), (1, -1, 0), (1, -1, 1), (1, 0, -1),
   (1, 0, 0), (1, 0, 1), (1, 1, -1), (1, 1, 0), (1, 1, 1)]

def transverseBasis (k : IVec) : List IVec :=
  let candidates := axes.map (cross k) |>.filter (· ≠ zero)
  match candidates with
  | [] => []
  | first :: rest =>
      first :: (rest.filter (cross first · ≠ zero)).take 1

def frame (k : IVec) : List IVec :=
  match transverseBasis k with
  | first :: _ => [first, cross k first]
  | [] => []

def castVec (v : IVec) : FVec := (v.1, v.2.1, v.2.2)
def dotF (a b : FVec) : F := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
def smulF (c : F) (v : FVec) : FVec := (c * v.1, c * v.2.1, c * v.2.2)
def addF (a b : FVec) : FVec := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def raw (q r u v : IVec) : FVec :=
  addF (smulF (dotF (castVec u) (castVec r)) (castVec v))
    (smulF (dotF (castVec v) (castVec q)) (castVec u))

def component (v : FVec) (i : Nat) : F :=
  if i = 0 then v.1 else if i = 1 then v.2.1 else v.2.2

def coordinate (x f : IVec) : F := (dot x f : F) * (dot f f : F)⁻¹

def modeIndex (k : IVec) : Nat :=
  representatives.idxOf (representative k)

def orientation (k : IVec) : F := if k = representative k then 1 else -1

def recipientCoefficient (k x : IVec) (parents : FVec)
    (mode output input part : Nat) : F :=
  if modeIndex k = mode then
    let f := (frame (representative k)).getD input zero
    let base := coordinate x f * component parents output
    if part = 0 then base else orientation k * base
  else 0

def bracketCoefficient (p q r a u v : IVec) (column : Nat) : F :=
  let mode := column / 12
  let within := column % 12
  let output := within / 4
  let input := (within % 4) / 2
  let part := within % 2
  recipientCoefficient p a (raw q r u v) mode output input part +
  recipientCoefficient q u (raw r p v a) mode output input part +
  recipientCoefficient r v (raw p q a u) mode output input part

def constraintRow (p q r a u v : IVec) (imaginary : Bool) : Row :=
  Array.ofFn fun j : Fin 156 ↦
    if (j.val % 2 = 1) = imaginary then bracketCoefficient p q r a u v j else 0

def lexLe (a b : IVec) : Bool :=
  a.1 < b.1 || (a.1 = b.1 &&
    (a.2.1 < b.2.1 || (a.2.1 = b.2.1 && a.2.2 ≤ b.2.2)))

def triads : List (IVec × IVec × IVec) :=
  seed.flatMap fun p ↦ seed.filterMap fun q ↦
    let r := neg (add p q)
    if r ∈ seed && lexLe p q && lexLe q r && cross p q ≠ zero
    then some (p, q, r) else none

def polarizationTriples (p q r : IVec) : List (IVec × IVec × IVec) :=
  (transverseBasis p).flatMap fun a ↦
    (transverseBasis q).flatMap fun u ↦
      (transverseBasis r).map fun v ↦ (a, u, v)

def rows : List Row :=
  triads.flatMap fun t ↦
    (polarizationTriples t.1 t.2.1 t.2.2).flatMap fun x ↦
      [constraintRow t.1 t.2.1 t.2.2 x.1 x.2.1 x.2.2 false,
       constraintRow t.1 t.2.1 t.2.2 x.1 x.2.1 x.2.2 true]

/-! The denominator-free integer matrix.  Its unknown in column `(k,o,i,s)`
is the corresponding real or imaginary block entry divided by the squared
length of the `i`th transverse frame vector.  Thus it has exactly the same
real kernel information as `rows`, but reduction modulo a prime is now
literally entrywise reduction of an integer matrix. -/

def castVecZ (v : IVec) : ZVec := v

def dotZ (a b : ZVec) : Int :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def smulZ (c : Int) (v : ZVec) : ZVec :=
  (c * v.1, c * v.2.1, c * v.2.2)

def addZ (a b : ZVec) : ZVec :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def rawZ (q r u v : IVec) : ZVec :=
  addZ (smulZ (dotZ (castVecZ u) (castVecZ r)) (castVecZ v))
    (smulZ (dotZ (castVecZ v) (castVecZ q)) (castVecZ u))

def componentZ (v : ZVec) (i : Nat) : Int :=
  if i = 0 then v.1 else if i = 1 then v.2.1 else v.2.2

def recipientCoefficientZ (k x : IVec) (parents : ZVec)
    (mode output input part : Nat) : Int :=
  if modeIndex k = mode then
    let f := (frame (representative k)).getD input zero
    let base := dot x f * componentZ parents output
    if part = 0 then base else if k = representative k then base else -base
  else 0

def bracketCoefficientZ (p q r a u v : IVec) (column : Nat) : Int :=
  let mode := column / 12
  let within := column % 12
  let output := within / 4
  let input := (within % 4) / 2
  let part := within % 2
  recipientCoefficientZ p a (rawZ q r u v) mode output input part +
  recipientCoefficientZ q u (rawZ r p v a) mode output input part +
  recipientCoefficientZ r v (rawZ p q a u) mode output input part

def constraintRowZ (p q r a u v : IVec) (imaginary : Bool) : ZRow :=
  Array.ofFn fun j : Fin 156 ↦
    if (j.val % 2 = 1) = imaginary then bracketCoefficientZ p q r a u v j else 0

def rowsZ : List ZRow :=
  triads.flatMap fun t ↦
    (polarizationTriples t.1 t.2.1 t.2.2).flatMap fun x ↦
      [constraintRowZ t.1 t.2.1 t.2.2 x.1 x.2.1 x.2.2 false,
       constraintRowZ t.1 t.2.1 t.2.2 x.1 x.2.1 x.2.2 true]

def castZRow (row : ZRow) : Row := Array.map (fun z : Int ↦ (z : F)) row

def rowsZMod : List Row := rowsZ.map castZRow

def firstPivot (row : Row) : Option Nat :=
  (List.range row.size).find? fun j ↦ row[j]! ≠ 0

def addScaled (x : F) (source target : Row) : Row :=
  Array.ofFn fun j : Fin 156 ↦ target[j.val]! - x * source[j.val]!

def reduceBy (basis : List (Nat × Row)) (source : Row) : Row :=
  basis.foldl (fun row entry ↦
    let x := row[entry.1]!
    if x = 0 then row else addScaled x entry.2 row) source

def insertBasis (basis : List (Nat × Row)) (source : Row) : List (Nat × Row) :=
  let row := reduceBy basis source
  match firstPivot row with
  | none => basis
  | some pivot =>
      let normalized := row.map (· * (row[pivot]!)⁻¹)
      basis ++ [(pivot, normalized)]

def rowRank (matrix : List Row) : Nat :=
  (matrix.foldl insertBasis []).length

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem seed_counts : seed.length = 26 ∧ representatives.length = 13 ∧
    triads.length = 44 ∧ rows.length = 704 := by
  decide

/-- The 13-mode unrestricted-output seed has codimension twelve. The matrix
is reconstructed above; this equality is checked by definitional reduction. -/
theorem seed_rank : rowRank rows = 144 := by
  native_decide

/-- The denominator-free integer matrix retains rank 144 after reduction
modulo 101. -/
theorem seed_rank_integer_reduction : rowRank rowsZMod = 144 := by
  native_decide

structure TrackedPivot where
  pivot : Nat
  source : Nat
  row : Row

def reduceByTracked (basis : List TrackedPivot) (source : Row) : Row :=
  basis.foldl (fun row entry ↦
    let x := row[entry.pivot]!
    if x = 0 then row else addScaled x entry.row row) source

def insertTracked (basis : List TrackedPivot) (entry : Row × Nat) :
    List TrackedPivot :=
  let row := reduceByTracked basis entry.1
  match firstPivot row with
  | none => basis
  | some pivot =>
      let normalized := row.map (· * (row[pivot]!)⁻¹)
      basis ++ [{ pivot := pivot, source := entry.2, row := normalized }]

def trackedPivots : List TrackedPivot :=
  rowsZMod.zipIdx.foldl insertTracked []

def selectedRows : List Nat := trackedPivots.map (·.source)
def selectedColumns : List Nat := trackedPivots.map (·.pivot)

theorem selected_counts : selectedRows.length = 144 ∧ selectedColumns.length = 144 := by
  native_decide

theorem selectedColumn_lt (i : Fin 144) : selectedColumns.getD i 0 < 156 := by
  native_decide +revert

def minorEntryF (i j : Nat) : F :=
  ((rowsZMod.getD (selectedRows.getD i 0) #[]).getD
    (selectedColumns.getD j 0) 0)

def augmentedRows : Array Row :=
  Array.ofFn fun i : Fin 144 ↦ Array.ofFn fun j : Fin 288 ↦
    if j.val < 144 then minorEntryF i j else if j.val - 144 = i.val then 1 else 0

def gaussJordanStep (matrix : Array Row) (i : Nat) : Array Row :=
  let source := matrix[i]!
  let pivotInv := (source[i]!)⁻¹
  let pivotRow : Row := Array.ofFn fun j : Fin 288 ↦ pivotInv * source[j.val]!
  Array.ofFn fun rowIndex : Fin 144 ↦
    if rowIndex.val = i then pivotRow
    else
      let factor := (matrix[rowIndex.val]!)[i]!
      Array.ofFn fun j : Fin 288 ↦
        (matrix[rowIndex.val]!)[j.val]! - factor * pivotRow[j.val]!

def reducedAugmentedRows : Array Row :=
  (List.range 144).foldl gaussJordanStep augmentedRows

def inverseEntryF (i j : Nat) : F :=
  (reducedAugmentedRows[i]!).getD (144 + j) 0

def minorTimesInverse (i j : Nat) : F :=
  ∑ k : Fin 144, minorEntryF i k * inverseEntryF k j

/-- A compact inverse certificate for the selected `144 × 144` modular
minor.  The inverse is constructed by Gauss--Jordan elimination, but the
theorem independently checks the defining product entry by entry. -/
theorem modular_minor_has_right_inverse :
    ∀ i j : Fin 144,
      minorTimesInverse i j = if i = j then 1 else 0 := by
  native_decide

def minorMatrixF : Matrix (Fin 144) (Fin 144) F :=
  fun i j ↦ minorEntryF i j

def inverseMatrixF : Matrix (Fin 144) (Fin 144) F :=
  fun i j ↦ inverseEntryF i j

theorem minorMatrixF_mul_inverseMatrixF :
    minorMatrixF * inverseMatrixF = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  exact modular_minor_has_right_inverse i j

theorem minorMatrixF_det_ne_zero : minorMatrixF.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det minorMatrixF_mul_inverseMatrixF
  simp [Matrix.det_mul, hzero] at hdet

def minorEntryZ (i j : Nat) : Int :=
  ((rowsZ.getD (selectedRows.getD i 0) #[]).getD
    (selectedColumns.getD j 0) 0)

def minorMatrixZ : Matrix (Fin 144) (Fin 144) Int :=
  fun i j ↦ minorEntryZ i j

theorem minorMatrixF_is_integer_reduction :
    minorMatrixZ.map (fun z ↦ (z : F)) = minorMatrixF := by
  native_decide

theorem minorMatrixZ_det_ne_zero : minorMatrixZ.det ≠ 0 := by
  intro hzero
  apply minorMatrixF_det_ne_zero
  rw [← minorMatrixF_is_integer_reduction, ← Int.cast_det, hzero]
  simp

def minorMatrixR : Matrix (Fin 144) (Fin 144) ℝ :=
  minorMatrixZ.map fun z ↦ (z : ℝ)

theorem minorMatrixR_det_ne_zero : minorMatrixR.det ≠ 0 := by
  unfold minorMatrixR
  rw [← Int.cast_det]
  exact_mod_cast minorMatrixZ_det_ne_zero

/-! The twelve explicit symmetric-generator columns in the scaled seed
coordinates.  The six coordinates of each symmetric matrix are ordered as
`00, 11, 22, 01, 02, 12`. -/

def symmetricBasisEntry (basis row column : Nat) : Int :=
  if basis = 0 ∧ row = 0 ∧ column = 0 then 1
  else if basis = 1 ∧ row = 1 ∧ column = 1 then 1
  else if basis = 2 ∧ row = 2 ∧ column = 2 then 1
  else if basis = 3 ∧ ((row = 0 ∧ column = 1) ∨ (row = 1 ∧ column = 0)) then 1
  else if basis = 4 ∧ ((row = 0 ∧ column = 2) ∨ (row = 2 ∧ column = 0)) then 1
  else if basis = 5 ∧ ((row = 1 ∧ column = 2) ∨ (row = 2 ∧ column = 1)) then 1
  else 0

def symmetricBasisMulVec (basis : Nat) (v : IVec) : IVec :=
  (symmetricBasisEntry basis 0 0 * v.1 +
      symmetricBasisEntry basis 0 1 * v.2.1 + symmetricBasisEntry basis 0 2 * v.2.2,
   symmetricBasisEntry basis 1 0 * v.1 +
      symmetricBasisEntry basis 1 1 * v.2.1 + symmetricBasisEntry basis 1 2 * v.2.2,
   symmetricBasisEntry basis 2 0 * v.1 +
      symmetricBasisEntry basis 2 1 * v.2.1 + symmetricBasisEntry basis 2 2 * v.2.2)

def crossAnticommutatorBasis (basis : Nat) (k v : IVec) : IVec :=
  add (symmetricBasisMulVec basis (cross k v))
    (cross k (symmetricBasisMulVec basis v))

def generatorCoordinateQ (column generator : Nat) : Rat :=
  let mode := column / 12
  let within := column % 12
  let output := within / 4
  let input := (within % 4) / 2
  let part := within % 2
  let k := representatives.getD mode zero
  let f := (frame k).getD input zero
  let denominator := dot f f
  if part = 0 then
    if generator < 6 then
      (componentZ (symmetricBasisMulVec generator f) output : Rat) / denominator
    else 0
  else
    if generator < 6 then 0
    else
      (componentZ (crossAnticommutatorBasis (generator - 6) k f) output : Rat) /
        denominator

def generatorMatrixQ : Matrix (Fin 156) (Fin 12) Rat :=
  fun i j ↦ generatorCoordinateQ i j

def selectedConstraintEntryQ (i j : Nat) : Rat :=
  (((rowsZ.getD (selectedRows.getD i 0) #[]).getD j 0 : Int) : Rat)

def selectedConstraintFullMatrixQ : Matrix (Fin 144) (Fin 156) Rat :=
  fun i j ↦ selectedConstraintEntryQ i j

theorem selected_constraints_annihilate_generators :
    selectedConstraintFullMatrixQ * generatorMatrixQ = 0 := by
  native_decide

abbrev QRow := Array Rat

def generatorRowsQ : List QRow :=
  (List.range 156).map fun i ↦ Array.ofFn fun j : Fin 12 ↦ generatorCoordinateQ i j

def firstPivotQ (row : QRow) : Option Nat :=
  (List.range 12).find? fun j ↦ row[j]! ≠ 0

def addScaledQ (x : Rat) (source target : QRow) : QRow :=
  Array.ofFn fun j : Fin 12 ↦ target[j.val]! - x * source[j.val]!

structure QTrackedPivot where
  pivot : Nat
  source : Nat
  row : QRow

def reduceQ (basis : List QTrackedPivot) (source : QRow) : QRow :=
  basis.foldl (fun row entry ↦
    let x := row[entry.pivot]!
    if x = 0 then row else addScaledQ x entry.row row) source

def insertQ (basis : List QTrackedPivot) (entry : QRow × Nat) : List QTrackedPivot :=
  let row := reduceQ basis entry.1
  match firstPivotQ row with
  | none => basis
  | some pivot =>
      let normalized := row.map (· * (row[pivot]!)⁻¹)
      basis ++ [{ pivot := pivot, source := entry.2, row := normalized }]

def generatorPivotsQ : List QTrackedPivot := generatorRowsQ.zipIdx.foldl insertQ []
def selectedGeneratorRows : List Nat := generatorPivotsQ.map (·.source)
def selectedGeneratorColumns : List Nat := generatorPivotsQ.map (·.pivot)

theorem selectedGenerator_counts :
    selectedGeneratorRows.length = 12 ∧ selectedGeneratorColumns.length = 12 := by
  native_decide

def generatorMinorQ : Matrix (Fin 12) (Fin 12) Rat :=
  fun i j ↦ generatorCoordinateQ (selectedGeneratorRows.getD i 0)
    (selectedGeneratorColumns.getD j 0)

def generatorAugmentedQ : Array QRow :=
  Array.ofFn fun i : Fin 12 ↦ Array.ofFn fun j : Fin 24 ↦
    if j.val < 12 then generatorMinorQ i ⟨j.val % 12, Nat.mod_lt _ (by decide)⟩
    else if j.val - 12 = i.val then 1 else 0

def gaussJordanStepQ (matrix : Array QRow) (i : Nat) : Array QRow :=
  let source := matrix[i]!
  let pivotInv := (source[i]!)⁻¹
  let pivotRow : QRow := Array.ofFn fun j : Fin 24 ↦ pivotInv * source[j.val]!
  Array.ofFn fun rowIndex : Fin 12 ↦
    if rowIndex.val = i then pivotRow
    else
      let factor := (matrix[rowIndex.val]!)[i]!
      Array.ofFn fun j : Fin 24 ↦
        (matrix[rowIndex.val]!)[j.val]! - factor * pivotRow[j.val]!

def generatorReducedQ : Array QRow :=
  (List.range 12).foldl gaussJordanStepQ generatorAugmentedQ

def generatorInverseEntryQ (i j : Nat) : Rat :=
  (generatorReducedQ[i]!).getD (12 + j) 0

def generatorMinorTimesInverseQ (i j : Fin 12) : Rat :=
  ∑ k : Fin 12, generatorMinorQ i k * generatorInverseEntryQ k j

theorem generator_minor_has_right_inverse :
    ∀ i j : Fin 12,
      generatorMinorTimesInverseQ i j = if i = j then 1 else 0 := by
  native_decide

def generatorInverseMatrixQ : Matrix (Fin 12) (Fin 12) Rat :=
  fun i j ↦ generatorInverseEntryQ i j

theorem generatorMinorQ_mul_inverse :
    generatorMinorQ * generatorInverseMatrixQ = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  change generatorMinorTimesInverseQ i j =
    (1 : Matrix (Fin 12) (Fin 12) Rat) i j
  rw [generator_minor_has_right_inverse]
  simp [Matrix.one_apply]

theorem generatorMinorQ_det_ne_zero : generatorMinorQ.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det generatorMinorQ_mul_inverse
  simp [Matrix.det_mul, hzero] at hdet

def generatorMatrixR : Matrix (Fin 156) (Fin 12) ℝ :=
  generatorMatrixQ.map fun x ↦ (x : ℝ)

def generatorMinorR : Matrix (Fin 12) (Fin 12) ℝ :=
  generatorMinorQ.map fun x ↦ (x : ℝ)

theorem generatorMinorR_det_ne_zero : generatorMinorR.det ≠ 0 := by
  unfold generatorMinorR
  rw [← Rat.cast_det]
  exact_mod_cast generatorMinorQ_det_ne_zero

end FourierMultiplierRigidity.SeedCertificate
