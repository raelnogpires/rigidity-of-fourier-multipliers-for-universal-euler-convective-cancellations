import FourierMultiplierRigidity.CorollaryC

/-!
# Corollary E: the actual operator and its longitudinal defect

This module proves the matrix-symbol bridge, rather than taking it as a
comment attached to a definition. The completed operator is the Corollary C
multiplier `strainGenerator 0 B_H`. On transverse input it equals
`B_H(-Δ) + curl B_H curl`; its explicit symbol is `(kᵀHk)v - (Hk·v)k`.
It has strain–vorticity cancellation, not Euler convective cancellation.

The defect is invisible to transverse vector pairings. The convective
recipient `(ω·∇)ω` need not be transverse: the defect cannot be discarded
from the strain–vorticity functional. No regularity estimate is asserted.
-/

namespace FourierMultiplierRigidity.StrainVorticity
open scoped ComplexConjugate
noncomputable section

def bHMatrix (H : RMatrix) : RMatrix :=
  (Matrix.trace H / 2) • (1 : RMatrix) - H

def bHForward (B : RMatrix) : RMatrix :=
  Matrix.trace B • (1 : RMatrix) - B

theorem bHMatrix_symm (H : RMatrix) (hH : H.transpose = H) :
    (bHMatrix H).transpose = bHMatrix H := by
  simp [bHMatrix, Matrix.transpose_sub, Matrix.transpose_smul, hH]

theorem bHMatrix_left_inverse (H : RMatrix) : bHForward (bHMatrix H) = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bHForward, bHMatrix, Matrix.trace, Fin.sum_univ_three,
      Matrix.one_apply, smul_eq_mul] <;> ring

theorem bHMatrix_right_inverse (B : RMatrix) : bHMatrix (bHForward B) = B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bHForward, bHMatrix, Matrix.trace, Fin.sum_univ_three,
      Matrix.one_apply, smul_eq_mul] <;> ring

def lHSymbol (H : RMatrix) (k : LatticeVec) : CVec →ₗ[ℂ] CVec :=
  Vec3.dot (latticeToComplex k)
    (Matrix.mulVec (complexifyMatrix H) (latticeToComplex k)) • LinearMap.id

def tBHSymbol (H : RMatrix) (k : LatticeVec) : CVec →ₗ[ℂ] CVec where
  toFun v := Vec3.dot (latticeToComplex k)
      (Matrix.mulVec (complexifyMatrix H) (latticeToComplex k)) • v -
    Vec3.dot (Matrix.mulVec (complexifyMatrix H) (latticeToComplex k)) v •
      latticeToComplex k
  map_add' u v := by
    simp only [Vec3.dot_add_right, smul_add, add_smul]
    abel
  map_smul' c v := by
    simp only [Vec3.dot_smul_right, smul_sub, smul_smul, RingHom.id_apply]
    congr 1 <;> congr 1 <;> ring

/-- The actual second-order completion supplied by Corollary C. -/
def anisotropicOperator (H : RMatrix) : MultiplierSymbol :=
  strainGenerator 0 (bHMatrix H)

/-- Crucial operator bridge. Holds on the entire fiber, including its
longitudinal direction (both sides annihilate k). Symmetry is essential. -/
theorem anisotropicOperator_eq_symbol (H : RMatrix) (hH : H.transpose = H)
    (k : LatticeVec) (v : CVec) :
    (anisotropicOperator H).map k v = tBHSymbol H k v := by
  have h01 : H 1 0 = H 0 1 := congrFun (congrFun hH 0) 1
  have h02 : H 2 0 = H 0 2 := congrFun (congrFun hH 0) 2
  have h12 : H 2 1 = H 1 2 := congrFun (congrFun hH 1) 2
  change generatorMap 0 (bHMatrix H) k (curlSymbol k v) = _
  rw [generatorMap_apply]
  funext i
  fin_cases i <;>
    simp [tBHSymbol, bHMatrix, curlSymbol, Vec3.cross, Vec3.dot,
      complexifyMatrix, Matrix.mulVec, dotProduct, Matrix.trace,
      Fin.sum_univ_three, Matrix.one_apply, smul_eq_mul,
      h01, h02, h12, Complex.I_mul_I] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- Identifies the operator with B(-Δ)+curl B curl on divergence-free input. -/
theorem anisotropicOperator_differential (H : RMatrix) (k : LatticeVec)
    (v : CVec) (hv : Transverse k v) :
    (anisotropicOperator H).map k v =
      freqSq k • Matrix.mulVec (complexifyMatrix (bHMatrix H)) v +
      curlSymbol k (Matrix.mulVec (complexifyMatrix (bHMatrix H)) (curlSymbol k v)) := by
  simpa [anisotropicOperator, strainGenerator] using
    strainGenerator_expansion 0 (bHMatrix H) k v hv

/-- Actual strain–vorticity cancellation for the second-order operator. -/
theorem anisotropicOperator_cancellation (H : RMatrix) (hH : H.transpose = H) :
    UniversalSVCancellation (anisotropicOperator H) :=
  strainGenerator_cancellation 0 (bHMatrix H) Matrix.transpose_zero (bHMatrix_symm H hH)

/-- Exact longitudinal difference for the actual operator. -/
theorem anisotropicLongitudinalCompletion (H : RMatrix) (hH : H.transpose = H)
    (k : LatticeVec) (v : CVec) :
    (anisotropicOperator H).map k v - lHSymbol H k v =
      -Vec3.dot (Matrix.mulVec (complexifyMatrix H) (latticeToComplex k)) v •
        latticeToComplex k := by
  rw [anisotropicOperator_eq_symbol H hH]
  funext i
  simp [tBHSymbol, lHSymbol, smul_eq_mul] <;> ring

/-- Projection equality expressed against an arbitrary transverse vector.
This does not assert that the nonlinear recipient is transverse. -/
theorem anisotropic_transverse_pairing (H : RMatrix) (hH : H.transpose = H)
    (k : LatticeVec) (v w : CVec) (hw : Transverse k w) :
    Vec3.dot ((anisotropicOperator H).map k v) w = Vec3.dot (lHSymbol H k v) w := by
  apply sub_eq_zero.mp
  rw [← Vec3.dot_sub_left, anisotropicLongitudinalCompletion H hH,
    Vec3.dot_smul_left, hw, mul_zero]

theorem millerReduction (c : ℝ) (k : LatticeVec) (v : CVec) (hv : Transverse k v) :
    (anisotropicOperator (c • (1 : RMatrix))).map k v =
      lHSymbol (c • (1 : RMatrix)) k v := by
  apply sub_eq_zero.mp
  rw [anisotropicLongitudinalCompletion _ (scalar_matrix_symm c)]
  have hc : Matrix.mulVec (complexifyMatrix (c • (1 : RMatrix))) (latticeToComplex k) =
      (c : ℂ) • latticeToComplex k := by
    ext i
    simp [complexifyMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply,
      Fin.sum_univ_three, smul_eq_mul]
    fin_cases i <;> simp
  rw [hc, Vec3.dot_smul_left, hv, mul_zero, neg_zero, zero_smul]

end
end FourierMultiplierRigidity.StrainVorticity
