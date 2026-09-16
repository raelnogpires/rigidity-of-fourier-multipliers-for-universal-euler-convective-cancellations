import Mathlib.Analysis.InnerProductSpace.PiL2
import FourierMultiplierRigidity.LocalSpectra
import FourierMultiplierRigidity.SolenoidalSeedCertificate

/-!
# The stability constant of the Hermitian Boolean-seed certificate

`LocalSpectra.exists_stability_constant` discharges the spectral hypothesis of
the finite-certificate stability estimate for an arbitrary observation map on a
finite-dimensional parameter space.  This module instantiates it at the actual
certificate: the typed `26 × 28` Hermitian Boolean-seed evaluation matrix,
viewed as a map of Euclidean parameter space.

The constant produced here depends on that one certificate.  Nothing in this
module claims a bound uniform in the mode count; that remains the open problem
recorded in the manuscript.
-/

namespace FourierMultiplierRigidity.SolenoidalSeedCertificate

open FourierMultiplierRigidity.LocalSpectra

noncomputable section

/-- The Boolean-seed evaluation matrix as a continuous linear map of Euclidean
parameter space. -/
def booleanSeedObservation :
    EuclideanSpace ℝ (Fin 28) →L[ℝ] EuclideanSpace ℝ (Fin 26) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin booleanSeedMatrixR)

/-- **The certificate's stability constant exists.**  The estimate used in the
manuscript holds for the Hermitian Boolean seed with no spectral assumption:
approximate vanishing of its twenty-six evaluations forces the parameter to be
correspondingly close to the two-dimensional energy--helicity kernel. -/
theorem booleanSeed_exists_stability_constant :
    ∃ gamma : ℝ, 0 < gamma ∧
      ∀ x : EuclideanSpace ℝ (Fin 28),
        ‖kernelPerpComponent booleanSeedObservation x‖ ≤
          gamma⁻¹ * ‖booleanSeedObservation x‖ :=
  exists_stability_constant booleanSeedObservation

end

end FourierMultiplierRigidity.SolenoidalSeedCertificate
