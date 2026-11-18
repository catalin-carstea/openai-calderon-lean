/- Adopted from the selected ZIP, lean/Calderon/SmoothMovingFrameFields.lean.
   Generic angular L2 restriction and projection commutation only; proof bodies preserved.
-/
import Proof.Archive.SmoothAmbientAngularCasimir
import Proof.Archive.SmoothSphereRotationProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace OAI.AnisotropicCalderon.SmoothMovingFrameFields
open SphereHarmonic SmoothSphereRotation SmoothAngularCasimir SmoothSphereFields
  SmoothAmbientAngularCasimir SmoothSphereRotationProjection SpectralCoreRegularity

lemma ambientSphereL2_angularRotation (i j : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x =
      smoothSphereLift (sphereRotationDerivative i j (fun z => G (x,z)))
        (contDiff_sphereRotationDerivative i j _ (contDiff_angular_slice G hG x)) := by
  change (ContinuousMap.toLp 2 sphereProbability ℝ) _ =
    (ContinuousMap.toLp 2 sphereProbability ℝ) _
  congr 1
  ext theta
  exact congrFun (ambientAngularRotation_slice i j G hG x) theta.val

lemma sphereHarmonicCoordinate_ambientAngularRotation (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (k : ℕ) (i j : Fin 3) (G : R3 × R3 → ℝ)
    (hG : ContDiff ℝ ∞ G) (x : R3) :
    sphereHarmonicCoordinate hO hD k
      (ambientSphereL2 (ambientAngularRotation i j G) (contDiff_ambientAngularRotation i j G hG) x) =
    harmonicSphereRotation k i j (sphereHarmonicCoordinate hO hD k (ambientSphereL2 G hG x)) := by
  rw [ambientSphereL2_angularRotation i j G hG x,ambientSphereL2_eq_smoothSphereLift G hG x]
  exact sphereHarmonicCoordinate_sphereRotationDerivative hO hD k i j _ (contDiff_angular_slice G hG x)


end OAI.AnisotropicCalderon.SmoothMovingFrameFields
