import Proof.RotatedBoundaryMultiplierDerivative
import Proof.WeakEnergyAngleDerivative
import Proof.OrthogonalAffineCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Every actual compact representative of the rotated scalar first model
    has the same local full weak energy derivative budget. -/
theorem norm_fderiv_rotated_scalar_commonSupport_fullWeakEnergy_le
    (a : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (i j : I) (ell : X →L[ℝ] ℝ)
    (hRep : ∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) =
      ell (coordinateRotation i j θ z) • (1:Mat)) :
    ‖fderiv ℝ (commonSupportFullWeakEnergy a ha) 0‖ ≤ 14*weakFullDerivativeBudget*‖ell‖ := by
  let R : X → Mat := fun z => ell z • (1:Mat)
  have hR : ContDiff ℝ ∞ R := ell.contDiff.smul contDiff_const
  have hRepR (θ : ℝ) (z : X) (hzB : z ∈ Metric.closedBall (0:X) 2) :
      a (θ,z) = coordinateRotationPrincipalFamily i j (fun v : ℝ × X => R v.2) ((θ,0),z) := by
    rw [hRep θ z hzB,coordinateRotationPrincipalFamily_scalar]
  have hGeneratorTheorem := exists_commonSupport_angle_generator a ha S hz
  obtain ⟨b,hb,hzb,hAngle⟩ := hGeneratorTheorem
  have hGerm (z : X) (hzB : z ∈ (ballOpens:Set X)) := commonSupport_rotated_angle_generator_germ a R b i j hAngle
    (fun z _ => hR.differentiable (by simp) z) hRepR z hzB
  have hBound := affineScalar_rotation_generator_C1 i j ell
  have hNorm := norm_fderiv_angle_commonSupport_fullWeakEnergy_le a ha S hS hz b
    (fun z _ => hAngle z) (14*‖ell‖) (by positivity)
    (fun z hzB => by rw [(hGerm z hzB).eq_of_nhds];exact (hBound z hzB).1)
  exact hNorm.trans_eq (by ring)

end ShrinkingSpheres
