import Proof.BoundaryTaylorIdentity
import Proof.CommonSupportLowRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies

/-- The actual compact coefficient families share exactly the same normal
    Taylor residual and tangential family, irrespective of exterior cutoffs. -/
theorem commonSupport_boundary_taylor_family_identity
    (a a1 aR : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haR : ContDiff ℝ ∞ aR)
    (S S1 SR : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSR : IsCompact SR)
    (hz : ∀ θ z,z ∉ S → a (θ,z) = 0) (hz1 : ∀ θ z,z ∉ S1 → a1 (θ,z) = 0)
    (hzR : ∀ θ z,z ∉ SR → aR (θ,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (c r : ℝ) (s : ℝ → X → ℝ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hScalar : ∀ (θ : ℝ) (w : UnitSphere),a1 (θ,w.val) = s θ w.val • (1:Mat))
    (hAffine : ∀ θ z,z ∈ Metric.closedBall (0:X) 2 → a (θ,z) = c • (1:Mat)+r • a1 (θ,z)+aR (θ,z)) :
    (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz θ)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 θ)) =
        (fun θ => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily aR haR SR hSR hzR θ)) ∧
      ∀ j : I,(fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j θ)) =
        (fun θ => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily aR haR SR hSR hzR j θ)) := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let FR := commonSupportMatrixFamily 2 aR haR SR hSR hzR
  have hPoint (θ : ℝ) := negative_boundary_taylor_identity_of_sphere (F θ) F0 (F1 θ) (FR θ) c r (s θ) hF0
    (fun w => by
      change coefficientMatrixField 2 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 θ) w.val = _
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact hScalar θ w)
    (fun w => by
      change coefficientMatrixField 2 (commonSupportMatrixFamily 2 aR haR SR hSR hzR θ) w.val =
        coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz θ) w.val-c • (1:Mat)-
        r • coefficientMatrixField 2 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 θ) w.val
      rw [coefficientMatrixField_commonSupportMatrixFamily,coefficientMatrixField_commonSupportMatrixFamily,
        coefficientMatrixField_commonSupportMatrixFamily]
      change aR (θ,w.val) = a (θ,w.val)-c • (1:Mat)-r • a1 (θ,w.val)
      rw [hAffine θ w.val (Metric.closedBall_subset_closedBall (by norm_num)
        (Metric.sphere_subset_closedBall w.property))]
      module)
  constructor
  · funext θ
    rw [commonSupport_negative_normal_multiplier_eq,commonSupport_negative_normal_multiplier_eq,
      commonSupport_negative_normal_multiplier_eq]
    exact (hPoint θ).1
  · intro j
    funext θ
    rw [commonSupport_negative_tangent_multiplier_eq,commonSupport_negative_tangent_multiplier_eq]
    exact (hPoint θ).2 j

end ShrinkingSpheres
