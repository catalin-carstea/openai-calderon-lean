import Proof.BoundaryAffineRemainder
import Proof.RadialConormalReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual affine boundary Taylor residual depends only on the residual
    matrix on the sphere; the scalar first model has no tangent contribution. -/
theorem negative_boundary_taylor_identity_of_sphere
    (F F0 F1 FR : SmoothCoefficientMatrix 2) (c r : ℝ) (s : X → ℝ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = s w.val • (1:Mat))
    (hFR : ∀ w : UnitSphere,coefficientMatrixField 2 FR w.val =
      coefficientMatrixField 2 F w.val-c • (1:Mat)-r • coefficientMatrixField 2 F1 w.val) :
    negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
      c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJet F1) =
        negativeBoundaryCoefficientMulL (normalCoefficientJet FR) ∧
      ∀ j : I,negativeBoundaryCoefficientMulL (tangentCoefficientJet F j) =
        negativeBoundaryCoefficientMulL (tangentCoefficientJet FR j) := by
  have hField (w : UnitSphere) : coefficientMatrixField 2 (F-c • F0-r • F1) w.val =
      coefficientMatrixField 2 FR w.val := by
    rw [hFR w]
    have h0 := hF0 w.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property))
    ext k l
    have h0kl := congrArg (fun A : Mat => A k l) h0
    change coefficientValue 2 ((F-c • F0-r • F1) k l) w.val = _
    simp only [Pi.sub_apply,Pi.smul_apply,coefficientValue_sub_local,coefficientValue_smul,
      Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    change coefficientValue 2 (F k l) w.val-c*coefficientValue 2 (F0 k l) w.val-
      r*coefficientValue 2 (F1 k l) w.val = _
    change coefficientValue 2 (F0 k l) w.val = (1:Mat) k l at h0kl
    rw [h0kl]
    rfl
  have hN : negativeBoundaryCoefficientMulL (normalCoefficientJet (F-c • F0-r • F1)) =
      negativeBoundaryCoefficientMulL (normalCoefficientJet FR) :=
    negativeBoundaryCoefficientMulL_congr_sphere _ _
      (normalCoefficientJet_value_congr_sphere _ _ hField)
  have hNAlg : negativeBoundaryCoefficientMulL (normalCoefficientJet (F-c • F0-r • F1)) =
      negativeBoundaryCoefficientMulL (normalCoefficientJet F)-
        c • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
        r • negativeBoundaryCoefficientMulL (normalCoefficientJet F1) := by
    rw [negativeNormalCoefficient_sub_smul,negative_normal_coefficient_decomposition F F0 c hF0]
    abel
  refine ⟨hNAlg.symm.trans hN,?_⟩
  intro j
  have hT : negativeBoundaryCoefficientMulL (tangentCoefficientJet (F-c • F0-r • F1) j) =
      negativeBoundaryCoefficientMulL (tangentCoefficientJet FR j) :=
    negativeBoundaryCoefficientMulL_congr_sphere _ _
      (tangentCoefficientJet_value_congr_sphere _ _ hField j)
  rw [negativeTangentCoefficient_sub_smul,negativeTangentCoefficient_scalar_zero F1 s hF1 j,
    smul_zero,sub_zero,← negative_tangent_coefficient_decomposition F F0 c hF0 j] at hT
  exact hT

end ShrinkingSpheres
