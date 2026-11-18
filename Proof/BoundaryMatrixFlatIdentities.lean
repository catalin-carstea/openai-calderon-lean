import Proof.BoundaryMatrixMultiplierLinear
import Proof.BoundaryNormalPerturbation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma boundaryMatrixMultiplier_none_flat_eq_id (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    boundaryMatrixMultiplier none F0 = ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ))) := by
  have h := negative_normal_coefficient_decomposition F0 F0 1 hF0
  have hz : boundaryMatrixMultiplier none (0:SmoothCoefficientMatrix 2) = 0 :=
    (boundaryMatrixMultiplierL none).map_zero
  simp only [one_smul,sub_self] at h
  change boundaryMatrixMultiplier none F0 =
    ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))+boundaryMatrixMultiplier none 0 at h
  exact h.trans (by rw [hz,add_zero])

lemma boundaryMatrixMultiplier_some_flat_eq_zero (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) (j : I) :
    boundaryMatrixMultiplier (some j) F0 = 0 := by
  have h := negative_tangent_coefficient_decomposition F0 F0 1 hF0 j
  have hz : boundaryMatrixMultiplier (some j) (0:SmoothCoefficientMatrix 2) = 0 :=
    (boundaryMatrixMultiplierL (some j)).map_zero
  simp only [one_smul,sub_self] at h
  exact h.trans hz

end ShrinkingSpheres
