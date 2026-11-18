import Proof.FirstConormalDegreeRealization
import Proof.OrderOneBoundaryAffine

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem norm_coarse_coefficient_of_local_C1 (F : SmoothCoefficientJets 2) (q : ℝ) (hq : 0 ≤ q)
    (h : LocalC1Bound (coefficientValue 2 F) q) :
    ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData F))‖ ≤ q := by
  apply (norm_coarseSphereScalarMulL_le _).trans
  apply (ContinuousMap.norm_le _ hq).mpr
  intro w
  exact (h.on_unitSphere (contDiff_coefficientValue 2 F) w).1

theorem norm_firstConormalOneL_le (F1 : SmoothCoefficientMatrix 2) (c K P CB : ℝ)
    (ell : X →L[ℝ] ℝ) (hc : 0 ≤ c) (hcK : c ≤ K) (hP : 0 ≤ P) (hCB : 0 ≤ CB)
    (hB : ‖coarseFirstRadialVariationL c ell‖ ≤ CB)
    (hV1 : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) x| ≤ P)
    (hD1 : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) :
    ‖firstConormalOneL F1 c ell‖ ≤ K*CB+72*P := by
  have hM : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))‖ ≤ 36*P :=
    norm_coarse_coefficient_of_local_C1 (normalCoefficientJet F1) (36*P) (by positivity)
      (normalCoefficientJet_local_C1 F1 P hP hV1 hD1)
  have hFirst : ‖c • (coarseFirstRadialVariationL c ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ K*CB := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hB (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (norm_nonneg _) hCB)) hc).trans
        ((show c*(CB*1) ≤ K*CB by rw [mul_one];exact mul_le_mul_of_nonneg_right hcK hCB))
  have hSecond : ‖(coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))).comp sphereSobolevDegreeL‖ ≤ 72*P :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul hM norm_sphereSobolevDegreeL_le_two
      (norm_nonneg _) (by positivity)).trans_eq (by ring))
  exact (norm_add_le _ _).trans (add_le_add hFirst hSecond)

end ShrinkingSpheres
