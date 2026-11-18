import Proof.CommonSupportOneBoundaryDerivative
import Proof.CoarseOneBoundaryAffine
import Proof.BoundaryMatrixMultiplierLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option synthInstance.maxHeartbeats 120000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

abbrev CoarseOneBoundaryBundle :=
  (SphereSobolev 0 →L[ℝ] SphereSobolev 0) × (SphereSobolev 1 →L[ℝ] SphereSobolev 1) ×
    (SphereSobolev 1 →L[ℝ] SphereSobolev 0) × (SphereSobolev 1 →L[ℝ] SphereSobolev 0)

def coarseOneBoundaryBundle (F : SmoothCoefficientMatrix 2) : CoarseOneBoundaryBundle :=
  (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))),
    oneBoundaryCoefficientMulL (normalCoefficientJet F),
    coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j),
    adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j))

def coarseOneBoundaryBundleBudget : ℝ :=
  1+36+73*36+boundaryTangentialCoarseBudget*78+boundaryTangentialAdjointBudget*(73*78)

lemma coarseOneBoundaryBundleBudget_nonneg : 0 ≤ coarseOneBoundaryBundleBudget := by
  have hCG := boundaryTangentialCoarseBudget_nonneg
  have hCA := boundaryTangentialAdjointBudget_nonneg
  unfold coarseOneBoundaryBundleBudget
  positivity

lemma coarseOneBoundaryBundle_sub_smul (F G : SmoothCoefficientMatrix 2) (r : ℝ) :
    coarseOneBoundaryBundle (F-r • G) = coarseOneBoundaryBundle F-r • coarseOneBoundaryBundle G := by
  apply Prod.ext
  · exact coarseNormalCoefficient_sub_smul F G r
  · apply Prod.ext
    · exact oneNormalCoefficient_sub_smul F G r
    · exact Prod.ext (coarseBoundaryTangential_sub_smul F G r) (adjointBoundaryTangential_sub_smul F G r)

theorem norm_coarseOneBoundaryBundle_local_C1 (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDeriv : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    ‖coarseOneBoundaryBundle F‖ ≤ coarseOneBoundaryBundleBudget*q := by
  have hN := normalCoefficientJet_local_C1 F q hq hValue hDeriv
  have hT (j : I) := tangentCoefficientJet_local_C1 F q hq hValue hDeriv j
  have hM0 := norm_coarse_boundary_coefficient_local_C1 (normalCoefficientJet F) (36*q) (by positivity) hN
  have hM1 := norm_oneBoundaryCoefficientMulL_local_C1 (normalCoefficientJet F) (36*q) (by positivity) hN
  have hTC (j : I) := norm_coarse_boundary_coefficient_local_C1 (tangentCoefficientJet F j) (78*q) (by positivity) (hT j)
  have hT1 (j : I) := norm_oneBoundaryCoefficientMulL_local_C1 (tangentCoefficientJet F j) (78*q) (by positivity) (hT j)
  have hTG := norm_coarseBoundaryTangentialL_le (fun j => tangentCoefficientJet F j) (78*q) (by positivity) hTC
  have hTA := norm_adjointBoundaryTangentialL_le (fun j => tangentCoefficientJet F j) ((73*78)*q) (by positivity)
    (fun j => (hT1 j).trans_eq (by ring))
  have hCG := boundaryTangentialCoarseBudget_nonneg
  have hCA := boundaryTangentialAdjointBudget_nonneg
  have hB0 : 36 ≤ coarseOneBoundaryBundleBudget := by unfold coarseOneBoundaryBundleBudget;nlinarith only [hCG,hCA]
  have hB1 : 73*36 ≤ coarseOneBoundaryBundleBudget := by unfold coarseOneBoundaryBundleBudget;nlinarith only [hCG,hCA]
  have hBG : boundaryTangentialCoarseBudget*78 ≤ coarseOneBoundaryBundleBudget := by unfold coarseOneBoundaryBundleBudget;nlinarith only [hCG,hCA]
  have hBA : boundaryTangentialAdjointBudget*(73*78) ≤ coarseOneBoundaryBundleBudget := by unfold coarseOneBoundaryBundleBudget;nlinarith only [hCG,hCA]
  change max _ (max _ (max _ _)) ≤ _
  refine max_le (hM0.trans (mul_le_mul_of_nonneg_right hB0 hq))
    (max_le ?_ (max_le ?_ ?_))
  · exact hM1.trans ((mul_le_mul_of_nonneg_right hB1 hq).trans' (by ring_nf;exact le_rfl))
  · exact hTG.trans ((mul_le_mul_of_nonneg_right hBG hq).trans' (by ring_nf;exact le_rfl))
  · exact hTA.trans ((mul_le_mul_of_nonneg_right hBA hq).trans' (by ring_nf;exact le_rfl))

theorem norm_coarseOneBoundaryBundle_le (F : SmoothCoefficientMatrix 2) :
    ‖coarseOneBoundaryBundle F‖ ≤ coarseOneBoundaryBundleBudget*‖F‖ := by
  have hEntry (i j : I) : ‖F i j‖ ≤ ‖F‖ :=
    (norm_le_pi_norm (F i) j).trans (norm_le_pi_norm F i)
  apply norm_coarseOneBoundaryBundle_local_C1 F ‖F‖ (norm_nonneg _)
  · intro i j x _
    have h := norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 0 (by omega) x
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h.trans (hEntry i j)
  · intro i j x _
    have h := norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 1 (by omega) x
    simpa only [norm_iteratedFDeriv_one] using h.trans (hEntry i j)

def coarseOneBoundaryBundleL : SmoothCoefficientMatrix 2 →L[ℝ] CoarseOneBoundaryBundle :=
  (realLinearMapOfSubSmul coarseOneBoundaryBundle coarseOneBoundaryBundle_sub_smul).mkContinuous
    coarseOneBoundaryBundleBudget norm_coarseOneBoundaryBundle_le

end ShrinkingSpheres
