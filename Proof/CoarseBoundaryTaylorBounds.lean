import Proof.CoarseBoundaryCoefficientNorm
import Proof.CoarseOneBoundaryAffine
import Proof.CommonSupportOneBoundaryDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarseNormalCoefficient_flat (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F0))) =
      ContinuousLinearMap.id ℝ (SphereSobolev 0) := by
  have h := coarseSphereScalarMulL_const
    (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F0))) 1 (by
      intro w
      exact (congrFun (coefficientValue_normalCoefficientJet F0) w.val).trans
        (boundaryNormalCoefficient_flat_sphere F0 hF0 w))
  simpa only [one_smul] using h

theorem norm_coarse_normal_coefficient_le (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) z| ≤ q)
    (hDerivative : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) z‖ ≤ q) :
    ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))‖ ≤ 36*q :=
  norm_coarse_boundary_coefficient_local_C1 _ (36*q) (by positivity)
    (normalCoefficientJet_local_C1 F q hq hValue hDerivative)

theorem norm_coarse_normal_affine_remainder_le (F F0 F1 : SmoothCoefficientMatrix 2)
    (r q : ℝ) (hq : 0 ≤ q)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hValue : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j) z| ≤ q)
    (hDerivative : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j)) z‖ ≤ q) :
    ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))-
      ContinuousLinearMap.id ℝ (SphereSobolev 0)-r •
        coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))‖ ≤ 36*q := by
  have h := norm_coarse_normal_coefficient_le (F-(1:ℝ) • F0-r • F1) q hq hValue hDerivative
  rw [coarseNormalCoefficient_sub_smul,coarseNormalCoefficient_sub_smul,coarseNormalCoefficient_flat F0 hF0,one_smul] at h
  exact h

theorem norm_coarse_tangent_affine_remainder_le (F F0 F1 : SmoothCoefficientMatrix 2)
    (r q : ℝ) (hq : 0 ≤ q) (s : X → ℝ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = s w.val • (1:Mat))
    (hValue : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j) z| ≤ q)
    (hDerivative : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j)) z‖ ≤ q) :
    ‖coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)‖ ≤ boundaryTangentialCoarseBudget*(78*q) := by
  let FR := F-(1:ℝ) • F0-r • F1
  have hEach (j : I) : ‖coarseSphereScalarMulL (smoothSphereValue
      (coefficientSmoothData (tangentCoefficientJet FR j)))‖ ≤ 78*q :=
    norm_coarse_boundary_coefficient_local_C1 _ (78*q) (by positivity)
      (tangentCoefficientJet_local_C1 FR q hq hValue hDerivative j)
  have hR := norm_coarseBoundaryTangentialL_le (fun j => tangentCoefficientJet FR j) (78*q) (by positivity) hEach
  have hFlat := (boundaryTangential_scalar_zero F0 (fun _ => 1) (by
    intro w
    simpa only [one_smul] using hF0 w.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property)))).1
  have hFirst := (boundaryTangential_scalar_zero F1 s hF1).1
  change ‖coarseBoundaryTangentialL (fun j => tangentCoefficientJet (F-(1:ℝ) • F0-r • F1) j)‖ ≤ _ at hR
  rw [coarseBoundaryTangential_sub_smul,coarseBoundaryTangential_sub_smul,hFlat,hFirst,
    smul_zero,smul_zero,sub_zero,sub_zero] at hR
  exact hR

end ShrinkingSpheres
