import Proof.CoarseBoundaryTaylorBounds
import Proof.OrderOneNormalInverse
import Proof.RadialCorrectionLinear
import Proof.OperatorPoissonTaylor
import Proof.FlatDegreeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

def radialAdjointPointBudget (P Q CJ : ℝ) : ℝ :=
  4+6*P+CJ+(36+73*36)*Q+37*(P+Q)+2*((73*36)*P+(73*36)*Q)+
    boundaryTangentialCoarseBudget*(78*Q)+boundaryTangentialAdjointBudget*((73*78)*Q)

structure RadialAdjointTaylorPointControl (F F1 : SmoothCoefficientMatrix 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (ell : X →L[ℝ] ℝ) (r C : ℝ) : Prop where
  normal_invertible : (oneBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible
  coarse_normal : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))‖ ≤ C
  first_forward : ‖(radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ C
  first_adjoint : ‖(radialCorrectionCovectorL ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ C
  forward_remainder : ‖D-sphereSobolevDegreeL-r •
    (radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ C*r^2
  coarse_remainder : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))-
    ContinuousLinearMap.id ℝ (SphereSobolev 0)-r •
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))‖ ≤ C*r^2
  one_remainder : ‖oneBoundaryCoefficientMulL (normalCoefficientJet F)-ContinuousLinearMap.id ℝ (SphereSobolev 1)-
    r • oneBoundaryCoefficientMulL (normalCoefficientJet F1)‖ ≤ C*r^2
  coarse_difference : ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))-
    ContinuousLinearMap.id ℝ (SphereSobolev 0)‖ ≤ C*r
  tangent : ‖coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)‖ ≤ C*r^2
  adjoint_tangent : ‖adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)‖ ≤ C*r^2
  inverse : ‖(oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse‖ ≤ C
  inverse_difference : ‖(oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse-
    ContinuousLinearMap.id ℝ (SphereSobolev 1)‖ ≤ C*r

/-- A single uniform point budget for the actual normalized boundary factors
    and a chosen forward response. It is independent of every later direction. -/
theorem radial_adjoint_taylor_point_control_of_local_C1
    (F F0 F1 : SmoothCoefficientMatrix 2) (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (ell : X →L[ℝ] ℝ) (r P Q CJ lam Lam : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hCJ : 0 ≤ CJ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hF1 : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = ell w.val • (1:Mat))
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 F) lam Lam)
    (hV1 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) z| ≤ P)
    (hD1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) z‖ ≤ P)
    (hVR : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j) z| ≤ Q*r^2)
    (hDR : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-(1:ℝ) • F0-r • F1) i j)) z‖ ≤ Q*r^2)
    (hEll : ‖ell‖ ≤ P)
    (hJ : ‖D-sphereSobolevDegreeL-r •
      (radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*r^2)
    (hSmall : ((73*36)*P+(73*36)*Q)*r ≤ (1/2:ℝ)) :
    RadialAdjointTaylorPointControl F F1 D ell r (radialAdjointPointBudget P Q CJ) := by
  let C := radialAdjointPointBudget P Q CJ
  have hCG := boundaryTangentialCoarseBudget_nonneg
  have hCA := boundaryTangentialAdjointBudget_nonneg
  have hCGQ := mul_nonneg hCG hQ
  have hCAQ := mul_nonneg hCA hQ
  have hSizes : 0 ≤ C ∧ 2 ≤ C ∧ 6*P ≤ C ∧ CJ ≤ C ∧ 36*Q ≤ C ∧ (73*36)*Q ≤ C ∧
      36*(P+Q) ≤ C ∧ boundaryTangentialCoarseBudget*(78*Q) ≤ C ∧
      boundaryTangentialAdjointBudget*((73*78)*Q) ≤ C ∧
      2*((73*36)*P+(73*36)*Q) ≤ C ∧ 1+36*(P+Q) ≤ C := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      dsimp [C,radialAdjointPointBudget] <;> nlinarith only [hP,hQ,hCJ,hCGQ,hCAQ]
  obtain ⟨hC,hC2,hCB,hCJR,hCQ0,hCQ1,hCDel,hCT,hCTd,hCID,hCM0⟩ := hSizes
  have hOne := one_boundary_taylor_data_of_local_C1 F F0 F1 1 r 1 P Q lam Lam
    (by norm_num) (by norm_num) (by norm_num) hr hr1 hP hQ (fun z => ell z) hF0 hF1 hUE hV1 hD1 hVR hDR
    (by simpa only [one_mul] using hSmall)
  let M0 := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))
  let M01 := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))
  have hN01 : ‖M01‖ ≤ 36*P := norm_coarse_normal_coefficient_le F1 P hP hV1 hD1
  have hR0 : ‖M0-ContinuousLinearMap.id ℝ (SphereSobolev 0)-r • M01‖ ≤ (36*Q)*r^2 :=
    (norm_coarse_normal_affine_remainder_le F F0 F1 r (Q*r^2) (by positivity) hF0 hVR hDR).trans_eq (by ring)
  have hDel : ‖M0-ContinuousLinearMap.id ℝ (SphereSobolev 0)‖ ≤ 36*(P+Q)*r :=
    (norm_sub_of_affine_remainder_le M0 (ContinuousLinearMap.id ℝ (SphereSobolev 0)) M01 r
      (36*P) (36*Q) hr hr1 (by positivity) (by positivity) hN01 hR0).trans_eq (by ring)
  have hM0 : ‖M0‖ ≤ 1+36*(P+Q) := by
    have hEq : M0 = (M0-ContinuousLinearMap.id ℝ (SphereSobolev 0))+ContinuousLinearMap.id ℝ (SphereSobolev 0) := by abel
    calc
      _ ≤ ‖M0-ContinuousLinearMap.id ℝ (SphereSobolev 0)‖+‖ContinuousLinearMap.id ℝ (SphereSobolev 0)‖ :=
        (congrArg norm hEq).le.trans (norm_add_le _ _)
      _ ≤ 36*(P+Q)*r+1 := add_le_add hDel ContinuousLinearMap.norm_id_le
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hr1 (show 0 ≤ 36*(P+Q) by positivity)]
  let B := radialCorrectionCovectorL ell
  have hB : ‖B‖ ≤ 6*P := (norm_radialCorrectionCovectorL_apply_le ell).trans (by gcongr)
  have hFirst : ‖B.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ 6*P :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hB (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
  have hFirstA : ‖B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ 6*P :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul ((ContinuousLinearMap.adjoint.norm_map B).le.trans hB)
        (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
  have hT := norm_coarse_tangent_affine_remainder_le F F0 F1 r (Q*r^2) (by positivity)
    (fun z => ell z) hF0 hF1 hVR hDR
  have hTd := norm_adjointBoundaryTangentialL_le (fun j => tangentCoefficientJet F j)
    (((73*78)*Q)*r^2) (by positivity) hOne.tangent_bound
  refine ⟨hOne.normal_invertible,hM0.trans hCM0,hFirst.trans hCB,hFirstA.trans hCB,
    hJ.trans (by gcongr),hR0.trans (by gcongr),?_,hDel.trans (by gcongr),?_,?_,?_,?_⟩
  · simpa only [one_smul] using hOne.normal_remainder_bound.trans (mul_le_mul_of_nonneg_right hCQ1 (sq_nonneg r))
  · have hT0 : ‖coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)‖ ≤
        (boundaryTangentialCoarseBudget*(78*Q))*r^2 := hT.trans_eq (by ring)
    exact hT0.trans (mul_le_mul_of_nonneg_right hCT (sq_nonneg r))
  · have hTd0 : ‖adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)‖ ≤
        (boundaryTangentialAdjointBudget*((73*78)*Q))*r^2 := hTd.trans_eq (by ring)
    exact hTd0.trans (mul_le_mul_of_nonneg_right hCTd (sq_nonneg r))
  · have hI : ‖(oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse‖ ≤ 2 := by
      simpa only [mul_one] using hOne.normal_inverse_bound
    exact hI.trans hC2
  · have h := hOne.inverse_difference_bound
    simp only [inv_one,one_smul,one_mul,mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hCID hr)

end ShrinkingSpheres
