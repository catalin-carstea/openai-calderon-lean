import Proof.OrderOneBoundaryAffine
import Proof.BoundaryAngularCompatibility

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

/-- The coarse endpoint inherits the already proved native negative-half
    normal coefficient algebra through its injective inclusion. -/
lemma coarseNormalCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) :
    coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (F-c • G)))) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))-
        c • coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet G))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have h := congrArg (fun A : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    A (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u)) (negativeNormalCoefficient_sub_smul F G c)
  simpa only [_root_.sub_apply,_root_.smul_apply,negativeBoundaryCoefficientMulL_coarse,map_sub,map_smul] using h

lemma coarseTangentCoefficient_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) (j : I) :
    coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (tangentCoefficientJet (F-c • G) j))) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (tangentCoefficientJet F j)))-
        c • coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (tangentCoefficientJet G j))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have h := congrArg (fun A : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    A (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) u)) (negativeTangentCoefficient_sub_smul F G c j)
  simpa only [_root_.sub_apply,_root_.smul_apply,negativeBoundaryCoefficientMulL_coarse,map_sub,map_smul] using h

lemma coarseBoundaryTangential_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) :
    coarseBoundaryTangentialL (fun j => tangentCoefficientJet (F-c • G) j) =
      coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)-
        c • coarseBoundaryTangentialL (fun j => tangentCoefficientJet G j) := by
  simp only [coarseBoundaryTangentialL,coarseTangentCoefficient_sub_smul,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,
    Finset.sum_sub_distrib,← Finset.smul_sum]

lemma adjointBoundaryTangential_sub_smul (F G : SmoothCoefficientMatrix 2) (c : ℝ) :
    adjointBoundaryTangentialL (fun j => tangentCoefficientJet (F-c • G) j) =
      adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)-
        c • adjointBoundaryTangentialL (fun j => tangentCoefficientJet G j) := by
  simp only [adjointBoundaryTangentialL,oneTangentCoefficient_sub_smul,
    ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
    neg_sub,Finset.sum_sub_distrib,← Finset.smul_sum,Finset.sum_neg_distrib,smul_neg]
  module

lemma coarseTangentCoefficient_scalar_zero (F : SmoothCoefficientMatrix 2) (q : X → ℝ)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = q w.val • (1:Mat)) (j : I) :
    coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (tangentCoefficientJet F j))) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num)
  have h := negativeBoundaryCoefficientMulL_coarse (tangentCoefficientJet F j) u
  rw [negativeTangentCoefficient_scalar_zero F q hF j] at h
  simpa only [_root_.zero_apply,map_zero] using h.symm

lemma boundaryTangential_scalar_zero (F : SmoothCoefficientMatrix 2) (q : X → ℝ)
    (hF : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = q w.val • (1:Mat)) :
    coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j) = 0 ∧
      adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j) = 0 := by
  constructor
  · simp only [coarseBoundaryTangentialL,coarseTangentCoefficient_scalar_zero F q hF,
      ContinuousLinearMap.zero_comp,Finset.sum_const_zero]
  · simp only [adjointBoundaryTangentialL,oneTangentCoefficient_scalar_zero F q hF,
      ContinuousLinearMap.comp_zero,neg_zero,Finset.sum_const_zero]

end ShrinkingSpheres
