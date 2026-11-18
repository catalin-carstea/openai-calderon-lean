import Proof.ThreeRotationVectorAlgebra
import Proof.ThreeRotationSobolevAction
import Proof.GradedCovariantSectionComm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def threeConnectionCurvature (C : X → X →L[ℝ] (I → ℝ)) (y a b : X) : I → ℝ :=
  fderiv ℝ C y a b-fderiv ℝ C y b a-threeRotationBracket (C y a) (C y b)

def threeVectorConnection (C : X → X →L[ℝ] (I → ℝ)) (x : X) : X →L[ℝ] X →L[ℝ] X :=
  threeRotationVectorMapL.comp (C x)

lemma fderiv_clm_apply_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : X → X →L[ℝ] E) (y a b : X) (hC : DifferentiableAt ℝ C y) :
    fderiv ℝ (fun x => C x b) y a=fderiv ℝ C y a b := by
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    _root_.zero_apply,map_zero,zero_add] using
    DFunLike.congr_fun (hC.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).fderiv a

lemma fderiv_threeVectorConnection (C : X → X →L[ℝ] (I → ℝ)) (y a : X)
    (hC : DifferentiableAt ℝ C y) :
    fderiv ℝ (threeVectorConnection C) y a=threeRotationVectorMapL.comp (fderiv ℝ C y a) := by
  have hh := (hasFDerivAt_const threeRotationVectorMapL y).clm_comp hC.hasFDerivAt
  change HasFDerivAt (threeVectorConnection C) _ y at hh
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,_root_.zero_apply,ContinuousLinearMap.zero_comp,add_zero]
    using DFunLike.congr_fun hh.fderiv a

/-- Curvature of the actual finite vector representation, including the
opposite sign between its Lie bracket and the action on scalar functions. -/
theorem threeVectorConnection_curvature (C : X → X →L[ℝ] (I → ℝ)) (y a b : X)
    (hC : DifferentiableAt ℝ C y) :
    curvatureLinear (threeVectorConnection C) y a b=
      threeRotationVectorL (threeConnectionCurvature C y a b) := by
  calc
    _ = threeRotationVectorL (fderiv ℝ C y a b)-threeRotationVectorL (fderiv ℝ C y b a)+
        ((threeRotationVectorL (C y a)).comp (threeRotationVectorL (C y b))-
          (threeRotationVectorL (C y b)).comp (threeRotationVectorL (C y a))) := by
      simp only [curvatureLinear,fderiv_threeVectorConnection C y a hC,
        fderiv_threeVectorConnection C y b hC,threeVectorConnection,
        ContinuousLinearMap.comp_apply,threeRotationVectorMapL_apply]
      abel
    _ = _ := by
      rw [threeRotationVectorL_commutator]
      simp only [threeConnectionCurvature,← threeRotationVectorMapL_apply,map_sub]
      abel

/-- The genuine H2-to-H0 covariant commutator is a first-order angular
curvature action restricted by the actual H2-to-H1 inclusion. -/
theorem threeRotationSection_covariant_commutator
    (C : X → X →L[ℝ] (I → ℝ)) (U : X → SphereSobolev 2) (y a b : X)
    (hC : DifferentiableAt ℝ C y) (hU : ContDiffAt ℝ ∞ U y) :
    gradedSectionCovariantDerivative (sphereSobolevInclusionL 1 0 (by norm_num))
        (fun x v => threeRotationL 1 (C x v))
        (fun x => gradedSectionCovariantDerivative (sphereSobolevInclusionL 2 1 (by norm_num))
          (fun z v => threeRotationL 2 (C z v)) U x b) y a-
      gradedSectionCovariantDerivative (sphereSobolevInclusionL 1 0 (by norm_num))
        (fun x v => threeRotationL 1 (C x v))
        (fun x => gradedSectionCovariantDerivative (sphereSobolevInclusionL 2 1 (by norm_num))
          (fun z v => threeRotationL 2 (C z v)) U x a) y b=
    -threeRotationL 1 (threeConnectionCurvature C y a b)
      (sphereSobolevInclusionL 2 1 (by norm_num) (U y)) := by
  have hCv (v : X) := hC.clm_apply (differentiableAt_const v)
  have hB (v : X) : DifferentiableAt ℝ (fun x => threeRotationL 2 (C x v)) y := by
    simpa only [Function.comp_def,threeRotationMapL_apply] using
      (threeRotationMapL 2).differentiableAt.comp y (hCv v)
  have hD (v w : X) : fderiv ℝ (fun x => threeRotationL 2 (C x v)) y w=
      threeRotationL 2 (fderiv ℝ C y w v) := by
    rw [fderiv_threeRotationL 2 _ y w (hCv v),fderiv_clm_apply_fixed C y w v hC]
  have hJ (p : I → ℝ) (u : SphereSobolev 2) :
      sphereSobolevInclusionL 1 0 (by norm_num) (threeRotationL 2 p u)=
        threeRotationL 1 p (sphereSobolevInclusionL 2 1 (by norm_num) u) :=
    DFunLike.congr_fun (threeRotationL_one_inclusion_two p) u
  have hLie : threeRotationL 1 (C y a) (threeRotationL 2 (C y b) (U y))-
      threeRotationL 1 (C y b) (threeRotationL 2 (C y a) (U y))=
        threeRotationL 1 (threeRotationBracket (C y a) (C y b))
          (sphereSobolevInclusionL 2 1 (by norm_num) (U y)) := by
    have h0 := DFunLike.congr_fun (threeRotationL_lie_commutator 2 (C y a) (C y b)) (U y)
    have hR (p : I → ℝ) : threeRotationL ((2:ℝ)-1) p=threeRotationL 1 p := by congr 1 <;> norm_num
    have hI : sphereSobolevInclusionL 2 ((2:ℝ)-1) (by norm_num)=
        sphereSobolevInclusionL 2 1 (by norm_num) := by congr 1 <;> norm_num
    simpa only [ContinuousLinearMap.comp_apply,_root_.sub_apply,hR,hI] using h0
  have h := gradedSectionCovariantDerivative_commutator
    (sphereSobolevInclusionL 2 1 (by norm_num)) (sphereSobolevInclusionL 1 0 (by norm_num))
    (fun x v => threeRotationL 1 (C x v)) (fun x v => threeRotationL 2 (C x v)) U y a b hU
    (hB a) (hB b) (threeRotationL_one_inclusion_two (C y a)) (threeRotationL_one_inclusion_two (C y b))
  rw [h,hD b a,hD a b,map_sub,hJ,hJ]
  calc
    _ = -threeRotationL 1 (fderiv ℝ C y a b) (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
        threeRotationL 1 (fderiv ℝ C y b a) (sphereSobolevInclusionL 2 1 (by norm_num) (U y))+
        threeRotationL 1 (threeRotationBracket (C y a) (C y b))
          (sphereSobolevInclusionL 2 1 (by norm_num) (U y)) := by rw [← hLie];abel
    _ = _ := by
      simp only [threeConnectionCurvature,← threeRotationMapL_apply,map_sub,_root_.sub_apply]
      abel

end ShrinkingSpheres
