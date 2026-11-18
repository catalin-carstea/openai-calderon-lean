import Proof.GradedSphereSectionCovariantDerivative
import Proof.GradedLoweringRotation
import Proof.SkewRotationCoefficientContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma linear_covariant_sum_three {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J R : E →L[ℝ] F) (u du : I → E) :
    J (∑ i : I,du i)-R (∑ i : I,u i)=∑ i : I,(J (du i)-R (u i)) := by
  simp only [map_sum,Finset.sum_sub_distrib]

private lemma linear_covariant_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (J R : E →L[ℝ] F) (u du : E) (c dc : ℝ) :
    J (c • du+dc • u)-R (c • u)=dc • J u+c • (J du-R u) := by
  simp only [map_add,map_smul,smul_sub]
  module

lemma gradedSphereSectionCovariantDerivative_sum_three (s : ℝ) (d : Data)
    (U : I → X → SphereSobolev s) (y a : X) (hU : ∀ i,DifferentiableAt ℝ (U i) y) :
    gradedSphereSectionCovariantDerivative s d (fun x => ∑ i : I,U i x) y a=
      ∑ i : I,gradedSphereSectionCovariantDerivative s d (U i) y a := by
  let J := sphereSobolevInclusionL s (s-1) (by linarith)
  let R : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
    ∑ p : I,∑ q : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a p q) • sphereSobolevRotationL s p q
  have hD : fderiv ℝ (fun x => ∑ i : I,U i x) y a=∑ i : I,fderiv ℝ (U i) y a := by
    rw [fderiv_fun_sum (fun i _ => hU i)]
    rfl
  change J (fderiv ℝ (fun x => ∑ i : I,U i x) y a)-R (∑ i : I,U i y)=
    ∑ i : I,(J (fderiv ℝ (U i) y a)-R (U i y))
  rw [hD]
  exact linear_covariant_sum_three J R _ _

lemma flatLoweringSobolevL_connection_commutator (s : ℝ) (d : Data) (y a : X)
    (hSkew : ∀ p q,frameConnectionCoefficient d.γ d.frame y a p q=
      -frameConnectionCoefficient d.γ d.frame y a q p) (i : I) (u : SphereSobolev s) :
    (∑ p : I,∑ q : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a p q) •
      (sphereSobolevRotationL (s-1) p q (flatLoweringSobolevL s i u)-
        flatLoweringSobolevL (s-1) i (sphereSobolevRotationL s p q u)))=
      -sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)
        (∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • flatLoweringSobolevL s k u) := by
  let G := frameConnectionCoefficient d.γ d.frame y a
  have hGSkew (p q : I) : G p q= -G q p := hSkew p q
  let V := fun k => flatLoweringSobolevL s k u
  let c : I → ℝ := fun k => if k=i then 1 else 0
  have hCond (p q : I) (T : SphereSobolev (s-1)) : (if p=q then T else 0)=(if q=p then T else 0) := by
    by_cases h : p=q
    · rw [ite_eq_left h,ite_eq_left h.symm]
    · rw [ite_eq_right h,ite_eq_right (Ne.symm h)]
  have hBasis (p q : I) : (if i=q then V p else 0)-(if i=p then V q else 0)=c q • V p-c p • V q := by
    simp only [c,ite_smul,one_smul,zero_smul]
    exact congrArg₂ (fun x z : SphereSobolev (s-1) => x-z) (hCond i q _) (hCond i p _)
  have hCoeff (p : I) : (∑ q : I,G p q*c q)=G p i := by
    simp only [c,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hCon : (∑ p : I,∑ q : I,((1/2:ℝ)*G p q) •
      ((if i=q then V p else 0)-(if i=p then V q else 0)))= -(∑ k : I,G i k • V k) := by
    simp only [hBasis]
    rw [skew_rotation_coefficient_contraction G hSkew c V]
    simp only [hCoeff]
    calc
      _ = ∑ k : I,-(G i k • V k) := Finset.sum_congr rfl (fun k _ => by rw [hGSkew k i,neg_smul])
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hComm (p q : I) : sphereSobolevRotationL (s-1) p q (flatLoweringSobolevL s i u)-
      flatLoweringSobolevL (s-1) i (sphereSobolevRotationL s p q u)=
      sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)
        ((if i=q then V p else 0)-(if i=p then V q else 0)) := by
    simpa only [ContinuousLinearMap.comp_apply,_root_.sub_apply,clm_ite_zero_apply] using
      DFunLike.congr_fun (flatLoweringSobolevL_rotation_commutator s p q i) u
  calc
    _ = ∑ p : I,∑ q : I,((1/2:ℝ)*G p q) •
        sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)
          ((if i=q then V p else 0)-(if i=p then V q else 0)) := by simp only [hComm];rfl
    _ = sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)
        (∑ p : I,∑ q : I,((1/2:ℝ)*G p q) • ((if i=q then V p else 0)-(if i=p then V q else 0))) := by
      simp only [map_sum,map_smul]
    _ = _ := (congrArg (sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)) hCon).trans (map_neg _ _)

/-- Genuine covariant Leibniz rule for lowering on every Sobolev level.
Only its tensor-index connection remains after the angular cancellation. -/
lemma gradedSphereSectionCovariantDerivative_flatLowering (s : ℝ) (d : Data)
    (U : X → SphereSobolev s) (y a : X) (hU : DifferentiableAt ℝ U y)
    (hSkew : ∀ p q,frameConnectionCoefficient d.γ d.frame y a p q=
      -frameConnectionCoefficient d.γ d.frame y a q p) (i : I) :
    gradedSphereSectionCovariantDerivative (s-1) d (fun x => flatLoweringSobolevL s i (U x)) y a=
      flatLoweringSobolevL (s-1) i (gradedSphereSectionCovariantDerivative s d U y a)+
      sphereSobolevInclusionL (s-1) ((s-1)-1) (by linarith)
        (∑ k : I,frameConnectionCoefficient d.γ d.frame y a i k • flatLoweringSobolevL s k (U y)) := by
  have hD : fderiv ℝ (fun x => flatLoweringSobolevL s i (U x)) y a=
      flatLoweringSobolevL s i (fderiv ℝ U y a) := by
    simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using DFunLike.congr_fun
      ((flatLoweringSobolevL s i).hasFDerivAt.comp y hU.hasFDerivAt).fderiv a
  have hCompat := DFunLike.congr_fun (flatLoweringSobolevL_inclusion s (s-1) (by linarith) i) (fderiv ℝ U y a)
  simp only [ContinuousLinearMap.comp_apply] at hCompat
  have hConn := flatLoweringSobolevL_connection_commutator s d y a hSkew i (U y)
  simp only [smul_sub,Finset.sum_sub_distrib] at hConn
  unfold gradedSphereSectionCovariantDerivative
  rw [hD,←hCompat]
  simp only [map_sub,map_sum,map_smul]
  rw [sub_eq_iff_eq_add.mp hConn]
  simp only [map_sum,map_smul]
  abel

lemma gradedSphereSectionCovariantDerivative_smul (s : ℝ) (d : Data)
    (c : X → ℝ) (U : X → SphereSobolev s) (y a : X)
    (hc : DifferentiableAt ℝ c y) (hU : DifferentiableAt ℝ U y) :
    gradedSphereSectionCovariantDerivative s d (fun x => c x • U x) y a=
      fderiv ℝ c y a • sphereSobolevInclusionL s (s-1) (by linarith) (U y)+
        c y • gradedSphereSectionCovariantDerivative s d U y a := by
  have hD : fderiv ℝ (fun x => c x • U x) y a=
      c y • fderiv ℝ U y a+fderiv ℝ c y a • U y := by
    have hh := DFunLike.congr_fun (hc.hasFDerivAt.smul hU.hasFDerivAt).fderiv a
    change fderiv ℝ (fun x => c x • U x) y a=_ at hh
    simpa only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.smulRight_apply] using
      hh
  let J := sphereSobolevInclusionL s (s-1) (by linarith)
  let R : SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
    ∑ p : I,∑ q : I,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a p q) • sphereSobolevRotationL s p q
  change J (fderiv ℝ (fun x => c x • U x) y a)-R (c y • U y)=
    fderiv ℝ c y a • J (U y)+c y • (J (fderiv ℝ U y a)-R (U y))
  rw [hD]
  exact linear_covariant_smul J R _ _ _ _

end ShrinkingSpheres
