import Proof.ThreeRotationVectorAlgebra
import Proof.ThreeRotationSobolevAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

def frameConnectionThreeLinear (g : MetricField) (e : Frame) (y : X) : X →L[ℝ] (I → ℝ) :=
  ContinuousLinearMap.pi (fun k : I => if k=0 then frameConnectionLinear g e y 0 1
    else if k=1 then frameConnectionLinear g e y 0 2 else frameConnectionLinear g e y 1 2)

lemma frameConnectionThreeLinear_apply (g : MetricField) (e : Frame) (y a : X) :
    frameConnectionThreeLinear g e y a=threeSkewCoordinates (frameConnectionCoefficient g e y a) := by
  funext k
  fin_cases k <;>
    simp [frameConnectionThreeLinear,ContinuousLinearMap.pi_apply,threeSkewCoordinates,
      frameConnectionLinear_apply]

lemma Elliptic.contDiffOn_frameConnectionThreeLinear {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g : MetricField} (hg : Elliptic Y K g) (hK : 0 < K)
    (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y) :
    ContDiffOn ℝ ∞ (frameConnectionThreeLinear g e) Y := by
  apply contDiffOn_clm_apply.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro k
  have hΓ (i j : I) := hg.contDiffOn_frameConnection hY hK e he (fun _ => a) contDiffOn_const i j
  fin_cases k
  · simpa [frameConnectionThreeLinear_apply,threeSkewCoordinates] using hΓ 0 1
  · simpa [frameConnectionThreeLinear_apply,threeSkewCoordinates] using hΓ 0 2
  · simpa [frameConnectionThreeLinear_apply,threeSkewCoordinates] using hΓ 1 2

lemma frameConnectionOperator_eq_threeLinear (g : MetricField) (e : Frame) (y : X)
    (hA : ∀ a i j,frameConnectionCoefficient g e y a i j= -frameConnectionCoefficient g e y a j i) :
    frameConnectionOperator g e y=threeRotationVectorMapL.comp (frameConnectionThreeLinear g e y) := by
  apply ContinuousLinearMap.ext
  intro a
  rw [ContinuousLinearMap.comp_apply,threeRotationVectorMapL_apply,frameConnectionThreeLinear_apply]
  exact frameConnectionOperator_eq_three g e y a (hA a)

lemma skew_sum_sobolev_rotation_eq_three (s : ℝ) (A : I → I → ℝ)
    (hA : ∀ i j,A i j= -A j i) :
    (∑ i : I,∑ j : I,((1/2:ℝ)*A i j) • sphereSobolevRotationL s i j)=
      threeRotationL s (threeSkewCoordinates A) := by
  have hD (i : I) : A i i=0 := by linarith only [hA i i]
  simp only [Fin.sum_univ_three,hD,mul_zero,zero_smul,zero_add,add_zero,
    sphereSobolevRotationL_index_self,smul_zero,hA 1 0,hA 2 0,hA 2 1,
    sphereSobolevRotationL_index_swap s 1 0,sphereSobolevRotationL_index_swap s 2 0,
    sphereSobolevRotationL_index_swap s 2 1,threeRotationL,threeSkewCoordinates,
    show (1:I) ≠ 0 by decide,show (2:I) ≠ 0 by decide,show (2:I) ≠ 1 by decide,ite_true,ite_false]
  module

lemma highSectionCovariantDerivative_eq_three (d : Data) (U : X → SphereSobolev 2) (y a : X)
    (hA : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j= -frameConnectionCoefficient d.γ d.frame y a j i) :
    highSectionCovariantDerivative d U y a=
      sphereSobolevInclusionL 2 1 (by norm_num) (fderiv ℝ U y a)-
        threeRotationL 2 (frameConnectionThreeLinear d.γ d.frame y a) (U y) := by
  have h := DFunLike.congr_fun (skew_sum_sobolev_rotation_eq_three 2
    (frameConnectionCoefficient d.γ d.frame y a) hA) (U y)
  simpa only [highSectionCovariantDerivative,frameConnectionThreeLinear_apply,
    _root_.sum_apply,_root_.smul_apply] using congrArg
      (fun v => sphereSobolevInclusionL 2 1 (by norm_num) (fderiv ℝ U y a)-v) h

lemma oneSectionCovariantDerivative_eq_three (d : Data) (U : X → SphereSobolev 1) (y a : X)
    (hA : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j= -frameConnectionCoefficient d.γ d.frame y a j i) :
    oneSectionCovariantDerivative d U y a=
      sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ U y a)-
        threeRotationL 1 (frameConnectionThreeLinear d.γ d.frame y a) (U y) := by
  have h := DFunLike.congr_fun (skew_sum_sobolev_rotation_eq_three 1
    (frameConnectionCoefficient d.γ d.frame y a) hA) (U y)
  simpa only [oneSectionCovariantDerivative,frameConnectionThreeLinear_apply,
    _root_.sum_apply,_root_.smul_apply] using congrArg
      (fun v => sphereSobolevInclusionL 1 0 (by norm_num) (fderiv ℝ U y a)-v) h

lemma threeRotationVectorL_coordinates (p : I → ℝ) :
    threeSkewCoordinates (fun i j => threeRotationVectorL p (axis i) j)=p := by
  funext k
  fin_cases k <;>
    simp [threeSkewCoordinates,threeRotationVectorL,_root_.add_apply,_root_.smul_apply,
      rotationVectorL_apply,rotationVector,axis]

end ShrinkingSpheres
