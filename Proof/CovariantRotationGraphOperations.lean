import Proof.CoarseCovariantGraphAlgebra
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma CoarseCovariantRotationGraph.add {d : Data} {y a : X}
    {F G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {S T : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (hF : CoarseCovariantRotationGraph d y a F S) (hG : CoarseCovariantRotationGraph d y a G T)
    (hFD : DifferentiableAt ℝ F y) (hGD : DifferentiableAt ℝ G y) :
    CoarseCovariantRotationGraph d y a (fun x => F x+G x) (S+T) := by
  have hD : fderiv ℝ (fun x => F x+G x) y a=fderiv ℝ F y a+fderiv ℝ G y a := by
    rw [fderiv_fun_add hFD hGD]
    rfl
  intro u
  have hSum := congrArg₂ (fun v w : SphereSobolev (-1:ℝ) => v+w) (hF u) (hG u)
  change sphereSobolevInclusionL 0 (-1) (by norm_num) ((S+T) (sphereSobolevInclusionL 2 1 (by norm_num) u))= _
  simp only [_root_.add_apply,map_add,hD] at hSum ⊢
  simp only [smul_sub,smul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hSum ⊢
  exact hSum.trans (by abel)

lemma CoarseCovariantRotationGraph.smul {d : Data} {y a : X}
    {F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0} {S : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (hF : CoarseCovariantRotationGraph d y a F S) (c : X → ℝ)
    (hCD : DifferentiableAt ℝ c y) (hFD : DifferentiableAt ℝ F y) :
    CoarseCovariantRotationGraph d y a (fun x => c x • F x)
      (c y • S+fderiv ℝ c y a • F y) := by
  have hProduct : HasFDerivAt (fun x => c x • F x)
      (c y • fderiv ℝ F y+(fderiv ℝ c y).smulRight (F y)) y :=
    hCD.hasFDerivAt.smul hFD.hasFDerivAt
  have hD : fderiv ℝ (fun x => c x • F x) y a=
      c y • fderiv ℝ F y a+fderiv ℝ c y a • F y := by
    have hh := DFunLike.congr_fun hProduct.fderiv a
    simpa only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.smulRight_apply] using hh
  intro u
  have hScale := congrArg (fun v : SphereSobolev (-1:ℝ) => c y • v+
    fderiv ℝ c y a • sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num)
      (F y (sphereSobolevInclusionL 2 1 (by norm_num) u))) (hF u)
  change sphereSobolevInclusionL 0 (-1) (by norm_num)
    ((c y • S+fderiv ℝ c y a • F y) (sphereSobolevInclusionL 2 1 (by norm_num) u))= _
  simp only [_root_.add_apply,_root_.smul_apply,map_add,map_smul,hD] at hScale ⊢
  simp only [Fin.sum_univ_three,smul_add,smul_sub,smul_smul] at hScale ⊢
  exact hScale.trans (by module)

lemma CoarseCovariantRotationGraph.sum_three {d : Data} {y a : X}
    (F : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hF : ∀ i,CoarseCovariantRotationGraph d y a (F i) (S i))
    (hD : ∀ i,DifferentiableAt ℝ (F i) y) :
    CoarseCovariantRotationGraph d y a (fun x => ∑ i : I,F i x) (∑ i : I,S i) := by
  simpa only [Fin.sum_univ_three] using
    ((hF 0).add (hF 1) (hD 0) (hD 1)).add (hF 2) ((hD 0).add (hD 1)) (hD 2)
end ShrinkingSpheres
