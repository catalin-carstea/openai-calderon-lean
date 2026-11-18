import Proof.ActualCovariantRotationGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
lemma CoarseCovariantRotationGraph.congr_germ {d : Data} {y a : X}
    {F G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {S : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (hF : CoarseCovariantRotationGraph d y a F S) (hFG : F =ᶠ[𝓝 y] G) :
    CoarseCovariantRotationGraph d y a G S := by
  have hP : F y=G y := hFG.eq_of_nhds
  have hD : fderiv ℝ F y=fderiv ℝ G y := hFG.fderiv_eq
  intro u
  have hh := hF u
  simpa only [hP,hD] using hh
lemma CoarseCovariantRotationGraph.sub {d : Data} {y a : X}
    {F G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    {S T : SphereSobolev 1 →L[ℝ] SphereSobolev 0}
    (hF : CoarseCovariantRotationGraph d y a F S) (hG : CoarseCovariantRotationGraph d y a G T)
    (hFD : DifferentiableAt ℝ F y) (hGD : DifferentiableAt ℝ G y) :
    CoarseCovariantRotationGraph d y a (fun x => F x-G x) (S-T) := by
  have hD : fderiv ℝ (fun x => F x-G x) y a=fderiv ℝ F y a-fderiv ℝ G y a := by
    rw [fderiv_fun_sub hFD hGD]
    rfl
  intro u
  have hSub := congrArg₂ (fun x z : SphereSobolev (-1) => x-z) (hF u) (hG u)
  change sphereSobolevInclusionL 0 (-1) (by norm_num)
      ((S-T) (sphereSobolevInclusionL 2 1 (by norm_num) u))= _
  simp only [_root_.sub_apply,map_sub,hD] at hSub ⊢
  simp only [smul_sub,Finset.sum_sub_distrib] at hSub ⊢
  exact hSub.trans (by abel)
end ShrinkingSpheres
