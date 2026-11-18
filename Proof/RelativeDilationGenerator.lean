import Proof.AffineMatrixRemainderJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def relativeDilationGenerator (f : X → E) (z : X) : E := fderiv ℝ f z z

lemma hasDerivAt_relative_dilation (f : X → E) (z : X) (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun t : ℝ => f ((1+t) • z)) (relativeDilationGenerator f z) 0 := by
  have hInput := ((hasDerivAt_const (0:ℝ) (1:ℝ)).add (hasDerivAt_id (0:ℝ))).smul_const z
  change HasDerivAt (fun t : ℝ => (1+t) • z) _ 0 at hInput
  have hArg : HasDerivAt (fun t : ℝ => (1+t) • z) z 0 := by
    simpa only [zero_add,one_smul] using hInput
  have hAt : DifferentiableAt ℝ f (((1:ℝ)+0) • z) := by simpa using hf
  simpa only [Function.comp_def,relativeDilationGenerator,zero_add,add_zero,one_smul] using
    hAt.hasFDerivAt.comp_hasDerivAt (0:ℝ) hArg

lemma fderiv_relativeDilationGenerator_apply (f : X → E) (z v : X)
    (hf : ContDiffAt ℝ ∞ f z) :
    fderiv ℝ (relativeDilationGenerator f) z v =
      fderiv ℝ (fderiv ℝ f) z v z+fderiv ℝ f z v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)
  have h := congrArg (fun T : X →L[ℝ] E => T v)
    (hD.hasFDerivAt.clm_apply (hasFDerivAt_id z)).fderiv
  change fderiv ℝ (fun w => fderiv ℝ f w w) z v = _
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply,id_eq,add_comm] using h

lemma norm_relativeDilationGenerator_le (f : X → E) (z : X) (q : ℝ)
    (hD : ‖fderiv ℝ f z‖ ≤ q) : ‖relativeDilationGenerator f z‖ ≤ q*‖z‖ :=
  ((fderiv ℝ f z).le_opNorm z).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg z))

lemma norm_fderiv_relativeDilationGenerator_le (f : X → E) (z : X)
    (hf : ContDiffAt ℝ ∞ f z) (q1 q2 : ℝ) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hD : ‖fderiv ℝ f z‖ ≤ q1) (hD2 : ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ q2) :
    ‖fderiv ℝ (relativeDilationGenerator f) z‖ ≤ q2*‖z‖+q1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [fderiv_relativeDilationGenerator_apply f z v hf]
  have hSecond : ‖fderiv ℝ (fderiv ℝ f) z v z‖ ≤ q2*‖v‖*‖z‖ :=
    (((fderiv ℝ (fderiv ℝ f) z) v).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) z).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hD2 (norm_nonneg v))) (norm_nonneg z))
  exact ((norm_add_le _ _).trans (add_le_add hSecond
    (((fderiv ℝ f z).le_opNorm v).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg v))))).trans_eq (by ring)

end ShrinkingSpheres
