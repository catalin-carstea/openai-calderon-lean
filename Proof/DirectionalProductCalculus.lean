import Proof.LocalFlowVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma second_fderiv_mul_apply (f g : P → ℝ) (p a b : P)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    fderiv ℝ (fderiv ℝ (fun q => f q*g q)) p b a =
      fderiv ℝ (fderiv ℝ f) p b a*g p+fderiv ℝ f p a*fderiv ℝ g p b+
      fderiv ℝ f p b*fderiv ℝ g p a+f p*fderiv ℝ (fderiv ℝ g) p b a := by
  have hDf := (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have hDg := (hg.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
  have hFA := hDf.clm_apply (hasFDerivAt_const a p)
  have hGA := hDg.clm_apply (hasFDerivAt_const a p)
  have hNearF := (hf.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hNearG := (hg.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hEq : (fun q => fderiv ℝ (fun z => f z*g z) q a) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ f q a*g q+f q*fderiv ℝ g q a) := by
    filter_upwards [hNearF,hNearG] with q hfq hgq
    have hb := congrArg (fun L : P →L[ℝ] ℝ => L a)
      ((hfq.differentiableAt (by simp)).hasFDerivAt.mul (hgq.differentiableAt (by simp)).hasFDerivAt).fderiv
    change fderiv ℝ (fun z => f z*g z) q a = _ at hb
    exact hb.trans (by simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul];ring)
  have hProduct := (hFA.mul (hg.differentiableAt (by simp)).hasFDerivAt).add
    ((hf.differentiableAt (by simp)).hasFDerivAt.mul hGA)
  change HasFDerivAt (fun q => fderiv ℝ f q a*g q+f q*fderiv ℝ g q a) _ p at hProduct
  rw [← fderiv_apply_const_of_contDiffAt (fun q => f q*g q) p a b (hf.mul hg),hEq.fderiv_eq,hProduct.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,zero_apply,map_zero,zero_add]
  ring

end ShrinkingSpheres
