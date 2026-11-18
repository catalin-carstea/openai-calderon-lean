import Proof.IndexedOperatorRotationPairing
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
lemma hasDerivAt_const_add_comp_const {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → E →L[ℝ] F) (dA : E →L[ℝ] F) (t : ℝ) (hA : HasDerivAt A dA t)
    (C : D →L[ℝ] F) (M : D →L[ℝ] E) :
    HasDerivAt (fun θ => C+(A θ).comp M) (dA.comp M) t := by
  have hComp := hA.clm_comp (hasDerivAt_const t M)
  have hAdd := (hasDerivAt_const t C).add hComp
  have hFun : ((fun _ : ℝ => C)+(fun θ => (A θ).comp M))=(fun θ => C+(A θ).comp M) := by
    funext θ
    rfl
  rw [hFun] at hAdd
  simpa only [ContinuousLinearMap.comp_zero,add_zero,zero_add] using hAdd
end ShrinkingSpheres
