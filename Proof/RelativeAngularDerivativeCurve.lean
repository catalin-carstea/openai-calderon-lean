import Proof.NormalizedRelativeAngularCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
namespace ShrinkingSpheres
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma hasDerivAt_relativeAngularFamily (g : MetricField) (F : NormalFrameRelativeParameter → E)
    (p : NormalFrameRelativeParameter) (i j : I)
    (hF : DifferentiableAt ℝ F (normalFrameRelativeNormalization g p)) :
    HasDerivAt (fun θ => F (normalFrameRelativeAngularCurve g p i j θ))
      (normalFrameRelativeAngularDerivative g F i j p) 0 := by
  have hF0 : HasFDerivAt F (fderiv ℝ F (normalFrameRelativeNormalization g p))
      (normalFrameRelativeAngularCurve g p i j 0) := by
    rw [normalFrameRelativeAngularCurve_zero]
    exact hF.hasFDerivAt
  have hD := hF0.comp_hasDerivAt 0 (hasDerivAt_normalFrameRelativeAngularCurve g p i j)
  simpa only [Function.comp_def,normalFrameRelativeAngularDerivative] using hD
end ShrinkingSpheres
