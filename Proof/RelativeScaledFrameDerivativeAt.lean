import Proof.NormalFrameHorizontalRescaling
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ShrinkingSpheres
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Center rescaling preserves every pure frame direction at every actual
    parameter, including away from the distinguished centered point. -/
lemma fderiv_relativeScaledParameter_frame_at (F : NormalFrameRelativeParameter → E)
    {β : ℝ} (hβ : β ≠ 0) (y : X) (p : NormalFrameRelativeParameter) (A : X →L[ℝ] X) :
    fderiv ℝ (F ∘ normalFrameRelativeScaledParameter β y) p (((0:X),A),0)=
      fderiv ℝ F (normalFrameRelativeScaledParameter β y p) (((0:X),A),0) := by
  have hΦ := normalFrameRelativeScaledParameter_affine β hβ y
  change fderiv ℝ (fun q => F (normalFrameRelativeScaledParameter β y q)) p _=_
  rw [hΦ,fderiv_comp_affine_equiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    normalFrameParameterScaleEquiv_apply,smul_zero]
end ShrinkingSpheres
