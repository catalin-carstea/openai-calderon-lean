import Proof.ScaledNormalFrameHorizontalInputJets
import Proof.RelativeHorizontalVectorFieldJets
import Proof.OrderedDirectionalNaturality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalFrameParameterScaleEquiv (β : ℝ) (hβ : β ≠ 0) :
    NormalFrameRelativeParameter ≃L[ℝ] NormalFrameRelativeParameter :=
  (((LinearEquiv.smulOfNeZero ℝ X β⁻¹ (inv_ne_zero hβ)).toContinuousLinearEquiv).prodCongr
    (ContinuousLinearEquiv.refl ℝ (X →L[ℝ] X))).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

lemma normalFrameParameterScaleEquiv_apply (β : ℝ) (hβ : β ≠ 0) (p : NormalFrameRelativeParameter) :
    normalFrameParameterScaleEquiv β hβ p = ((β⁻¹ • p.1.1,p.1.2),p.2) := rfl

lemma norm_normalFrameParameterScaleEquiv_le_one {β : ℝ} (hβ : 1 ≤ β) :
    ‖(normalFrameParameterScaleEquiv β (zero_lt_one.trans_le hβ).ne').toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change max (max ‖β⁻¹ • p.1.1‖ ‖p.1.2‖) ‖p.2‖ ≤ 1*‖p‖
  rw [one_mul]
  refine max_le (max_le ?_ ((norm_snd_le p.1).trans (norm_fst_le p))) (norm_snd_le p)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hβ))]
  exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hβ) (norm_nonneg _)).trans
    (by simpa only [one_mul] using (norm_fst_le p.1).trans (norm_fst_le p))

def normalFrameRelativeScaledParameter (β : ℝ) (y : X) (p : NormalFrameRelativeParameter) :
    NormalFrameRelativeParameter := ((normalFrameScaledCenter β y p,p.1.2),p.2)

lemma normalFrameRelativeScaledParameter_affine (β : ℝ) (hβ : β ≠ 0) (y : X) :
    normalFrameRelativeScaledParameter β y =
      fun p => ((y,(0:X →L[ℝ] X)),0)+normalFrameParameterScaleEquiv β hβ p := by
  funext p
  rw [normalFrameParameterScaleEquiv_apply]
  change ((y+β⁻¹ • p.1.1,p.1.2),p.2) = _
  simp only [Prod.mk_add_mk,zero_add]

lemma normalFrameRelativeScaledParameter_point (β : ℝ) (y : X) (L : X →L[ℝ] X) :
    normalFrameRelativeScaledParameter β y ((0,L),0) = ((y,L),0) := by
  rw [normalFrameRelativeScaledParameter,normalFrameScaledCenter_point]

def normalFrameRelativeHorizontalField (g : MetricField) (r : X → ℝ) (a : X) :
    NormalFrameRelativeParameter → NormalFrameRelativeParameter :=
  relativeHorizontalFieldOfFamilies (fun p => connectionBilinear g p.1.1)
    (fun p => fderiv ℝ (fun x => Real.log (r x)) p.1.1) a

def normalFrameRelativeScaledHorizontalField (g : MetricField) (r : X → ℝ) (β : ℝ) (y a : X) :
    NormalFrameRelativeParameter → NormalFrameRelativeParameter :=
  relativeHorizontalFieldOfFamilies (normalFrameScaledConnection g β y) (normalFrameScaledLogCovector r β y) a

lemma normalFrameScaledHorizontalField_tangent (g : MetricField) (r : X → ℝ)
    (β : ℝ) (hβ : β ≠ 0) (y a : X) (p : NormalFrameRelativeParameter) :
    normalFrameParameterScaleEquiv β hβ (normalFrameRelativeScaledHorizontalField g r β y a p) =
      β⁻¹ • normalFrameRelativeHorizontalField g r a (normalFrameRelativeScaledParameter β y p) := by
  rw [normalFrameParameterScaleEquiv_apply]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change -((β⁻¹ • connectionBilinear g (normalFrameScaledCenter β y p) a).comp p.1.2) =
        β⁻¹ • (-((connectionBilinear g (normalFrameScaledCenter β y p) a).comp p.1.2))
      rw [ContinuousLinearMap.smul_comp,smul_neg]
  · change (1+p.2)*(β⁻¹ • fderiv ℝ (fun x => Real.log (r x)) (normalFrameScaledCenter β y p) a) =
      β⁻¹ • ((1+p.2)*fderiv ℝ (fun x => Real.log (r x)) (normalFrameScaledCenter β y p) a)
    simp only [smul_eq_mul]
    ring

/-- Repeated rescaled horizontal differentiation is exactly the true
    horizontal differentiation divided by beta once per derivative. -/
theorem ordered_normalFrame_horizontal_rescaling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (r : X → ℝ) (β : ℝ) (hβ : β ≠ 0) (y : X)
    (a : ℕ → X) (F : NormalFrameRelativeParameter → E) (n : ℕ) :
    orderedDirectionalFamily (fun j => normalFrameRelativeScaledHorizontalField g r β y (a j))
      (F ∘ normalFrameRelativeScaledParameter β y) n =
    fun p => (β⁻¹)^n • orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField g r (a j)) F n
      (normalFrameRelativeScaledParameter β y p) := by
  have hPhi := normalFrameRelativeScaledParameter_affine β hβ y
  have hNat := orderedDirectionalFamily_affine_equiv (normalFrameParameterScaleEquiv β hβ)
    (((y,(0:X →L[ℝ] X)),0):NormalFrameRelativeParameter)
    (fun j p => β⁻¹ • normalFrameRelativeHorizontalField g r (a j) p)
    (fun j => normalFrameRelativeScaledHorizontalField g r β y (a j))
    (fun j p => by rw [← congrFun hPhi p];exact normalFrameScaledHorizontalField_tangent g r β hβ y (a j) p) F n
  rw [orderedDirectionalFamily_const_smul_fields] at hNat
  rw [hPhi]
  simpa only [Function.comp_def,Pi.smul_apply] using hNat

end ShrinkingSpheres
