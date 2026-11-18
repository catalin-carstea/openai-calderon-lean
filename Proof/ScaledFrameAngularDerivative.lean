import Proof.RelativeScaledFrameDerivativeAt
import Proof.NormalFrameHorizontalRescaling
import Proof.RelativeAngularNormalizationJets
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rescaling the center variable leaves every pure frame direction intact. -/
lemma fderiv_relativeScaledParameter_frame (F : NormalFrameRelativeParameter → E)
    {β : ℝ} (hβ : β ≠ 0) (y : X) (L A : X →L[ℝ] X) :
    fderiv ℝ (F ∘ normalFrameRelativeScaledParameter β y) ((0,L),0) (((0:X),A),0)=
      fderiv ℝ F ((y,L),0) (((0:X),A),0) := by
  have h := fderiv_relativeScaledParameter_frame_at F hβ y
    (((0,L),0):NormalFrameRelativeParameter) A
  rw [normalFrameRelativeScaledParameter_point] at h
  exact h

/-- A gained joint first-jet bound gives a gained true angular derivative
    bound, with no beta loss from rescaling the center. -/
lemma norm_relativeAngularDerivative_of_scaled_jets (g : MetricField)
    (F : NormalFrameRelativeParameter → E) {β B : ℝ} (hβ : β ≠ 0)
    (y : X) (L : X →L[ℝ] X)
    (he : ∀ k l,metricPair g y (L (axis k)) (L (axis l))=if k=l then 1 else 0)
    (hJ : SmoothFiniteJetBound (F ∘ normalFrameRelativeScaledParameter β y) ((0,L),0) 3 B)
    (i j : I) :
    ‖normalFrameRelativeAngularDerivative g F i j ((y,L),0)‖ ≤ 2*B*‖L‖ := by
  have hFix := normalFrameRelativeNormalization_eq_self g (((y,L),0):NormalFrameRelativeParameter) he
  have hD : ‖fderiv ℝ (F ∘ normalFrameRelativeScaledParameter β y)
      (((0,L),0):NormalFrameRelativeParameter)‖ ≤ B := by
    simpa only [norm_iteratedFDeriv_one] using hJ.bound 1 (by norm_num)
  rw [normalFrameRelativeAngularDerivative,hFix,normalFrameRelativeAngularTangent,hFix,
    ← fderiv_relativeScaledParameter_frame F hβ y L (L.comp (rotationVectorL i j))]
  have hT : ‖(((0:X),L.comp (rotationVectorL i j)),(0:ℝ))‖ ≤ 2*‖L‖ :=
    ((relativeAngularTangentFromFrameL i j).le_opNorm L).trans
      (mul_le_mul_of_nonneg_right (norm_relativeAngularTangentFromFrameL_le_two i j) (norm_nonneg L))
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul hD hT (norm_nonneg _) hJ.nonneg).trans_eq (by ring))
end ShrinkingSpheres
