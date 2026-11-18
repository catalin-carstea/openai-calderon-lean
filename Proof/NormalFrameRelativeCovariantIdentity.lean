import Proof.NormalFrameHorizontalRescaling

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalFrameRelativeTangentL (r : ℝ) : NormalFrameParameter →L[ℝ] NormalFrameRelativeParameter :=
  ((ContinuousLinearMap.fst ℝ X (ℝ × (X →L[ℝ] X))).prod
    ((ContinuousLinearMap.snd ℝ ℝ (X →L[ℝ] X)).comp
      (ContinuousLinearMap.snd ℝ X (ℝ × (X →L[ℝ] X))))).prod
    (r⁻¹ • (ContinuousLinearMap.fst ℝ ℝ (X →L[ℝ] X)).comp
      (ContinuousLinearMap.snd ℝ X (ℝ × (X →L[ℝ] X))))

def normalFrameRelativize (r : ℝ) (p : NormalFrameParameter) : NormalFrameRelativeParameter :=
  normalFrameRelativeTangentL r p-((0,(0:X →L[ℝ] X)),1)

lemma normalFrameRelativize_point (r : ℝ) (hr : r ≠ 0) (y : X) (L : X →L[ℝ] X) :
    normalFrameRelativize r (y,(r,L)) = ((y,L),0) := by
  change ((y,L),r⁻¹*r)-((0,(0:X →L[ℝ] X)),1) = _
  simp only [inv_mul_cancel₀ hr,Prod.mk_sub_mk,sub_zero,sub_self]

private lemma deriv_curve_of_parameter_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : NormalFrameParameter → E) (J : NormalFrameParameter →L[ℝ] E)
    (p : NormalFrameParameter) (hH : HasFDerivAt H J p)
    (c : ℝ → NormalFrameParameter) (v : NormalFrameParameter)
    (hc : HasDerivAt c v 0) (h0 : c 0 = p) : deriv (H ∘ c) 0 = J v := by
  have hh : HasFDerivAt H J (c 0) := by rw [h0];exact hH
  exact (hh.comp_hasDerivAt 0 hc).deriv

/-- The relative horizontal derivative is exactly the actual moving-radius
    derivative with the frame-connection rotation removed. This identifies
    the connection used by the repeated horizontal estimates. -/
theorem deriv_normalFrameRelative_covariant_eq_horizontal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (e : Frame) (r : X → ℝ) (y a : X)
    (F : NormalFrameRelativeParameter → E)
    (hr : DifferentiableAt ℝ r y) (hr0 : r y ≠ 0)
    (hL : DifferentiableAt ℝ (frameVectorLinear e) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => e x i) y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient g e y a i j = -frameConnectionCoefficient g e y a j i)
    (hF : DifferentiableAt ℝ F ((y,frameVectorLinear e y),0)) :
    deriv (fun t => F (normalFrameRelativize (r y) (normalFrameActualCurve e r y a t))) 0-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient g e y a i j) •
        deriv (fun t => F (normalFrameRelativize (r y) (normalFrameRotationCurve e r y i j t))) 0 =
      fderiv ℝ F ((y,frameVectorLinear e y),0)
        (normalFrameRelativeHorizontalField g r a ((y,frameVectorLinear e y),0)) := by
  let p : NormalFrameParameter := (y,(r y,frameVectorLinear e y))
  let q : NormalFrameRelativeParameter := ((y,frameVectorLinear e y),0)
  let T := normalFrameRelativeTangentL (r y)
  let H := F ∘ normalFrameRelativize (r y)
  have hRel : HasFDerivAt (normalFrameRelativize (r y)) T p := T.hasFDerivAt.sub_const _
  have hFAt : HasFDerivAt F (fderiv ℝ F q) (normalFrameRelativize (r y) p) := by
    rw [normalFrameRelativize_point _ hr0]
    exact hF.hasFDerivAt
  have hHD : HasFDerivAt H ((fderiv ℝ F q).comp T) p := hFAt.comp p hRel
  have hSplit := deriv_normalFrame_family_covariant_split g e r y a H hr hr0 hL he hframe hSkew hHD.differentiableAt
  have hP := deriv_curve_of_parameter_derivative H _ p hHD (normalFrameParallelCurve g e r y a) _
    (hasDerivAt_normalFrameParallelCurve g e r y a) (normalFrameParallelCurve_zero g e r y a)
  have hR := deriv_curve_of_parameter_derivative H _ p hHD (normalFrameRadiusCurve e r y) _
    (hasDerivAt_normalFrameRadiusCurve e r y) (normalFrameRadiusCurve_zero e r y)
  change deriv (H ∘ normalFrameParallelCurve g e r y a) 0 = _ at hP
  change deriv (H ∘ normalFrameRadiusCurve e r y) 0 = _ at hR
  change deriv (H ∘ normalFrameActualCurve e r y a) 0-
    ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient g e y a i j) • deriv (H ∘ normalFrameRotationCurve e r y i j) 0 = _
  simp only [Function.comp_def] at hP hR ⊢
  rw [hSplit,hP,hR]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← map_smul,← map_add]
  congr 1
  change ((a,-((connectionBilinear g y a).comp (frameVectorLinear e y))),(r y)⁻¹*(0:ℝ))+
    (fderiv ℝ (fun x => Real.log (r x)) y a) • (((0:X),(0:X →L[ℝ] X)),(r y)⁻¹*r y) = _
  rw [mul_zero,inv_mul_cancel₀ hr0]
  simp only [Prod.smul_mk,smul_zero,smul_eq_mul,mul_one,Prod.mk_add_mk,add_zero,zero_add]
  change ((a,-((connectionBilinear g y a).comp (frameVectorLinear e y))),
      fderiv ℝ (fun x => Real.log (r x)) y a) =
    ((a,-((connectionBilinear g y a).comp (frameVectorLinear e y))),
      (1+(0:ℝ))*fderiv ℝ (fun x => Real.log (r x)) y a)
  simp only [add_zero,one_mul]

end ShrinkingSpheres
