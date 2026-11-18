import Proof.NormalFrameRelativeActualParameter
import Proof.NormalFrameRelativeCovariantIdentity
import Proof.NormalizedRelativeAngularCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma normalFrameRelativeActualParameter_curve (d : Data) (y a : X) (t : ℝ) :
    normalFrameRelativeActualParameter d (d.radius y) (y+t • a) =
      normalFrameRelativize (d.radius y) (normalFrameActualCurve d.frame d.radius y a t) := by
  simp [normalFrameRelativeActualParameter,normalFrameRelativize,normalFrameRelativeTangentL,
    normalFrameActualCurve,div_eq_mul_inv,mul_comm]


/-- A genuine actual germ identifies the corrected derivative of the global
    family with the same independent-parameter horizontal derivative. -/
theorem fderiv_actual_germ_covariant_eq_horizontal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y a : X) (H : X → E) (F : NormalFrameRelativeParameter → E)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d (d.radius y) x))
    (hr : DifferentiableAt ℝ d.radius y) (hr0 : d.radius y ≠ 0)
    (hL : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => d.frame x i) y)
    (hframe : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j =
      -frameConnectionCoefficient d.γ d.frame y a j i)
    (hH : DifferentiableAt ℝ H y)
    (hF : DifferentiableAt ℝ F ((y,frameVectorLinear d.frame y),0)) :
    fderiv ℝ H y a-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        deriv (fun t => F (normalFrameRelativize (d.radius y)
          (normalFrameRotationCurve d.frame d.radius y i j t))) 0 =
      fderiv ℝ F ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeHorizontalField d.γ d.radius a ((y,frameVectorLinear d.frame y),0)) := by
  have hLine := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  change HasDerivAt (fun t : ℝ => y+t • a) _ 0 at hLine
  simp only [one_smul,zero_add] at hLine
  have hTo : Tendsto (fun t : ℝ => y+t • a) (𝓝 0) (𝓝 y) := by
    simpa only [zero_smul,add_zero] using hLine.continuousAt.tendsto
  have hEq := hGerm.comp_tendsto hTo
  change (fun t : ℝ => H (y+t • a)) =ᶠ[𝓝 0]
    (fun t => F (normalFrameRelativeActualParameter d (d.radius y) (y+t • a))) at hEq
  simp_rw [normalFrameRelativeActualParameter_curve] at hEq
  have hD : deriv (fun t : ℝ => H (y+t • a)) 0 = fderiv ℝ H y a := by
    have hh : HasFDerivAt H (fderiv ℝ H y) (y+(0:ℝ) • a) := by simpa only [zero_smul,add_zero] using hH.hasFDerivAt
    exact (hh.comp_hasDerivAt 0 hLine).deriv
  have hActual : deriv (fun t => F (normalFrameRelativize (d.radius y)
      (normalFrameActualCurve d.frame d.radius y a t))) 0 = fderiv ℝ H y a :=
    hEq.deriv_eq.symm.trans hD
  rw [← hActual]
  exact deriv_normalFrameRelative_covariant_eq_horizontal d.γ d.frame d.radius y a F hr hr0 hL he hframe hSkew hF

lemma normalFrameRelativeActualRotationCurve (d : Data) (y : X) (i j : I)
    (hr : d.radius y ≠ 0)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (t : ℝ) :
    normalFrameRelativize (d.radius y) (normalFrameRotationCurve d.frame d.radius y i j t) =
      normalFrameRelativeAngularCurve d.γ ((y,frameVectorLinear d.frame y),0) i j t := by
  have hFrame (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using he i j
  unfold normalFrameRelativeAngularCurve
  rw [normalFrameRelativeNormalization_eq_self _ _ hFrame]
  simp [normalFrameRelativize,normalFrameRelativeTangentL,normalFrameRotationCurve,inv_mul_cancel₀ hr]

/-- The same corrected actual derivative, with the canonical angular
    commutators used by the native physical distribution graphs. -/
theorem fderiv_actual_germ_covariant_eq_normalized_horizontal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y a : X) (H : X → E) (F : NormalFrameRelativeParameter → E)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d (d.radius y) x))
    (hr : DifferentiableAt ℝ d.radius y) (hr0 : d.radius y ≠ 0)
    (hL : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (he : ∀ i,DifferentiableAt ℝ (fun x => d.frame x i) y)
    (hframe : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (hSkew : ∀ i j,frameConnectionCoefficient d.γ d.frame y a i j =
      -frameConnectionCoefficient d.γ d.frame y a j i)
    (hH : DifferentiableAt ℝ H y)
    (hF : DifferentiableAt ℝ F ((y,frameVectorLinear d.frame y),0)) :
    fderiv ℝ H y a-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        normalFrameRelativeAngularDerivative d.γ F i j ((y,frameVectorLinear d.frame y),0) =
      fderiv ℝ F ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeHorizontalField d.γ d.radius a ((y,frameVectorLinear d.frame y),0)) := by
  have hFrame (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hframe i j
  have hNorm := normalFrameRelativeNormalization_eq_self d.γ ((y,frameVectorLinear d.frame y),0) hFrame
  have hFD : DifferentiableAt ℝ F (normalFrameRelativeNormalization d.γ ((y,frameVectorLinear d.frame y),0)) := by
    rw [hNorm]
    exact hF
  have hDeriv (i j : I) : deriv (fun t => F (normalFrameRelativize (d.radius y)
      (normalFrameRotationCurve d.frame d.radius y i j t))) 0 =
      normalFrameRelativeAngularDerivative d.γ F i j ((y,frameVectorLinear d.frame y),0) := by
    simp_rw [normalFrameRelativeActualRotationCurve d y i j hr0 hframe]
    exact (normalFrameRelativeAngularDerivative_eq_curve d.γ F i j _ hFD).symm
  simpa only [hDeriv] using fderiv_actual_germ_covariant_eq_horizontal d y a H F hGerm
    hr hr0 hL he hframe hSkew hH hF
end ShrinkingSpheres
