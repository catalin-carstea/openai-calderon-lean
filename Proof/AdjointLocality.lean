import Proof.TracePairing
import Proof.HorizontalRepresentative
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

instance sphereProbability_openPos : sphereProbability.IsOpenPosMeasure := by
  unfold sphereProbability surfaceMeasure
  exact Measure.isOpenPosMeasure_smul _ (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))

lemma smoothNear.sphere_slice {Y : Set X} {g : MetricField} {φ : Field}
    (hφ : smoothNear φ (bundle Y g)) {y : X} (hy : y ∈ Y) :
    smoothNear (fun w => φ (y,w)) (sphereAt g y) := by
  obtain ⟨V,hV,hb,hφV⟩ := hφ
  refine ⟨(fun w : X => (y,w)) ⁻¹' V,hV.preimage (continuous_const.prodMk continuous_id),
    fun w hw => hb ⟨hy,hw⟩,?_⟩
  exact hφV.comp (contDiffOn_const.prodMk contDiffOn_id) (fun w hw => hw)

lemma smoothNear.realComponent {F : X → ℂ} {S : Set X} (hF : smoothNear F S) (L : ℂ →L[ℝ] ℝ) :
    smoothNear (fun w => L (F w)) S := by
  obtain ⟨V,hV,hSV,hFV⟩ := hF
  exact ⟨V,hV,hSV,L.contDiff.comp_contDiffOn hFV⟩

lemma smoothNear.continuous_frame_slice {g : MetricField} {e : Frame} {y : X} {F : X → ℂ}
    (hF : smoothNear F (sphereAt g y))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    Continuous (fun v : UnitSphere => F (frameVector e y v.val)) := by
  obtain ⟨V,hV,hSV,hFV⟩ := hF
  have hc : Continuous (fun v : UnitSphere => frameVector e y v.val) :=
    (frameVectorLinear e y).continuous.comp continuous_subtype_val
  exact hFV.continuousOn.comp_continuous hc (fun v => hSV (frameVector_mem_sphere g e y hframe v))

/-- Smooth real boundary tests separate complex fields on the physical sphere, for exactly
    the same frame and probability measure as the moving-trace adjoint. -/
theorem sphere_pairing_separates {g : MetricField} {e : Frame} {y : X} {F : X → ℂ}
    (hF : smoothNear F (sphereAt g y))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hpair : ∀ a : X → ℝ,smoothNear a (sphereAt g y) → sphereAverage e y (fun w => F w*(a w : ℂ)) = 0) :
    ∀ w ∈ sphereAt g y,F w = 0 := by
  have hc := hF.continuous_frame_slice hframe
  have hRe := hpair (fun w => (F w).re) (hF.realComponent Complex.reCLM)
  have hIm := hpair (fun w => (F w).im) (hF.realComponent Complex.imCLM)
  have hzero (L : ℂ →L[ℝ] ℝ) (ha : sphereAverage e y (fun w => F w*(L (F w) : ℂ)) = 0) :
      (fun v : UnitSphere => L (F (frameVector e y v.val))) = 0 := by
    have hi : Integrable (fun v : UnitSphere => F (frameVector e y v.val)*(L (F (frameVector e y v.val)) : ℂ)) sphereProbability :=
      (hc.mul (Complex.continuous_ofReal.comp (L.continuous.comp hc))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hsq : (∫ v : UnitSphere,(L (F (frameVector e y v.val)))^2 ∂sphereProbability) = 0 := by
      have hh := congrArg L ha
      change L (∫ v : UnitSphere,F (frameVector e y v.val)*(L (F (frameVector e y v.val)) : ℂ) ∂sphereProbability) = L 0 at hh
      rw [← L.integral_comp_comm hi] at hh
      have hlin (z : ℂ) : L (z*(L z : ℂ)) = (L z)^2 := by
        rw [mul_comm,← Complex.real_smul,map_smul,smul_eq_mul,pow_two]
      simpa only [map_zero,hlin] using hh
    have hisq : Integrable (fun v : UnitSphere => (L (F (frameVector e y v.val)))^2) sphereProbability :=
      ((L.continuous.comp hc).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hzsq := (integral_eq_zero_iff_of_nonneg (fun v => sq_nonneg _) hisq).mp hsq
    have hzae : (fun v : UnitSphere => L (F (frameVector e y v.val))) =ᵐ[sphereProbability] 0 := by
      filter_upwards [hzsq] with v hv
      exact sq_eq_zero_iff.mp hv
    exact Measure.eq_of_ae_eq hzae (L.continuous.comp hc) continuous_const
  have hr := hzero Complex.reCLM hRe
  have hi := hzero Complex.imCLM hIm
  intro w hw
  obtain ⟨v,hv⟩ := exists_unitSphere_frameVector g e y hframe w hw
  apply Complex.ext
  · simpa only [Complex.reCLM_apply,Pi.zero_apply,hv,Complex.zero_re] using congrFun hr v
  · simpa only [Complex.imCLM_apply,Pi.zero_apply,hv,Complex.zero_im] using congrFun hi v


/-- Dirichlet solvability makes the frozen adjoint duality determine a local action on
    boundary data: a zero input on one sphere has zero adjoint output on that sphere. -/
theorem IsMovingTraceAdjoint.zero_on_sphere {Y : Set X} {g g₁ : MetricField} {e : Frame}
    {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A)
    (hD : Dirichlet Y g g₁ expMap r) {φ : Field} (hφ : smoothNear φ (bundle Y g))
    (i : I) {y : X} (hy : y ∈ Y)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hzero : ∀ w ∈ sphereAt g y,φ (y,w) = 0) :
    ∀ w ∈ sphereAt g y,adjointField A i φ (y,w) = 0 := by
  have hAdj := hA i φ hφ
  apply sphere_pairing_separates (hAdj.1.sphere_slice hy) hframe
  intro a ha
  obtain ⟨u,hu,_⟩ := hD y hy a ha
  calc
    sphereAverage e y (fun w => adjointField A i φ (y,w)*(a w : ℂ)) =
        sphereAverage e y (fun w => adjointField A i φ (y,w)*(u (endpoint expMap r (y,w)) : ℂ)) := by
      unfold sphereAverage
      apply integral_congr_ae
      apply Eventually.of_forall
      intro v
      exact congrArg (fun t : ℝ => adjointField A i φ (y,frameVector e y v.val)*(t : ℂ))
        (hu.2 _ (frameVector_mem_sphere g e y hframe v)).symm
    _ = _ := hAdj.2 y hy u hu.1
    _ = 0 := by
      unfold sphereAverage
      apply integral_eq_zero_of_ae
      apply Eventually.of_forall
      intro v
      change φ (y,frameVector e y v.val)*_ = 0
      rw [hzero _ (frameVector_mem_sphere g e y hframe v),zero_mul]

end ShrinkingSpheres
