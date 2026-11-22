module

public import Proof.CalderonPatch.GreenJetPairing
public import Proof.CalderonPatch.KernelJetTransposition

import Proof.CalderonPatch.HomogeneousTests

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Manifold Topology

namespace CalderonPatch

open CalderonN (I X axis coordDeriv chartTest chartVolume chartVolumeMeasure
  InteriorMetricChart IsDirichletGreenKernel parameterSecondOrder)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n

theorem parameterSecondOrder_congr_germ (a : I n → I n → ℝ) (b : I n → ℝ) (c : ℝ)
    {f h : X n → ℝ} {z : X n} (he : f =ᶠ[𝓝 z] h) :
    parameterSecondOrder a b c f z = parameterSecondOrder a b c h z := by
  have h₁ (i : I n) : fderiv ℝ f z (axis i) = fderiv ℝ h z (axis i) := by rw [he.fderiv_eq]
  have h₂ (i j : I n) : fderiv ℝ (fun p => fderiv ℝ f p (axis j)) z (axis i) =
      fderiv ℝ (fun p => fderiv ℝ h p (axis j)) z (axis i) :=
    (chartDerivativeWord_congr_germ [i,j] he).eq_of_nhds
  simp only [parameterSecondOrder,h₁,h₂,he.eq_of_nhds]

private theorem continuous_mul_supported {U : Set (X n)} (hU : IsOpen U)
    {f W : X n → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ U) (hW : ContinuousOn W U) :
    Continuous (fun x => f x * W x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.continuousAt.mul (hW.continuousAt (hU.mem_nhds hx))
  · have hne : x ∉ tsupport f := fun h => hx (hs h)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hne)] with y hy
    change f y = 0 at hy
    rw [hy,zero_mul]

private theorem integral_mul_chartTest {μ : Measure M} {L : (M → ℝ) → M → ℝ}
    (C : InteriorMetricChart J μ L) (f : X n → ℝ) (W : M → ℝ)
    (hWF : AEStronglyMeasurable (fun x => f x * W (C.chart.symm x))
      (chartVolumeMeasure C.chart.target C.metric)) :
    (∫ y, chartTest C.chart f y * W y ∂μ) =
      ∫ x in C.chart.target, (f x * chartVolume C.metric x) * W (C.chart.symm x) := by
  let e := C.chart
  let F := fun x => f x * W (e.symm x)
  have he : AEMeasurable (e : M → X n) (μ.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  calc
    _ = ∫ y in e.source, F (e y) ∂μ := by
      rw [← integral_indicator e.open_source.measurableSet]
      apply integral_congr_ae
      filter_upwards with y
      change e.source.indicator (f ∘ e) y * W y = e.source.indicator (F ∘ e) y
      by_cases hy : y ∈ e.source
      · simp only [indicator_of_mem hy, Function.comp_apply, F, e.left_inv hy]
      · simp only [indicator_of_notMem hy,zero_mul]
    _ = ∫ x, F x ∂chartVolumeMeasure e.target C.metric := by
      rw [← C.volume_eq, integral_map he]
      exact C.volume_eq ▸ hWF
    _ = _ := by
      rw [CalderonN.integral_chartVolume e.open_target C.metric C.smooth_metric F]
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro x _
      change (f x * W (e.symm x)) * chartVolume C.metric x = _
      rw [mul_right_comm]

/-- On a test supported away from the pole, applying the parameter
jet to the Green inverse is pairing with the off-pole differentiated
kernel in the canonical metric volume. -/
theorem greenInverseChart_parameterSecondOrder_off_pole
    {g : SmoothMetric n M} {μ : Measure M} {G : M × M → ℝ}
    {T : Compacts (X n)} (C : InteriorMetricChart J μ (nativeLaplace g))
    (hG : IsDirichletGreenKernel J μ (nativeLaplace g) G)
    (hT : (T : Set (X n)) ⊆ C.chart.target) (h0 : (0 : X n) ∈ C.chart.target)
    (f : 𝓓_{T}(X n, ℝ)) (hf : (0 : X n) ∉ tsupport (f : X n → ℝ))
    (a : I n → I n → ℝ) (b : I n → ℝ) (c : ℝ) :
    parameterSecondOrder a b c (greenInverseChart C G f) 0 =
      ∫ y, chartTest C.chart f y *
        parameterSecondOrder a b c (fun s => G (y,C.chart.symm s)) 0 ∂μ := by
  let S := C.chart.target
  let w := fun x => f x * chartVolume C.metric x
  let q := fun y => parameterSecondOrder a b c (fun s => G (y,C.chart.symm s)) 0
  have hS : tsupport (f : X n → ℝ) ⊆ S := f.tsupport_subset.trans hT
  have hApart : C.chart.symm 0 ∉ C.chart.symm '' tsupport (f : X n → ℝ) := by
    rintro ⟨x,hx,hx0⟩
    have h := C.chart.symm.injOn (hS hx) h0 hx0
    exact hf (h ▸ hx)
  obtain ⟨U,V,hU,hV,hKU,hUS,h0V,hVS,hDis⟩ :=
    exists_green_chart_rectangle C C C.chart.open_target (Subset.rfl (s := S))
      f.compact_supp hS h0 hApart
  have hEq : greenInverseChart C G f =ᶠ[𝓝 0]
      (fun s => ∫ x in S, w x * G (C.chart.symm x,C.chart.symm s)) := by
    filter_upwards [hV.mem_nhds h0V] with s hs
    have hcts : ContinuousOn (fun x => G (C.chart.symm x,C.chart.symm s)) U :=
      (contDiffOn_jointGreen_of_disjoint_charts hG C C hUS hVS hDis).continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn (fun _ hx => ⟨hx,hs⟩)
    have hMeas := (continuous_mul_supported hU f.contDiff.continuous hKU hcts).aestronglyMeasurable
      (μ := chartVolumeMeasure S C.metric)
    rw [greenInverseChart_apply C f (hVS hs)]
    exact (integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)).trans
      (integral_mul_chartTest C f (fun y => G (y,C.chart.symm s)) hMeas)
  have hw : ContDiffOn ℝ ∞ w S := f.contDiff.contDiffOn.mul
    (CalderonN.contDiffOn_metric_volume C.smooth_metric)
  have hw0 (x : X n) (hx : x ∈ S \ tsupport (f : X n → ℝ)) : w x = 0 :=
    mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hx.2) _
  rw [parameterSecondOrder_congr_germ a b c hEq,
    greenParameterSecondOrder_pairing hG C C C.chart.open_target (Subset.rfl (s := S))
      f.compact_supp hS h0 hApart w hw hw0 a b c]
  obtain ⟨C',hC's,hC't,hC'i,hC'm⟩ := restrict_interiorMetricChart C hU hUS
  have h0out : C.chart.symm 0 ∉ C'.chart.source := by
    intro hx
    have hxU : C.chart (C.chart.symm 0) ∈ U :=
      (hC's ▸ hx : C.chart.symm 0 ∈ C.chart.source ∩ C.chart ⁻¹' U).2
    have h := hDis _ hxU 0 h0V
    rw [C.chart.right_inv h0] at h
    exact h rfl
  have hH := harmonic_greenParameterJet_off_pole hG C C' h0 h0out a b c
  rw [hC't,hC'm] at hH
  rw [hC'i] at hH
  have hcts : ContinuousOn (q ∘ C.chart.symm) U := hH.1.continuousOn
  have hMeas := (continuous_mul_supported hU f.contDiff.continuous hKU hcts).aestronglyMeasurable
    (μ := chartVolumeMeasure S C.metric)
  exact (integral_mul_chartTest C f q hMeas).symm

end CalderonPatch
