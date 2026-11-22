module

public import Proof.CalderonN.SphereFrameInvariant
public import Proof.CalderonN.FixedKernelIntegral

import Proof.CalderonN.ParallelTransportODE
import Proof.CalderonN.ParallelFrameCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Adapted from `SphereIntegralCalculus` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1800000

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Differentiation of a fixed probability-sphere integral uses the same
compact-carrier theorem as the local Green pairing. -/
theorem hasFDerivAt_sphereIntegral {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [ProperSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (X dim)} {V : Set P} (hU : IsOpen U) (hV : IsOpen V) (hSU : (standardSphere dim) ⊆ U)
    {f : (X dim) → P → E} (hf : ContDiffOn ℝ 1 (Function.uncurry f) (U ×ˢ V))
    {z : P} (hz : z ∈ V) :
    HasFDerivAt (fun t => ∫ w : ↥(standardSphere dim), f w t ∂(sphereProbability dim))
      (∫ w : ↥(standardSphere dim), fderiv ℝ (f w) z ∂(sphereProbability dim)) z := by
  let μ : Measure (X dim) := Measure.map Subtype.val (sphereProbability dim)
  have hS : IsClosed (standardSphere dim) := isClosed_sphere
  have hEmb : MeasurableEmbedding ((↑) : ↥(standardSphere dim) → (X dim)) := MeasurableEmbedding.subtype_coe hS.measurableSet
  let : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [show μ univ = (sphereProbability dim) (Subtype.val ⁻¹' (univ : Set (X dim))) from
      Measure.map_apply hEmb.measurable MeasurableSet.univ]
    simp
  have hμ : μ (standardSphere dim)ᶜ = 0 := by
    rw [show μ (standardSphere dim)ᶜ = (sphereProbability dim) (Subtype.val ⁻¹' (standardSphere dim)ᶜ) from
      Measure.map_apply hEmb.measurable hS.isOpen_compl.measurableSet]
    have hpre : Subtype.val ⁻¹' (standardSphere dim)ᶜ = (∅ : Set ↥(standardSphere dim)) := by
      ext w
      simp
    rw [hpre,measure_empty]
  have h := hasFDerivAt_integral_on_compact (isCompact_sphere _ _) hSU hU hV hμ hf le_rfl hz
  have hfun : (fun t => ∫ w : (X dim), f w t ∂μ) =
      fun t => ∫ w : ↥(standardSphere dim), f w t ∂(sphereProbability dim) :=
    funext (fun t => hEmb.integral_map _)
  rw [hfun,hEmb.integral_map] at h
  exact h

/-- Differentiate the moving sphere average by choosing a frame parallel
along the base line. (Frame dim) invariance identifies it with the frozen average. -/
theorem hasDerivAt_sphereAverage_along_line
    {Y : Set (X dim)} (hY : IsOpen Y) {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {f : (Field dim)} (hf : smoothNear f (bundle Y γ)) {y : (X dim)} (hy : y ∈ Y) (a : (X dim)) :
    HasDerivAt (fun t : ℝ => sphereAverage e (y+t • a) (fun w => f (y+t • a,w)))
      (sphereAverage e y (fun w => horizontal γ f y w a)) 0 := by
  let q (t : ℝ) := y+t • a
  have hq : ContDiff ℝ ∞ q := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hq₀ : q 0 = y := by simp [q]
  have hdq (t : ℝ) : HasDerivAt q a t := by
    simpa only [q,id_eq,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
      ((((hasDerivAt_id t).smul_const a).hasFDerivAt.const_add y : HasFDerivAt _ _ t).hasDerivAt)
  obtain ⟨F,hF,hF₀,hPar⟩ := exists_parallelFrame hγ hq (e y)
  let wAt (w : (X dim)) (t : ℝ) := ∑ i, w i • F t i
  let J (p : (X dim) × ℝ) := (q p.2,wAt p.1 p.2)
  have hJ : ContDiff ℝ ∞ J := by
    refine (hq.comp contDiff_snd).prodMk (ContDiff.sum (fun i _ => ?_))
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_fst).smul ((hF i).comp contDiff_snd)
  have hW₀ (w : (X dim)) : wAt w 0 = frameVector e y w := by
    simp only [wAt,frameVector,hF₀]
  obtain ⟨S,hS,hSub,hfS⟩ := hf
  have hJnear : (standardSphere dim) ×ˢ ({(0 : ℝ)} : Set ℝ) ⊆ J ⁻¹' S := by
    rintro ⟨w,t⟩ ⟨hw,ht⟩
    obtain rfl : t = 0 := mem_singleton_iff.mp ht
    change (q 0,wAt w 0) ∈ S
    rw [hq₀,hW₀]
    exact hSub ⟨hy,frameVector_mem_sphere γ e y (he y hy) ⟨w,hw⟩⟩
  obtain ⟨U,V,hU,hV,hSU,h₀V,hUV⟩ := generalized_tube_lemma (isCompact_sphere (0 : (X dim)) 1)
    isCompact_singleton (hS.preimage hJ.continuous) hJnear
  let b (w : (X dim)) (t : ℝ) := f (q t,wAt w t)
  have hb : ContDiffOn ℝ 1 (Function.uncurry b) (U ×ˢ V) :=
    (hfS.comp hJ.contDiffOn hUV).of_le (by simp)
  have hInt := (hasFDerivAt_sphereIntegral hU hV hSU hb (h₀V (mem_singleton 0))).hasDerivAt
  have hP := hPar 0 (left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
  have hW (w : (X dim)) : HasDerivAt (wAt w) (-connection γ y a (frameVector e y w)) 0 := by
    have hvel : deriv q 0 = a := (hdq 0).deriv
    have hF' i : HasDerivAt (fun s => F s i) (-connection γ y a (F 0 i)) 0 := by
      simpa only [hq₀,hvel] using hP.self_of_nhds.1 i
    have h := hasDerivAt_parallelFrame_sum γ y a F (fun _ => w)
      (hasDerivAt_const (0 : ℝ) w) hF'
    simpa only [wAt,hW₀,PiLp.zero_apply,zero_smul,Finset.sum_const_zero,zero_sub] using h
  have hDer (w : ↥(standardSphere dim)) : deriv (b w) (0 : ℝ) = horizontal γ f y (frameVector e y w) a := by
    have hPair : HasDerivAt (fun t => (q t,wAt w t)) (a,-connection γ y a (frameVector e y w)) 0 := by
      convert ((hdq 0).hasFDerivAt.prodMk (hW w).hasFDerivAt).hasDerivAt using 1
      simp
    have hm : (q 0,wAt w 0) ∈ S := hJnear (show ((w : (X dim)),(0 : ℝ)) ∈ _ from ⟨w.property,mem_singleton 0⟩)
    have hdf := ((hfS.contDiffAt (hS.mem_nhds hm)).differentiableAt (by simp)).hasFDerivAt
    have hd := (hdf.comp_hasDerivAt 0 hPair).deriv
    simpa only [b,Function.comp_def,horizontal,hq₀,hW₀] using hd
  have hOp : Integrable (fun w : ↥(standardSphere dim) => fderiv ℝ (b w) (0 : ℝ)) (sphereProbability dim) := by
    let : CompactSpace ↥(standardSphere dim) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
    have hc := continuousOn_slice
      (contDiffOn_partial hb (n := 0) (by simp) hU hV).continuousOn hSU (h₀V (mem_singleton 0))
    have hCont : Continuous (fun w : ↥(standardSphere dim) => fderiv ℝ (b w) (0 : ℝ)) :=
      hc.comp_continuous continuous_subtype_val (fun w => w.property)
    exact hCont.integrable_of_hasCompactSupport (μ := (sphereProbability dim))
      (HasCompactSupport.of_compactSpace _)
  have hOut : HasDerivAt (fun t => ∫ w : ↥(standardSphere dim), b w t ∂(sphereProbability dim))
      (sphereAverage e y (fun w => horizontal γ f y w a)) 0 := by
    have heq : (∫ w : ↥(standardSphere dim), fderiv ℝ (b w) (0 : ℝ) ∂(sphereProbability dim)) (1 : ℝ) =
        sphereAverage e y (fun w => horizontal γ f y w a) := by
      rw [ContinuousLinearMap.integral_apply hOp]
      exact integral_congr_ae (Eventually.of_forall fun w => (fderiv_apply_one_eq_deriv.trans (hDer w)))
    exact heq ▸ hInt
  have hQ : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ Y :=
    hq.continuous.continuousAt.preimage_mem_nhds (by simpa only [hq₀] using hY.mem_nhds hy)
  apply hOut.congr_of_eventuallyEq
  filter_upwards [hP,hQ] with t ht hty
  have hOrtho i j : metricPair γ (q t) (F t i) (F t j) = if i = j then 1 else 0 :=
    (ht.2 i j).trans (by rw [hq₀,he y hy])
  exact (sphereAverage_eq_of_orthonormalFrames γ (q t) e (fun _ => F t)
    (he (q t) hty) hOrtho (fun w => f (q t,w))).symm

theorem differentiableOn_sphereAverage {Y : Set (X dim)} (hY : IsOpen Y) {γ : (MetricField dim)} {e : (Frame dim)}
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Y)
    {f : (Field dim)} (hf : smoothNear f (bundle Y γ)) :
    DifferentiableOn ℝ (fun y => sphereAverage e y (fun w => f (y,w))) Y := by
  intro y hy
  let D := (univ : Set (X dim)) ×ˢ Y
  let J (q : (X dim) × (X dim)) := (q.2,frameVector e q.2 q.1)
  have hD : IsOpen D := isOpen_univ.prod hY
  have hJ : ContDiffOn ℝ ∞ J D := by
    refine contDiffOn_snd.prodMk (ContDiffOn.sum (fun i _ => ?_))
    have hE : ContDiffOn ℝ ∞ (fun q : (X dim) × (X dim) => e q.2 i) D :=
      (hec i).comp contDiffOn_snd (fun _ hq => hq.2)
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_fst).contDiffOn.smul hE
  obtain ⟨S,hS,hSub,hfS⟩ := hf
  let O := D ∩ J ⁻¹' S
  have hO : IsOpen O := hJ.continuousOn.isOpen_inter_preimage hD hS
  have hK : (standardSphere dim) ×ˢ ({y} : Set (X dim)) ⊆ O := by
    rintro ⟨w,z⟩ ⟨hw,hz⟩
    have hz' : z = y := mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨mem_univ _,hy⟩,hSub ⟨hy,frameVector_mem_sphere γ e y (he y hy) ⟨w,hw⟩⟩⟩
  obtain ⟨U,V,hU,hV,hSU,hyV,hUV⟩ := generalized_tube_lemma (isCompact_sphere (0 : (X dim)) 1)
    isCompact_singleton hO hK
  have hfJ : ContDiffOn ℝ 1 (Function.uncurry fun w z => f (z,frameVector e z w)) (U ×ˢ V) :=
    (hfS.comp (hJ.mono (fun q hq => (hUV hq).1)) (fun q hq => (hUV hq).2)).of_le (by simp)
  exact (hasFDerivAt_sphereIntegral hU hV hSU hfJ (hyV (mem_singleton y))).differentiableAt.differentiableWithinAt

theorem coordDeriv_sphereAverage {Y : Set (X dim)} (hY : IsOpen Y)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {e : (Frame dim)}
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContDiffOn ℝ ∞ (fun y => e y i) Y)
    {f : (Field dim)} (hf : smoothNear f (bundle Y γ)) {y : (X dim)} (hy : y ∈ Y) (i : (I dim)) :
    coordDeriv i (fun z => sphereAverage e z (fun w => f (z,w))) y =
      sphereAverage e y (fun w => horizontal γ f y w (axis i)) := by
  have hDe := (differentiableOn_sphereAverage hY he hec hf).differentiableAt (hY.mem_nhds hy)
  have hLine : HasDerivAt (fun t : ℝ => y+t • axis i) (axis i) 0 := by
    simpa only [id_eq,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
      ((((hasDerivAt_id (0 : ℝ)).smul_const (axis i)).hasFDerivAt.const_add y :
        HasFDerivAt _ _ (0 : ℝ)).hasDerivAt)
  have hD := hDe.hasFDerivAt
  have h₀ : y+(0 : ℝ) • axis i = y := by simp
  have hL := (hasDerivAt_sphereAverage_along_line hY hγ he hf hy (axis i)).deriv
  have hF := ((h₀.symm ▸ hD).comp_hasDerivAt 0 hLine).deriv
  simpa only [coordDeriv,h₀] using hF.symm.trans hL

end CalderonN
