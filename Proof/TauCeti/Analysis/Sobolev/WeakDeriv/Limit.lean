/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.WeakDeriv.Basic

 























public section

namespace TauCeti

open Filter MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] {μ : Measure E}
  {Ω : Opens E} {v : E} {ι : Type*} {l : Filter ι}

omit [NormedSpace ℝ E] in
 


private theorem tendsto_integral_smul_of_tendsto_lintegral_enorm_sub {c : E → ℝ} {K : ℝ}
    (hK : ∀ x, ‖c x‖ ≤ K) (hcsupp : ∀ x ∉ (Ω : Set E), c x = 0)
    {a : ι → E → F} {b : E → F} (ha : ∀ i, Integrable (fun x => c x • a i x) μ)
    (hb : Integrable (fun x => c x • b x) μ)
    (hab : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖a i x - b x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, c x • a i x ∂μ) l (𝓝 (∫ x, c x • b x ∂μ)) := by
  refine tendsto_integral_of_L1 (fun x => c x • b x) hb.1
    (Filter.Eventually.of_forall ha) ?_
  have hlim : Tendsto (fun i => ENNReal.ofReal K * ∫⁻ x in (Ω : Set E), ‖a i x - b x‖ₑ ∂μ) l
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hab
      (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun i => ?_
  have hsupp : Function.support (fun x => ‖c x • (a i x - b x)‖ₑ) ⊆ (Ω : Set E) := by
    intro x hx
    by_contra hxΩ
    exact hx (by simp [hcsupp x hxΩ])
  calc ∫⁻ x, ‖c x • a i x - c x • b x‖ₑ ∂μ
      = ∫⁻ x, ‖c x • (a i x - b x)‖ₑ ∂μ := by
        congr with x
        rw [smul_sub]
    _ = ∫⁻ x in (Ω : Set E), ‖c x • (a i x - b x)‖ₑ ∂μ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ ∫⁻ x in (Ω : Set E), ENNReal.ofReal K * ‖a i x - b x‖ₑ ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [enorm_smul]
        gcongr
        simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hK x)
    _ = ENNReal.ofReal K * ∫⁻ x in (Ω : Set E), ‖a i x - b x‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

 


theorem hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub [OpensMeasurableSpace E] [l.NeBot]
    {u u' : ι → E → F} {w w' : E → F}
    (hw : LocallyIntegrableOn w Ω μ) (hw' : LocallyIntegrableOn w' Ω μ)
    (h : ∀ i, HasWeakLineDerivOn μ Ω (u i) (u' i) v)
    (hu : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖u i x - w x‖ₑ ∂μ) l (𝓝 0))
    (hu' : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖u' i x - w' x‖ₑ ∂μ) l (𝓝 0)) :
    HasWeakLineDerivOn μ Ω w w' v := by
  have : Nonempty ι := nonempty_of_neBot l
  have hcomplete : CompleteSpace F := (h (Classical.arbitrary ι)).completeSpace
  refine hasWeakLineDerivOn_iff_testFunction.2 ⟨hcomplete, hw, hw', fun φ => ?_⟩
  obtain ⟨K, hK⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨K', hK'⟩ :=
    (TestFunction.lineDerivCLM ℝ v φ).continuous.bounded_above_of_compact_support
      (TestFunction.lineDerivCLM ℝ v φ).hasCompactSupport
  have hdφ : ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (φ : E → ℝ) x v :=
    funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top
  rw [hdφ] at hK'
  have h1 : Tendsto (fun i => ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • u i x ∂μ) l
      (𝓝 (∫ x, lineDeriv ℝ (φ : E → ℝ) x v • w x ∂μ)) :=
    tendsto_integral_smul_of_tendsto_lintegral_enorm_sub hK'
      (fun x hx => lineDeriv_eq_zero_of_notMem_tsupport φ (fun hm => hx (φ.tsupport_subset hm)) v)
      (fun i => integrable_lineDeriv_smul_of_locallyIntegrableOn (h i).locallyIntegrableOn φ v)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hw φ v) hu
  have h2 : Tendsto (fun i => ∫ x, (φ : E → ℝ) x • u' i x ∂μ) l
      (𝓝 (∫ x, (φ : E → ℝ) x • w' x ∂μ)) :=
    tendsto_integral_smul_of_tendsto_lintegral_enorm_sub hK
      (fun x hx => image_eq_zero_of_notMem_tsupport fun hm => hx (φ.tsupport_subset hm))
      (fun i => integrable_smul_of_locallyIntegrableOn (h i).locallyIntegrableOn_deriv φ)
      (integrable_smul_of_locallyIntegrableOn hw' φ) hu'
  refine tendsto_nhds_unique ?_ h2.neg
  simpa only [(h _).integral_lineDeriv_smul_eq_neg_integral_smul φ] using h1

 


theorem hasWeakFDerivOn_of_tendsto_lintegral_enorm_sub [OpensMeasurableSpace E] [l.NeBot]
    {u : ι → E → F} {U : ι → E → E →L[ℝ] F} {w : E → F} {W : E → E →L[ℝ] F}
    (hw : LocallyIntegrableOn w Ω μ) (hW : ∀ v : E, LocallyIntegrableOn (fun x => W x v) Ω μ)
    (h : ∀ i, HasWeakFDerivOn μ Ω (u i) (U i))
    (hu : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖u i x - w x‖ₑ ∂μ) l (𝓝 0))
    (hU : Tendsto (fun i => ∫⁻ x in (Ω : Set E), ‖U i x - W x‖ₑ ∂μ) l (𝓝 0)) :
    HasWeakFDerivOn μ Ω w W := by
  rw [hasWeakFDerivOn_iff]
  intro v
  refine hasWeakLineDerivOn_of_tendsto_lintegral_enorm_sub hw (hW v)
    (fun i => (h i).hasWeakLineDerivOn v) hu ?_
  have hbound : ∀ i, ∫⁻ x in (Ω : Set E), ‖U i x v - W x v‖ₑ ∂μ ≤
      ‖v‖ₑ * ∫⁻ x in (Ω : Set E), ‖U i x - W x‖ₑ ∂μ := by
    intro i
    rw [← lintegral_const_mul' _ _ enorm_ne_top]
    refine lintegral_mono fun x => ?_
    have hle : ‖U i x v - W x v‖ ≤ ‖U i x - W x‖ * ‖v‖ := by
      simpa using (U i x - W x).le_opNorm v
    calc ‖U i x v - W x v‖ₑ ≤ ENNReal.ofReal (‖U i x - W x‖ * ‖v‖) := by
          simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal hle
      _ = ‖v‖ₑ * ‖U i x - W x‖ₑ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm,
            mul_comm]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => zero_le) hbound
  simpa using ENNReal.Tendsto.const_mul (a := ‖v‖ₑ) hU (Or.inr enorm_ne_top)

end TauCeti
