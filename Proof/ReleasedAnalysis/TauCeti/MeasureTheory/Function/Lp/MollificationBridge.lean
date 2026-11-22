/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.Restriction
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! From Proof/TauCeti/MeasureTheory/Function/Lp/MollificationBridge.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 

















public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Set
open scoped Convolution ENNReal Pointwise

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

local instance : FiniteDimensional ℝ E := .of_locallyCompactSpace ℝ

omit [CompleteSpace F] in
private theorem setIntegral_normedConvolution (phi : ContDiffBump (0 : E)) {f : E → F}
    (hf : Integrable f mu) (s : Set E) :
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
      ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
  have hbase : Integrable (Function.uncurry fun t x : E => phi.normed mu t • f x) (mu.prod mu) :=
    (phi.continuous_normed.integrable_of_hasCompactSupport
      (phi.hasCompactSupport_normed (μ := mu))).smul_prod hf
  have hF_int : Integrable (Function.uncurry fun t x : E => phi.normed mu t • f (x - t))
      (mu.prod mu) := by
    have hshear := measurePreserving_prod_sub mu mu
    have hcomp := hshear.integrable_comp hbase.aestronglyMeasurable |>.mpr hbase
    convert hcomp using 1; rfl
  calc
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
        ∫ t, ∫ x in s, phi.normed mu t • f (x - t) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_smul]
    _ = ∫ x in s, ∫ t, phi.normed mu t • f (x - t) ∂mu ∂mu := by
      apply integral_integral_swap
      have hi := hF_int.integrableOn (s := univ ×ˢ s)
       
       
      change Integrable _ ((mu.prod mu).restrict (univ ×ˢ s)) at hi
      rw [← Measure.prod_restrict univ s] at hi
      simpa only [Measure.restrict_univ] using hi
    _ = ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      rw [convolution_lsmul]

omit [CompleteSpace F] in
private theorem setIntegral_normedConvolution_of_isCompact
    (phi : ContDiffBump (0 : E)) {f : E → F} (hf : LocallyIntegrable f mu)
    {s : Set E} (hs : IsCompact s) :
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
      ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
  let K : Set E := (fun z : E × E => z.1 - z.2) '' (s ×ˢ tsupport (phi.normed mu))
  let fK : E → F := K.indicator f
  have hK : IsCompact K :=
    (hs.prod (phi.hasCompactSupport_normed (μ := mu))).image
      (continuous_fst.sub continuous_snd)
  have hfK : Integrable fK mu := by
    exact (hf.integrableOn_isCompact hK).integrable_indicator hK.measurableSet
  have hmem (x : E) (hx : x ∈ s) (t : E) (ht : phi.normed mu t ≠ 0) : x - t ∈ K := by
    exact ⟨(x, t), ⟨hx, subset_tsupport _ ht⟩, rfl⟩
  calc
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
        ∫ t, phi.normed mu t • ∫ x in s, fK (x - t) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : phi.normed mu t = 0
      · simp only [ht, zero_smul]
      · congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
        exact (indicator_of_mem (hmem x hx t ht) f).symm
    _ = ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] fK) x ∂mu :=
      setIntegral_normedConvolution phi hfK s
    _ = ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hs.measurableSet] with x hx
      simp_rw [convolution_lsmul]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : phi.normed mu t = 0
      · simp only [ht, zero_smul]
      · have hfKx : fK (x - t) = f (x - t) := by
          simpa only [fK] using indicator_of_mem (hmem x hx t ht) f
        rw [hfKx]

 

theorem normedBumpLp_ae_eq_convolution (hp_ne_top : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {f : E → F} (hfLp : MemLp f p mu) :
    (normedBumpLp hp_ne_top phi mu
      (MemLp.toLp f hfLp)) =ᵐ[mu]
      (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) := by
  let conv : E → F := phi.normed mu ⋆[lsmul ℝ ℝ, mu] f
  have hf_loc : LocallyIntegrable f mu := hfLp.locallyIntegrable Fact.out
  have hconv_cont : Continuous conv := by
    exact phi.hasCompactSupport_normed.continuous_convolution_left
      (lsmul ℝ ℝ) phi.continuous_normed hf_loc
  rw [← sub_ae_eq_zero]
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    ((Lp.memLp (normedBumpLp hp_ne_top phi mu (hfLp.toLp f))).locallyIntegrable Fact.out
      |>.sub hconv_cont.locallyIntegrable)
  intro s hs
  rw [integral_sub'
    ((Lp.memLp (normedBumpLp hp_ne_top phi mu (hfLp.toLp f))).locallyIntegrable Fact.out
      |>.integrableOn_isCompact hs)
    (hconv_cont.locallyIntegrable.integrableOn_isCompact hs), sub_eq_zero]
  have hμs : mu s < ∞ := hs.measure_lt_top
  have hLp_int : Integrable
      (fun t => phi.normed mu t • mu.translateLp p (-t) (hfLp.toLp f)) mu := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact phi.continuous_normed.smul
        ((Measure.continuous_translateLp (mu := mu) hp_ne_top (hfLp.toLp f)).comp
          continuous_neg)
    · exact phi.hasCompactSupport_normed.smul_right
  calc
    ∫ x in s, (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) x ∂mu =
        Set.setIntegralLp (𝕜 := ℝ) s hμs
          (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) :=
      (Set.setIntegralLp_apply (𝕜 := ℝ) s hμs _).symm
    _ = ∫ t, Set.setIntegralLp (𝕜 := ℝ) s hμs
          (phi.normed mu t • mu.translateLp p (-t) (hfLp.toLp f)) ∂mu := by
      rw [normedBumpLp_apply]
      exact (Set.setIntegralLp (𝕜 := ℝ) s hμs).integral_comp_comm
        hLp_int |>.symm
    _ = ∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      rw [map_smul, Set.setIntegralLp_apply (𝕜 := ℝ),
        integral_congr_ae (ae_restrict_of_ae (hfLp.coeFn_translateLp_toLp (-t)))]
      simp only [sub_eq_add_neg]
    _ = ∫ x in s, conv x ∂mu := by
      exact setIntegral_normedConvolution_of_isCompact phi hf_loc hs

end TauCeti
