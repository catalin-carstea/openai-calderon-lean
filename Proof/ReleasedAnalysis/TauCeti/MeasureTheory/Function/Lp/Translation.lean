/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.SegmentIncrement
public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv
public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
public import Proof.ReleasedAnalysis.TauCeti.Topology.Instances.ENNReal
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-! From Proof/TauCeti/MeasureTheory/Function/Lp/Translation.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 
















































public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory

namespace Lp

variable {E F : Type*} [AddGroup E] [MeasurableSpace E] [TopologicalSpace E] [ContinuousAdd E]
  [BorelSpace E] [R1Space E] [NormedAddCommGroup F] {mu : Measure E} [mu.IsAddRightInvariant]
  [mu.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure mu] {p : ℝ≥0∞} [Fact (1 ≤ p)]

 

theorem continuous_compMeasurePreserving_add_right (hp : p ≠ ∞) (f : Lp F p mu) :
    Continuous fun h : E ↦ compMeasurePreserving (· + h) (measurePreserving_add_right mu h) f := by
  let T : E → C(E, E) := fun h ↦ ⟨(· + h), by fun_prop⟩
  have hT : Continuous T := ContinuousMap.continuous_of_continuous_uncurry T <| by
    dsimp only [T, Function.uncurry_apply_pair, ContinuousMap.coe_mk]
    fun_prop
  exact continuous_const.compMeasurePreservingLp hT
    (fun h ↦ measurePreserving_add_right mu h) hp

end Lp

namespace Measure

section LpTranslation

variable {E F : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E} [mu.IsAddRightInvariant]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

 

@[expose] def translateLp (mu : Measure E) [mu.IsAddRightInvariant] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : E) : Lp F p mu ≃ₗᵢ[ℝ] Lp F p mu :=
  Lp.compMeasurePreservingₗᵢEquiv ℝ (measurePreserving_add_right mu h)
    (measurePreserving_add_right mu (-h))
    (Filter.EventuallyEq.of_eq (funext fun x ↦ by simp))

 
theorem coeFn_translateLp (h : E) (f : Lp F p mu) :
    ⇑(translateLp mu p h f) =ᵐ[mu] ⇑f ∘ (· + h) := by
  rw [translateLp]
  exact Lp.coeFn_compMeasurePreservingₗᵢEquiv ℝ _ _ _ f

 
theorem compLpL_translateLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (h : E) (f : Lp F p mu) :
    L.compLpL p mu (translateLp mu p h f) = translateLp mu p h (L.compLpL p mu f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (translateLp mu p h f), coeFn_translateLp (mu := mu) h f,
    coeFn_translateLp (mu := mu) h (L.compLpL p mu f),
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae.eventually
      (L.coeFn_compLpL f)] with x hL htr htrL hLtr
  rw [hL, htr, htrL]
  exact hLtr.symm

 
theorem translateLp_add (h₁ h₂ : E) :
    translateLp (F := F) mu p (h₁ + h₂) = (translateLp mu p h₁).trans (translateLp mu p h₂) := by
  refine LinearIsometryEquiv.ext fun f => Lp.ext ?_
  filter_upwards [coeFn_translateLp (mu := mu) (h₁ + h₂) f,
    coeFn_translateLp (mu := mu) h₂ (translateLp mu p h₁ f),
    (measurePreserving_add_right mu h₂).quasiMeasurePreserving.ae_eq_comp
      (coeFn_translateLp (mu := mu) h₁ f)] with x hx hy hz
  simp only [Function.comp_apply] at hx hy hz
  rw [hx, LinearIsometryEquiv.trans_apply, hy, hz]
  exact congrArg _ (by abel)

 
@[simp]
theorem translateLp_zero (f : Lp F p mu) : translateLp mu p 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translateLp (mu := mu) 0 f] with x hx
  simpa only [Function.comp_apply, add_zero] using hx

 
@[simp]
theorem translateLp_symm (h : E) :
    (translateLp (F := F) mu p h).symm = translateLp mu p (-h) :=
  LinearIsometryEquiv.ext fun f => (LinearIsometryEquiv.symm_apply_eq _).2 <| by
    rw [← LinearIsometryEquiv.trans_apply, ← translateLp_add, neg_add_cancel, translateLp_zero]

 

theorem continuous_translateLp [TopologicalSpace E] [ContinuousAdd E] [BorelSpace E] [R1Space E]
    [mu.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure mu] (hp : p ≠ ∞) (f : Lp F p mu) :
    Continuous fun h : E ↦ translateLp mu p h f := by
  simpa only [translateLp, Lp.compMeasurePreservingₗᵢEquiv_apply] using
    Lp.continuous_compMeasurePreserving_add_right hp f

 
theorem enorm_translateLp_sub (h : E) (f : Lp F p mu) :
    ‖translateLp mu p h f - f‖ₑ = eLpNorm (fun x ↦ f (x + h) - f x) p mu := by
  have hae : ⇑(translateLp mu p h f - f) =ᵐ[mu] fun x ↦ f (x + h) - f x := by
    filter_upwards [Lp.coeFn_sub (translateLp mu p h f) f,
      coeFn_translateLp (mu := mu) h f] with x hx hy
    rw [hx, Pi.sub_apply, hy]
    rfl
  rw [Lp.enorm_def, eLpNorm_congr_ae hae]

end LpTranslation

end Measure

namespace MemLp

 
theorem coeFn_translateLp_toLp {E F : Type*} [AddCommGroup E] [MeasurableSpace E]
    [MeasurableAdd E] [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E}
    [mu.IsAddRightInvariant] {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : E → F} (hf : MemLp f p mu) (h : E) :
    ⇑(mu.translateLp p h (hf.toLp f)) =ᵐ[mu] fun x ↦ f (x + h) :=
  (Measure.coeFn_translateLp h (hf.toLp f)).trans
    ((measurePreserving_add_right mu h).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)

variable {E F : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E] {mu : Measure E}
  [mu.IsAddRightInvariant] {p : ℝ≥0∞}

 


theorem comp_add_right_restrict_of_mapsTo [TopologicalSpace F] [ContinuousENorm F]
    {Omega V : Set E} {h : E} {f : E → F}
    (hf : MemLp f p (mu.restrict Omega)) (hVO : MapsTo (· + h) V Omega) :
    MemLp (fun x => f (x + h)) p (mu.restrict V) :=
  (hf.comp_measurePreserving ((measurePreserving_add_right mu h).restrict_preimage_emb
    (measurableEmbedding_addRight h) Omega)).mono_measure
    (Measure.restrict_mono_set mu hVO.subset_preimage)

 
theorem tendsto_eLpNorm_comp_add_sub [TopologicalSpace E] [ContinuousAdd E] [BorelSpace E]
    [R1Space E] [mu.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure mu] [NormedAddCommGroup F]
    {u : E → F} (hu : MemLp u p mu) (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    Filter.Tendsto (fun h : E ↦ eLpNorm (fun x ↦ u (x + h) - u x) p mu) (nhds 0) (nhds 0) := by
  have : Fact (1 ≤ p) := ⟨hp⟩
  have htend := (Lp.continuous_compMeasurePreserving_add_right hp' (hu.toLp u)).tendsto 0
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at htend
  refine htend.congr' (Filter.Eventually.of_forall fun h ↦ eLpNorm_congr_ae ?_)
  exact (((Lp.coeFn_compMeasurePreserving _ _).trans
      ((measurePreserving_add_right mu h).quasiMeasurePreserving.ae_eq_comp hu.coeFn_toLp)).sub
    ((Lp.coeFn_compMeasurePreserving _ _).trans
      ((measurePreserving_add_right mu 0).quasiMeasurePreserving.ae_eq_comp
        hu.coeFn_toLp))).trans (Filter.EventuallyEq.of_eq (funext fun x ↦ by simp))

end MemLp

end MeasureTheory

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

 


theorem ContDiff.enorm_sub_rpow_le_lintegral_fderiv_apply (hu : ContDiff ℝ 1 u)
    {r : ℝ} (hr : 1 ≤ r) (x h : E) :
    ‖u (x + h) - u x‖ₑ ^ r ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ ^ r := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hmeas : AEMeasurable (fun t : ℝ => ‖fderiv ℝ u (x + t • h) h‖ₑ)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (((hu.continuous_fderiv one_ne_zero).comp
      (by fun_prop : Continuous fun t : ℝ => x + t • h)).clm_apply
      continuous_const).enorm.aemeasurable
  have huniv : (volume.restrict (Icc (0 : ℝ) 1)) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  have hsegment := TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply x h
    (fun t _ => (hu.differentiable one_ne_zero) (x + t • h))
    (((hu.continuous_fderiv one_ne_zero).comp_continuousOn (by fun_prop)).clm_apply
      continuousOn_const)
   
  calc ‖u (x + h) - u x‖ₑ ^ r
      ≤ (∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ) ^ r :=
        ENNReal.rpow_le_rpow hsegment hr0.le
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ ^ r := by
        simpa [huniv] using TauCeti.rpow_lintegral_le_measure_univ_rpow_mul hmeas hr

end Calculus

section Translation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {mu : Measure E} [SFinite mu] [mu.IsAddRightInvariant]
  {u : E → F}

 





theorem ContDiff.setLIntegral_enorm_comp_add_sub_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ}
    (hr : 1 ≤ r) (h : E) {K T : Set E} (hT : MeasurableSet T)
    (hKT : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ T) :
    ∫⁻ x in K, ‖u (x + h) - u x‖ₑ ^ r ∂mu ≤ ∫⁻ x in T, ‖fderiv ℝ u x h‖ₑ ^ r ∂mu := by
   
  set g : E → ℝ≥0∞ := T.indicator fun y => ‖fderiv ℝ u y h‖ₑ ^ r
  have hg : Measurable g :=
    (ENNReal.continuous_rpow_const.comp (((hu.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).enorm)).measurable.indicator hT
  have hjoint : Measurable fun z : E × ℝ => g (z.1 + z.2 • h) :=
    hg.comp (by fun_prop : Continuous fun z : E × ℝ => z.1 + z.2 • h).measurable
  calc ∫⁻ x in K, ‖u (x + h) - u x‖ₑ ^ r ∂mu
      ≤ ∫⁻ x in K, (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • h)) ∂mu := by
        refine setLIntegral_mono hjoint.lintegral_prod_right' fun x hx => ?_
        refine (hu.enorm_sub_rpow_le_lintegral_fderiv_apply hr x h).trans
          (setLIntegral_mono' measurableSet_Icc fun t ht => ?_)
        simp [g, indicator_of_mem (hKT x hx t ht)]
    _ ≤ ∫⁻ x, (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • h)) ∂mu := setLIntegral_le_lintegral _ _
    _ = ∫⁻ t in Icc (0 : ℝ) 1, (∫⁻ x, g (x + t • h) ∂mu) :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ x in T, ‖fderiv ℝ u x h‖ₑ ^ r ∂mu := by
        rw [setLIntegral_congr_fun measurableSet_Icc fun t _ =>
          lintegral_add_right_eq_self g (t • h), lintegral_const, Measure.restrict_apply_univ,
          Real.volume_Icc, lintegral_indicator hT]
        simp

 

theorem ContDiff.lintegral_enorm_comp_add_sub_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r)
    (h : E) :
    ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu ≤ ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
  have hr0 : (0 : ℝ) ≤ r := zero_le_one.trans hr
  calc ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu
      ≤ ∫⁻ x, ‖fderiv ℝ u x h‖ₑ ^ r ∂mu := by
        simpa only [Measure.restrict_univ] using
          hu.setLIntegral_enorm_comp_add_sub_rpow_le (mu := mu) (K := univ) hr h
            MeasurableSet.univ fun _ _ _ _ => mem_univ _
    _ ≤ ∫⁻ x, (‖fderiv ℝ u x‖ₑ * ‖h‖ₑ) ^ r ∂mu := by
        gcongr with x
        exact ContinuousLinearMap.le_opENorm _ _
    _ = ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0]
        rw [lintegral_mul_const' _ _ (by finiteness), mul_comm]

 







theorem ContDiff.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply [SecondCountableTopology E]
    (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (h : E) {K T : Set E}
    (hT : MeasurableSet T) (hKT : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ T) :
    eLpNorm (fun x => u (x + h) - u x) p (mu.restrict K)
      ≤ eLpNorm (fun x => fderiv ℝ u x h) p (mu.restrict T) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hsub : Continuous fun x => u (x + h) - u x := by fun_prop
  have hfd : Continuous fun x => fderiv ℝ u x h :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hsub.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hfd.aestronglyMeasurable]
  exact ENNReal.rpow_le_rpow (hu.setLIntegral_enorm_comp_add_sub_rpow_le hr h hT hKT)
    (by positivity)

 







theorem ContDiff.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv [SecondCountableTopology E]
    (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (h : E) :
    eLpNorm (fun x => u (x + h) - u x) p mu ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ u) p mu := by
  calc eLpNorm (fun x => u (x + h) - u x) p mu
      ≤ eLpNorm (fun x => fderiv ℝ u x h) p mu := by
        simpa only [Measure.restrict_univ] using
          hu.eLpNorm_comp_add_sub_le_eLpNorm_fderiv_apply (mu := mu) (K := univ) hp hp' h
            MeasurableSet.univ fun _ _ _ _ => mem_univ _
    _ ≤ ‖h‖ₑ * eLpNorm (fderiv ℝ u) p mu :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
          ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => by
            rw [mul_comm]
            exact ContinuousLinearMap.le_opENorm _ _)

 






theorem ContDiff.tendsto_eLpNorm_comp_add_sub [SecondCountableTopology E] (hu : ContDiff ℝ 1 u)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (hfin : eLpNorm (fderiv ℝ u) p mu ≠ ∞) :
    Filter.Tendsto (fun h : E => eLpNorm (fun x => u (x + h) - u x) p mu) (nhds 0) (nhds 0) :=
  TauCeti.tendsto_nhds_zero_of_le_enorm_mul hfin fun h =>
    hu.eLpNorm_comp_add_sub_le_mul_eLpNorm_fderiv hp hp' h

end Translation
