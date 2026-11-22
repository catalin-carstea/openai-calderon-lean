/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.Continuity
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! From Proof/TauCeti/Analysis/PDE/EnergyForm/Measurability.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 






















public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1200000
namespace TauCeti

namespace PDE

open MeasureTheory

variable {α n : Type*} [MeasurableSpace α] [Fintype n]
attribute [local irreducible] energyIntegrand energyIntegrandLinear

 

lemma stronglyMeasurable_energyIntegrand {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n}
    {c : α → ℝ}
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hc : StronglyMeasurable c) :
    StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) := by
  have hpack : StronglyMeasurable (fun x => (a x,b x,c x)) := ha.prodMk (hb.prodMk hc)
  have he : (fun x => PDE.energyIntegrand (a x) (b x) (c x)) =
      ((energyIntegrandLinear (n := n)) ∘ fun x => (a x,b x,c x)) :=
    funext (fun x => (energyIntegrandLinear_apply (a x) (b x) (c x)).symm)
  rw [he]
  exact (energyIntegrandLinear (n := n)).continuous.comp_stronglyMeasurable hpack

 

lemma stronglyMeasurable_energyIntegrand_apply₂ {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ} {U V : α → ℝ × EuclideanSpace ℝ n}
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hc : StronglyMeasurable c)
    (hU : StronglyMeasurable U) (hV : StronglyMeasurable V) :
    StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) (U x) (V x)) := by
  let Jet := ℝ × EuclideanSpace ℝ n
  have hform : StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) :=
    stronglyMeasurable_energyIntegrand ha hb hc
  have hcont : Continuous (fun p : (Jet →L[ℝ] Jet →L[ℝ] ℝ) × Jet × Jet =>
      p.1 p.2.1 p.2.2) := by
    exact (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply
      (continuous_snd.comp continuous_snd)
  exact hcont.comp_stronglyMeasurable (hform.prodMk (hU.prodMk hV))

 

lemma stronglyMeasurable_energyIntegrand_apply {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hc : StronglyMeasurable c)
    (U V : ℝ × EuclideanSpace ℝ n) :
    StronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) U V) :=
  stronglyMeasurable_energyIntegrand_apply₂ ha hb hc stronglyMeasurable_const
    stronglyMeasurable_const

variable {μ : MeasureTheory.Measure α}

 

lemma aestronglyMeasurable_energyIntegrand {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    (ha : MeasureTheory.AEStronglyMeasurable a μ) (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (hc : MeasureTheory.AEStronglyMeasurable c μ) :
    AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) μ := by
  have hpack : AEStronglyMeasurable (fun x => (a x,b x,c x)) μ := ha.prodMk (hb.prodMk hc)
  have he : (fun x => PDE.energyIntegrand (a x) (b x) (c x)) =
      ((energyIntegrandLinear (n := n)) ∘ fun x => (a x,b x,c x)) :=
    funext (fun x => (energyIntegrandLinear_apply (a x) (b x) (c x)).symm)
  rw [he]
  exact (energyIntegrandLinear (n := n)).continuous.comp_aestronglyMeasurable hpack

 

lemma aestronglyMeasurable_energyIntegrand_apply {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    (ha : MeasureTheory.AEStronglyMeasurable a μ) (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (hc : MeasureTheory.AEStronglyMeasurable c μ) (U V : ℝ × EuclideanSpace ℝ n) :
    AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) U V) μ :=
  MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap
    (MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap
      (aestronglyMeasurable_energyIntegrand ha hb hc) U) V

 

lemma aestronglyMeasurable_energyIntegrand_apply₂ {a : α → Matrix n n ℝ}
    {b : α → EuclideanSpace ℝ n} {c : α → ℝ} {U V : α → ℝ × EuclideanSpace ℝ n}
    (ha : MeasureTheory.AEStronglyMeasurable a μ) (hb : MeasureTheory.AEStronglyMeasurable b μ)
    (hc : MeasureTheory.AEStronglyMeasurable c μ) (hU : MeasureTheory.AEStronglyMeasurable U μ)
    (hV : MeasureTheory.AEStronglyMeasurable V μ) :
    AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  let Jet := ℝ × EuclideanSpace ℝ n
  have hform : AEStronglyMeasurable (fun x => PDE.energyIntegrand (a x) (b x) (c x)) μ :=
    aestronglyMeasurable_energyIntegrand ha hb hc
  have hcont : Continuous (fun p : (Jet →L[ℝ] Jet →L[ℝ] ℝ) × Jet × Jet =>
      p.1 p.2.1 p.2.2) := by
    exact (continuous_fst.clm_apply (continuous_fst.comp continuous_snd)).clm_apply
      (continuous_snd.comp continuous_snd)
  have hm : AEStronglyMeasurable (fun x => (energyIntegrand (a x) (b x) (c x), U x, V x)) μ :=
    hform.prodMk (hU.prodMk hV)
  exact hcont.comp_aestronglyMeasurable hm

end PDE

end TauCeti
