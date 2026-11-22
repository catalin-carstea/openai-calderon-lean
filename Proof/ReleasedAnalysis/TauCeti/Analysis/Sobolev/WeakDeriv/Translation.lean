/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.Translation
import Proof.ReleasedAnalysis.TauCeti.Analysis.Distribution.TestFunction.Translation
import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral

/-! From Proof/TauCeti/Analysis/Sobolev/WeakDeriv/Translation.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 





























public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped Distributions

namespace TauCeti

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega V : Opens E}
  {u u' : E → F} {U : E → E →L[ℝ] F} {v h : E}

local instance weakDerivTranslation_isAddHaarMeasure :
    (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

 

theorem HasWeakLineDerivOn.comp_add_right
    (hu : HasWeakLineDerivOn mu Omega u u' v) (hVO : MapsTo (· + h) V Omega) :
    HasWeakLineDerivOn mu V (fun x => u (x + h)) (fun x => u' (x + h)) v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨hu.completeSpace,
    MeasureTheory.LocallyIntegrableOn.comp_add_right_of_mapsTo hu.locallyIntegrableOn hVO,
    MeasureTheory.LocallyIntegrableOn.comp_add_right_of_mapsTo
      hu.locallyIntegrableOn_deriv hVO,
    fun phi => ?_⟩
  let psi := translateTestFunction hVO phi
  have hleft :
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • u (x + h) ∂mu) =
        ∫ y, lineDeriv ℝ (psi : E → ℝ) y v • u y ∂mu := by
    simpa only [psi, lineDeriv_translateTestFunction, add_sub_cancel_right] using
      integral_add_right_eq_self
        (fun y => lineDeriv ℝ (psi : E → ℝ) y v • u y) h
  have hright :
      (∫ x, (phi : E → ℝ) x • u' (x + h) ∂mu) =
        ∫ y, (psi : E → ℝ) y • u' y ∂mu := by
    simpa only [psi, translateTestFunction_apply, add_sub_cancel_right] using
      integral_add_right_eq_self (fun y => (psi : E → ℝ) y • u' y) h
  rw [hleft, hright]
  exact hu.integral_lineDeriv_smul_eq_neg_integral_smul psi

 

theorem HasWeakFDerivOn.comp_add_right
    (hu : HasWeakFDerivOn mu Omega u U) (hVO : MapsTo (· + h) V Omega) :
    HasWeakFDerivOn mu V (fun x => u (x + h)) (fun x => U (x + h)) := by
  rw [hasWeakFDerivOn_iff]
  intro w
  exact (hu.hasWeakLineDerivOn w).comp_add_right hVO

 

theorem HasWeakFDerivOn.translateLp {p : ENNReal} [Fact (1 ≤ p)]
    {f : Lp F p (mu.restrict ((⊤ : Opens E) : Set E))}
    {D : Lp (E →L[ℝ] F) p (mu.restrict ((⊤ : Opens E) : Set E))}
    (hf : HasWeakFDerivOn mu ⊤ f D) (h : E) :
    HasWeakFDerivOn mu ⊤
      ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h f)
      ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p h D) := by
  let nu := mu.restrict ((⊤ : Opens E) : Set E)
  have htrans := hf.comp_add_right (V := (⊤ : Opens E)) (h := h) (fun _ _ => by simp)
  exact (htrans.congr_ae (Measure.coeFn_translateLp (mu := nu) h f).symm).congr_ae_deriv
    (Measure.coeFn_translateLp (mu := nu) h D).symm

 


theorem HasWeakFDerivOn.differenceQuotient
    (hu : HasWeakFDerivOn mu Omega u U) (hV : V ≤ Omega) {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) V Omega) :
    HasWeakFDerivOn mu V (fun x => t⁻¹ • (u (x + t • w) - u x))
      (fun x => t⁻¹ • (U (x + t • w) - U x)) := by
  exact ((hu.comp_add_right hVO).sub (hu.mono hV)).const_smul t⁻¹

end TauCeti
