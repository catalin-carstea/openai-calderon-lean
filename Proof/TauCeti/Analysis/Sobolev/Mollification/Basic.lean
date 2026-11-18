/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

 



































public section

namespace TauCeti

open MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped ContDiff Convolution Distributions

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddLeftInvariant] [SFinite mu] {Omega : Opens E}

 



theorem HasWeakLineDerivOn.hasLineDerivAt_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasLineDerivAt ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) ((u' ⋆[(lsmul ℝ ℝ).flip, mu] rho) x) x v := by
  have hsmooth : ContDiff ℝ ∞ fun t ↦ rho (x - t) := by fun_prop
  have hcpt : HasCompactSupport fun t ↦ rho (x - t) :=
    hrho_cpt.comp_homeomorph (Homeomorph.subLeft x)
  have hsupp : tsupport (fun t ↦ rho (x - t)) ⊆ Omega := fun t ht ↦ by
    simpa using hx _ (tsupport_comp_subset_preimage rho (f := (x - ·)) (by fun_prop) ht)
  have hline (t : E) : lineDeriv ℝ (fun s ↦ rho (x - s)) t v = -fderiv ℝ rho (x - t) v := by
    simpa [Function.comp_def] using ((hrho.differentiable (by simp) (x - t)).hasFDerivAt.comp t
      ((hasFDerivAt_id t).const_sub x)).hasLineDerivAt v |>.lineDeriv
  have hweak := h.integral_lineDeriv_smul_eq_neg_integral_smul ⟨_, hsmooth, hcpt, hsupp⟩
  simp only [TestFunction.coe_mk, hline, neg_smul, integral_neg, neg_inj] at hweak
  convert (hrho_cpt.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu
    (hrho.of_le (by simp)) x).hasLineDerivAt v using 1
  rw [convolution_precompR_apply (lsmul ℝ ℝ).flip hu (hrho_cpt.fderiv ℝ)
    (hrho.continuous_fderiv (by simp)) x v]
  simpa only [convolution_def, flip_apply, lsmul_apply] using hweak.symm

 

theorem HasWeakLineDerivOn.lineDeriv_convolution_right {u u' : E → F} {v : E}
    (h : HasWeakLineDerivOn mu Omega u u' v) (hu : LocallyIntegrable u mu)
    (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    lineDeriv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) x v = (u' ⋆[(lsmul ℝ ℝ).flip, mu] rho) x :=
  (h.hasLineDerivAt_convolution_right hu rho hrho hrho_cpt x hx).lineDeriv

 




theorem HasWeakFDerivOn.hasFDerivAt_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) ((U ⋆[(lsmul ℝ ℝ).flip, mu] rho) x) x := by
  have hd := hrho_cpt.hasFDerivAt_convolution_right (lsmul ℝ ℝ).flip hu (hrho.of_le (by simp)) x
  refine hd.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  refine ((hd.hasLineDerivAt v).unique ((h.hasWeakLineDerivOn v).hasLineDerivAt_convolution_right
    hu rho hrho hrho_cpt x hx)).trans ?_
  have hInt := (hrho_cpt.convolutionExists_right (lsmul ℝ ℝ).flip hU hrho.continuous x).integrable
  simp only [convolution_def]
  rw [ContinuousLinearMap.integral_apply hInt]
  simp only [flip_apply, lsmul_apply, smul_apply]

 

theorem HasWeakFDerivOn.fderiv_convolution_right {u : E → F} {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (rho : E → ℝ)
    (hrho : ContDiff ℝ ∞ rho) (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ (u ⋆[(lsmul ℝ ℝ).flip, mu] rho) x = (U ⋆[(lsmul ℝ ℝ).flip, mu] rho) x :=
  (h.hasFDerivAt_convolution_right hu hU rho hrho hrho_cpt x hx).fderiv

end TauCeti
