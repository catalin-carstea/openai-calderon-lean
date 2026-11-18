/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.Mollification.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

 



















public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] [SFinite mu] [IsLocallyFiniteMeasure mu]
  {Omega : Opens E} {u : E → F} {U : E → E →L[ℝ] F} {p q : ℝ≥0∞}

 



theorem HasWeakFDerivOn.hasFDerivAt_indicator_convolution_right
    (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho)
      ((((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] rho) x) x := by
  have hu_ext : MemLp ((Omega : Set E).indicator u) p mu :=
    (memLp_indicator_iff_restrict (f := u) Omega.isOpen.measurableSet.nullMeasurableSet).2 hu
  have hU_ext : MemLp ((Omega : Set E).indicator U) q mu :=
    (memLp_indicator_iff_restrict (f := U) Omega.isOpen.measurableSet.nullMeasurableSet).2 hU
  exact h.indicator.hasFDerivAt_convolution_right (hu_ext.locallyIntegrable hp)
    (hU_ext.locallyIntegrable hq) rho hrho hrho_cpt x hx

 


theorem HasWeakFDerivOn.fderiv_indicator_convolution_right
    (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (rho : E → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hrho_cpt : HasCompactSupport rho) (x : E)
    (hx : ∀ y ∈ tsupport rho, x - y ∈ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] rho) x =
      (((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] rho) x :=
  (h.hasFDerivAt_indicator_convolution_right hu hU hp hq rho hrho hrho_cpt x hx).fderiv

 


theorem HasWeakFDerivOn.hasFDerivAt_indicator_convolution_normed
    [FiniteDimensional ℝ E] [HasContDiffBump E]
    (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    HasFDerivAt
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] phi.normed mu)
      ((((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] phi.normed mu) x) x := by
  apply h.hasFDerivAt_indicator_convolution_right hu hU hp hq
    (phi.normed mu) phi.contDiff_normed phi.hasCompactSupport_normed x
  intro y hy
  apply hx
  rw [phi.tsupport_normed_eq] at hy
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg,
    sub_zero] using hy

 


theorem HasWeakFDerivOn.fderiv_indicator_convolution_normed
    [FiniteDimensional ℝ E] [HasContDiffBump E]
    (h : HasWeakFDerivOn mu Omega u U)
    (hu : MemLp u p (mu.restrict Omega)) (hU : MemLp U q (mu.restrict Omega))
    (hp : 1 ≤ p) (hq : 1 ≤ q) (phi : ContDiffBump (0 : E)) (x : E)
    (hx : Metric.closedBall x phi.rOut ⊆ Omega) :
    fderiv ℝ
      (((Omega : Set E).indicator u) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, mu] phi.normed mu) x =
      (((Omega : Set E).indicator U) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ :
          ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F).flip, mu] phi.normed mu) x :=
  (h.hasFDerivAt_indicator_convolution_normed hu hU hp hq phi x hx).fderiv

end TauCeti
