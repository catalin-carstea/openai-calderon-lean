/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.CalderonN.WeakSolutionLocalization
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Regularity.HalfSpace

import Mathlib.Tactic

/-! Cutoff localization on a larger open domain with zero extension of a
zero-trace cutoff product. This uses the localization formula already
checked for the interior equation. A larger-domain test is restricted by
a second cutoff equal to one near the intersection of the two supports. -/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter
open scoped ContDiff Distributions ENNReal NNReal Gradient InnerProductSpace Topology Matrix.Norms.Elementwise
open OAI.AnisotropicCalderon.Regularity
open TauCeti

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
  {Ω H : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

theorem exists_isWeakSolutionDirichlet_smoothCutoff
    (ha : ContDiff ℝ ∞ a)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (μ.restrict H))
    (hΩH : Ω ≤ H) (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    {f : Lp ℝ 2 (μ.restrict Ω)} {u : W1p μ Ω 2}
    (hu : ∀ φ : 𝓓(Ω, ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ μ Ω 2 φ) =
        ∫ x in Ω, f x * φ x ∂μ)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hts : tsupport ψ ∩ H ⊆ (Ω : Set (EuclideanSpace ℝ ι)))
    {N : ℝ} (hN : 0 ≤ N) (hψN : ∀ x ∈ Ω, |ψ x| ≤ N)
    (hgradN : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ N)
    (hmem : W1p.contDiffSMul ψ hψ hN hψN hgradN u ∈ w1p0Submodule μ Ω 2) :
    ∃ w : W1p0 μ H 2, ∃ g : Lp ℝ 2 (μ.restrict H),
      IsWeakSolutionDirichlet a 0 0 g w ∧
        (∀ᵐ x ∂μ.restrict H, g x = (Ω : Set (EuclideanSpace ℝ ι)).indicator
          (locForcing a ψ f u) x) ∧
        (∀ᵐ x ∂μ.restrict H, W1p.value (w : W1p μ H 2) x =
          (Ω : Set (EuclideanSpace ℝ ι)).indicator (fun y => ψ y * W1p.value u y) x) ∧
        ∀ᵐ x ∂μ.restrict H, W1p.gradient (w : W1p μ H 2) x =
          (Ω : Set (EuclideanSpace ℝ ι)).indicator
            (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x := by
  have hΩ := Ω.isOpen.measurableSet
  have hsub : (Ω : Set (EuclideanSpace ℝ ι)) ⊆ H := SetLike.coe_subset_coe.mpr hΩH
  let v : W1p0 μ Ω 2 := ⟨_, hmem⟩
  let w : W1p0 μ H 2 := W1p0.extendByZeroL hΩH v
  let F := locForcing a ψ f u
  have hF := memLp_locForcing ha hψ hΩb f u
  let g := extendByZeroLpₗᵢ ℝ μ hΩ hsub (hF.toLp F)
  have hg : ∀ᵐ x ∂μ.restrict H, g x = (Ω : Set (EuclideanSpace ℝ ι)).indicator F x := by
    have h3 := (ae_restrict_iff' hΩ).1 hF.coeFn_toLp
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ (μ := μ) hΩ hsub (hF.toLp F),
      ae_restrict_of_ae h3] with x hx hx3
    change extendByZeroLpₗᵢ ℝ μ hΩ hsub (hF.toLp F) x = _
    rw [hx]
    by_cases hy : x ∈ (Ω : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hy, indicator_of_mem hy, hx3 hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy]
  have hwg : ∀ᵐ x ∂μ.restrict H, W1p.gradient (w : W1p μ H 2) x =
      (Ω : Set (EuclideanSpace ℝ ι)).indicator
        (fun y => ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x := by
    change ∀ᵐ x ∂μ.restrict H, W1p.gradient (W1p0.extendByZeroL hΩH v : W1p μ H 2) x = _
    rw [W1p0.gradient_extendByZeroL]
    have h3 := (ae_restrict_iff' hΩ).1 (W1p.gradient_contDiffSMul_ae hψ hN hψN hgradN u)
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ (μ := μ) hΩ hsub (W1p.gradient (v : W1p μ Ω 2)),
      ae_restrict_of_ae h3] with x hx hx3
    rw [hx]
    by_cases hy : x ∈ (Ω : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hy, indicator_of_mem hy]
      exact hx3 hy
    · rw [indicator_of_notMem hy, indicator_of_notMem hy]
  have hwv : ∀ᵐ x ∂μ.restrict H, W1p.value (w : W1p μ H 2) x =
      (Ω : Set (EuclideanSpace ℝ ι)).indicator (fun y => ψ y * W1p.value u y) x := by
    change ∀ᵐ x ∂μ.restrict H, W1p.value (W1p0.extendByZeroL hΩH v : W1p μ H 2) x = _
    rw [W1p0.value_extendByZeroL]
    have h3 := (ae_restrict_iff' hΩ).1 (W1p.value_contDiffSMul_ae hψ hN hψN hgradN u)
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ (μ := μ) hΩ hsub (W1p.value (v : W1p μ Ω 2)),
      ae_restrict_of_ae h3] with x hx hx3
    rw [hx]
    by_cases hy : x ∈ (Ω : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hy, indicator_of_mem hy]
      exact hx3 hy
    · rw [indicator_of_notMem hy, indicator_of_notMem hy]
  have hu' (φ : 𝓓(Ω, ℝ)) : ∫ x in Ω, matrixBilinearForm (a x) (∇ (φ : _ → ℝ) x)
      (W1p.gradient u x) ∂μ = ∫ x in Ω, f x * φ x ∂μ := by
    refine Eq.trans ?_ (hu φ)
    rw [energyFormH1_zero_zero_eq_setIntegral]
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := μ) 2 φ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx]
  refine ⟨w,g,(isWeakSolutionDirichlet_iff_forall_testFunction hcoeff _ _).2 ?_,hg,hwv,hwg⟩
  intro φ
  let K := tsupport φ ∩ tsupport ψ
  have hK : IsCompact K := φ.hasCompactSupport.inter_right (isClosed_tsupport ψ)
  have hKΩ : K ⊆ Ω := fun x hx => hts ⟨hx.2,φ.tsupport_subset hx.1⟩
  obtain ⟨χ,hχ,-,hχone,hχc,hχs⟩ := hK.exists_contDiff_cutoff Ω.isOpen hKΩ
  let θ : 𝓓(Ω, ℝ) := ⟨χ * φ,hχ.mul φ.contDiff,hχc.mul_right,tsupport_mul_subset_left.trans hχs⟩
  have hθ : (θ : EuclideanSpace ℝ ι → ℝ) = χ * φ := rfl
  have hχ1 (x : EuclideanSpace ℝ ι) (hx : x ∈ K) :
      (θ : EuclideanSpace ℝ ι → ℝ) =ᶠ[𝓝 x] (φ : EuclideanSpace ℝ ι → ℝ) := by
    filter_upwards [mem_interior_iff_mem_nhds.1 (hχone hx)] with y hy
    have hy' : χ y = 1 := Set.mem_singleton_iff.1 hy
    simp [hθ,hy']
  have hzero {x : EuclideanSpace ℝ ι} (hx : x ∉ tsupport φ) :
      (θ : EuclideanSpace ℝ ι → ℝ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
    simp [hθ,hy]
  have hHΩ : (H : Set (EuclideanSpace ℝ ι)) ∩ Ω = Ω := inter_eq_right.2 hsub
  change energyFormH1 a 0 0 (w : W1p μ H 2) (W1p.ofTestFunctionₗ μ H 2 φ) = _
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc
    _ = ∫ x in H, (Ω : Set (EuclideanSpace ℝ ι)).indicator
        (fun y => matrixBilinearForm (a y) (∇ (θ : _ → ℝ) y)
          (ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y)) x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := μ) 2 φ, hwg] with x hφ hweak
      rw [W1p.gradient_ofTestFunctionₗ,hφ,hweak]
      by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ ι))
      · rw [indicator_of_mem hxΩ,indicator_of_mem hxΩ]
        by_cases hxψ : x ∈ tsupport ψ
        · by_cases hxφ : x ∈ tsupport φ
          · rw [(hχ1 x ⟨hxφ,hxψ⟩).gradient_eq]
          · rw [(hzero hxφ).gradient_eq,gradient_of_notMem_tsupport hxφ]
            simp
        · simp [image_eq_zero_of_notMem_tsupport hxψ,gradient_of_notMem_tsupport hxψ]
      · rw [indicator_of_notMem hxΩ,indicator_of_notMem hxΩ,map_zero]
    _ = ∫ x in Ω, F x * θ x ∂μ := by
      rw [setIntegral_indicator hΩ,hHΩ]
      exact setIntegral_localized_eq ha hu' hψ θ
    _ = ∫ x in H, g x * φ x ∂μ := by
      rw [← hHΩ,← setIntegral_indicator hΩ]
      refine integral_congr_ae ?_
      filter_upwards [hg] with x hx
      rw [hx]
      by_cases hxΩ : x ∈ (Ω : Set (EuclideanSpace ℝ ι))
      · rw [indicator_of_mem hxΩ,indicator_of_mem hxΩ]
        by_cases hxψ : x ∈ tsupport ψ
        · by_cases hxφ : x ∈ tsupport φ
          · rw [(hχ1 x ⟨hxφ,hxψ⟩).eq_of_nhds]
          · rw [(hzero hxφ).eq_of_nhds,image_eq_zero_of_notMem_tsupport hxφ]
            rfl
        · simp [F,locForcing_eq_zero_of_notMem_tsupport ha hψ f u hxψ]
      · rw [indicator_of_notMem hxΩ,indicator_of_notMem hxΩ,zero_mul]

end TauCeti.PDE
