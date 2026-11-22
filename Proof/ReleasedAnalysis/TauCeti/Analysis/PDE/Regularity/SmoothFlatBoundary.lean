/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Regularity.SmoothCutoff

import Mathlib.Tactic

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise NNReal Topology
open TauCeti

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
  {Ω H V : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c : ℝ}
  {ν : EuclideanSpace ℝ ι} {L : ℝ≥0}

/-- Localized second-order regularity of a zero-trace weak solution
on a flat part of an open boundary. -/
theorem exists_wkp_two_of_smoothCutoff
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c < ⟪x, ν⟫_ℝ)
    (hE : UniformlyEllipticOn Set.univ a lam Lam)
    (hL : LipschitzWith L fun x => matrixBilinearForm (a x))
    (hA : ContDiff ℝ ∞ a) (hAs : ContDiff ℝ ∞ fun x => matrixBilinearForm (a x))
    (hApos : ∀ x v, v ≠ 0 → 0 < matrixBilinearForm (a x) v v)
    (hΩH : Ω ≤ H) (hVΩ : V ≤ Ω) (hΩb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    {f : Lp ℝ 2 (μ.restrict Ω)} {u : W1p μ Ω 2}
    (hu : ∀ φ : 𝓓(Ω, ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ μ Ω 2 φ) =
        ∫ x in Ω, f x * φ x ∂μ)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hts : (tsupport ψ ∩ H) ⊆ (Ω : Set (EuclideanSpace ℝ ι)))
    {B : ℝ} (hB : 0 ≤ B) (hbψ : ∀ x ∈ Ω, |ψ x| ≤ B)
    (hbg : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ B)
    (hzero : W1p.contDiffSMul ψ hψ hB hbψ hbg u ∈ w1p0Submodule μ Ω 2)
    (hψ1 : ∀ x ∈ V, ψ x = 1) :
    ∃ U : Wkp μ V 2 2,
      (Wkp.value 2 U : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict V] (W1p.value u : EuclideanSpace ℝ ι → ℝ) := by
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (μ.restrict H) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) hE.upper_nonneg
      hA.continuous.aestronglyMeasurable aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ => hE.upper_bound (mem_univ x)) (by simp) (by simp)
  obtain ⟨w,g,hw,_,hwv,_⟩ :=
    exists_isWeakSolutionDirichlet_smoothCutoff hA hcoeff hΩH hΩb hu hψ hts hB hbψ hbg hzero
  obtain ⟨Z,hZ⟩ :=
    (hE.mono_set (subset_univ (H : Set (EuclideanSpace ℝ ι)))).exists_lowerOrder_eq_of_halfSpace
      hν hH hL.lipschitzOnWith hAs hApos hw
  let hVH := hVΩ.trans hΩH
  refine ⟨Wkp.restrictL hVH 2 Z,(Wkp.value_restrictL_ae hVH 2 Z).trans ?_⟩
  rw [← Wkp.value_firstOrder 1 Z]
  change (W1p.value (Wkp.lowerOrder 1 Z) : EuclideanSpace ℝ ι → ℝ) =ᵐ[μ.restrict V] _
  rw [hZ]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hVH hwv,
    ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
  rw [hx,indicator_of_mem (hVΩ hxV),hψ1 x hxV,one_mul]

end TauCeti.PDE
