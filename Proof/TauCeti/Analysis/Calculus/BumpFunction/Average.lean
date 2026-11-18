/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

 























public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 

private def normedBumpAverage (phi : ContDiffBump (0 : E))
    (mu : Measure E) (T : E → F ≃ₗᵢ[ℝ] F) (f : F) : F :=
  ∫ t, phi.normed mu t • T (-t) f ∂mu

private theorem integrable_normed_smul_neg (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (T : E → F ≃ₗᵢ[ℝ] F) (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    Integrable (fun t ↦ phi.normed mu t • T (-t) f) mu :=
  (phi.continuous_normed.smul ((hT f).comp continuous_neg)).integrable_of_hasCompactSupport
    phi.hasCompactSupport_normed.smul_right

private theorem normedBumpAverage_add (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (T : E → F ≃ₗᵢ[ℝ] F) (hT : ∀ f, Continuous fun h ↦ T h f) (f g : F) :
    normedBumpAverage phi mu T (f + g) =
      normedBumpAverage phi mu T f + normedBumpAverage phi mu T g := by
  simp only [normedBumpAverage, map_add, smul_add]
  exact integral_add (integrable_normed_smul_neg phi mu T hT f)
    (integrable_normed_smul_neg phi mu T hT g)

omit [BorelSpace E] in
private theorem normedBumpAverage_smul (phi : ContDiffBump (0 : E)) (mu : Measure E)
    (T : E → F ≃ₗᵢ[ℝ] F) (c : ℝ) (f : F) :
    normedBumpAverage phi mu T (c • f) = c • normedBumpAverage phi mu T f := by
  simp only [normedBumpAverage, map_smul, smul_comm _ c, integral_smul]

private theorem norm_normedBumpAverage_le (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → F ≃ₗᵢ[ℝ] F) (f : F) :
    ‖normedBumpAverage phi mu T f‖ ≤ ‖f‖ := by
  calc
    ‖normedBumpAverage phi mu T f‖ ≤ ∫ t, phi.normed mu t * ‖f‖ ∂mu :=
      norm_integral_le_of_norm_le (phi.integrable_normed.mul_const _) <| .of_forall fun t ↦ by
        rw [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t), (T (-t)).norm_map]
    _ = ‖f‖ := by rw [integral_mul_const, phi.integral_normed, one_mul]

 




def normedBumpAverageL (phi : ContDiffBump (0 : E)) (mu : Measure E)
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) : F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := normedBumpAverage phi mu T
      map_add' := normedBumpAverage_add phi mu T hT
      map_smul' := normedBumpAverage_smul phi mu T } 1
    fun f ↦ by rw [one_mul]; exact norm_normedBumpAverage_le phi mu T f

 
theorem normedBumpAverageL_apply (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    normedBumpAverageL phi mu T hT f = ∫ t, phi.normed mu t • T (-t) f ∂mu := by
  rfl

 
theorem map_normedBumpAverageL {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G]
    (A : F →L[ℝ] G) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    A (normedBumpAverageL phi mu T hT f) =
      ∫ t, phi.normed mu t • A (T (-t) f) ∂mu := by
  simp only [normedBumpAverageL_apply,
    ← A.integral_comp_comm (integrable_normed_smul_neg phi mu T hT f), map_smul]

 

theorem normedBumpAverageL_comm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace F] [CompleteSpace G]
    (A : F →L[ℝ] G) (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (T : E → F ≃ₗᵢ[ℝ] F) (T' : E → G ≃ₗᵢ[ℝ] G)
    (hT : ∀ f, Continuous fun h ↦ T h f) (hT' : ∀ g, Continuous fun h ↦ T' h g)
    (hA : ∀ h f, A (T h f) = T' h (A f)) (f : F) :
    A (normedBumpAverageL phi mu T hT f) = normedBumpAverageL phi mu T' hT' (A f) := by
  rw [map_normedBumpAverageL, normedBumpAverageL_apply]
  simp only [hA]

 
theorem norm_normedBumpAverageL_le_one (phi : ContDiffBump (0 : E))
    (mu : Measure E) [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) :
    ‖normedBumpAverageL phi mu T hT‖ ≤ 1 := by
  rw [normedBumpAverageL]
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

 

theorem tendsto_normedBumpAverageL [CompleteSpace F] {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (nhds 0))
    (mu : Measure E) [mu.IsAddHaarMeasure] (T : E → F ≃ₗᵢ[ℝ] F)
    (hT : ∀ f, Continuous fun h ↦ T h f) (f : F) :
    Tendsto (fun i ↦ normedBumpAverageL (phi i) mu T hT f) l (nhds (T 0 f)) := by
  simpa only [normedBumpAverageL_apply, convolution_lsmul, zero_sub] using
    ContDiffBump.convolution_tendsto_right_of_continuous (μ := mu) hphi (hT f) (0 : E)

end TauCeti
