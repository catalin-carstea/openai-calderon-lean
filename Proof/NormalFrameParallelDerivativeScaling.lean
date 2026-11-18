import Proof.FrameRadiusParameterJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace ShrinkingSpheres

/-- The derivative along the parallel-center curve is linear in the center
velocity, although the genuine coefficient extension is shared and fixed. -/
theorem deriv_normalFrame_parallel_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (e : Frame) (r : X → ℝ) (y : X)
    (H : NormalFrameParameter → E)
    (hH : DifferentiableAt ℝ H (y,(r y,frameVectorLinear e y))) (a : X) (c : ℝ) :
    deriv (fun t => H (normalFrameParallelCurve g e r y (c • a) t)) 0 =
      c • deriv (fun t => H (normalFrameParallelCurve g e r y a t)) 0 := by
  have hHa : HasFDerivAt H (fderiv ℝ H (y,(r y,frameVectorLinear e y)))
      (normalFrameParallelCurve g e r y a 0) := by
    rw [normalFrameParallelCurve_zero];exact hH.hasFDerivAt
  have hHc : HasFDerivAt H (fderiv ℝ H (y,(r y,frameVectorLinear e y)))
      (normalFrameParallelCurve g e r y (c • a) 0) := by
    rw [normalFrameParallelCurve_zero];exact hH.hasFDerivAt
  change deriv (H ∘ normalFrameParallelCurve g e r y (c • a)) 0 =
    c • deriv (H ∘ normalFrameParallelCurve g e r y a) 0
  rw [(hHc.comp_hasDerivAt 0 (hasDerivAt_normalFrameParallelCurve g e r y (c • a))).deriv,
    (hHa.comp_hasDerivAt 0 (hasDerivAt_normalFrameParallelCurve g e r y a)).deriv]
  rw [← map_smul]
  congr 1
  simp only [Prod.smul_mk,smul_zero,map_smul,ContinuousLinearMap.smul_comp,smul_neg]

/-- A bound for all unit center velocities controls every velocity with
exactly one norm factor. No bound on the frame derivative is used. -/
theorem norm_deriv_normalFrame_parallel_le_of_unit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : MetricField) (e : Frame) (r : X → ℝ) (y : X)
    (H : NormalFrameParameter → E)
    (hH : DifferentiableAt ℝ H (y,(r y,frameVectorLinear e y)))
    (C : ℝ) (hUnit : ∀ a : X,‖a‖ ≤ 1 →
      ‖deriv (fun t => H (normalFrameParallelCurve g e r y a t)) 0‖ ≤ C)
    (a : X) :
    ‖deriv (fun t => H (normalFrameParallelCurve g e r y a t)) 0‖ ≤ C*‖a‖ := by
  by_cases ha : a = 0
  · subst a
    have hZero := deriv_normalFrame_parallel_smul g e r y H hH (0:X) (0:ℝ)
    simpa only [zero_smul,norm_zero,mul_zero] using le_of_eq (congrArg norm hZero)
  · have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    let u : X := ‖a‖⁻¹ • a
    have hu : ‖u‖ ≤ 1 := by
      dsimp only [u]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a)),inv_mul_cancel₀ hna]
    have hau : ‖a‖ • u = a := by
      dsimp only [u]
      rw [smul_smul,mul_inv_cancel₀ hna,one_smul]
    have hScale := deriv_normalFrame_parallel_smul g e r y H hH u ‖a‖
    rw [hau] at hScale
    rw [hScale,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg a)]
    exact (mul_le_mul_of_nonneg_left (hUnit u hu) (norm_nonneg a)).trans_eq (mul_comm _ _)

end ShrinkingSpheres
