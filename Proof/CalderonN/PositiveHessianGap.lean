module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Normed.Module.FiniteDimension

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

@[expose] public section

/-! The quadratic lower bound adopts the Taylor argument in
`StrictWeightPrescribedMetricJets` from anisotropic-calderon-lean revision
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff

namespace CalderonN

/-- A vanishing value and first derivative and a strictly positive
Hessian give a quadratic lower bound on a smaller closed ball. -/
theorem exists_quadratic_lower_of_hessian_positive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U)
    {z0 : E} (h0U : z0 ∈ U) (hFzero : F z0 = 0) (hDFzero : fderiv ℝ F z0 = 0)
    (hpos : ∀ W : E, W ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) z0 W W) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ closedBall z0 r ⊆ U ∧
      ∀ z ∈ closedBall z0 r, c * ‖z - z0‖^2 ≤ F z := by
  let Q : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) z0
  have hQcontinuous : Continuous (fun W : E => Q W W) :=
    (Q.contDiff.clm_apply contDiff_id : ContDiff ℝ ∞ (fun W : E => Q W W)).continuous
  obtain ⟨m,hm,hSphere⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hQcontinuous.continuousOn (fun W hW => hpos W (by
      have hNorm : ‖W‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hW
      intro hZero
      simp only [hZero,norm_zero] at hNorm
      norm_num at hNorm))
  have hQlower (W : E) : m*‖W‖^2 ≤ Q W W := by
    by_cases hW : W = 0
    · subst W
      simp only [norm_zero,map_zero]
      norm_num
    have hNorm : 0 < ‖W‖ := norm_pos_iff.mpr hW
    let V : E := ‖W‖⁻¹ • W
    have hV : ‖V‖ = 1 := by
      simp only [V,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hNorm),
        inv_mul_cancel₀ hNorm.ne']
    have hVSphere : V ∈ sphere (0 : E) 1 := by
      simpa only [mem_sphere,dist_zero_right] using hV
    have hMin := hSphere V hVSphere
    have hBack : ‖W‖ • V = W := by
      simp only [V,smul_smul,mul_inv_cancel₀ hNorm.ne',one_smul]
    have hScale : Q W W = ‖W‖^2 * Q V V := by
      calc
        Q W W = Q (‖W‖ • V) (‖W‖ • V) := by rw [hBack]
        _ = ‖W‖^2 * Q V V := by
          simp only [map_smul,smul_apply,smul_eq_mul]
          ring
    rw [hScale,mul_comm m (‖W‖^2)]
    exact mul_le_mul_of_nonneg_left hMin (sq_nonneg ‖W‖)
  have hFDsmooth : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hFDDsmooth : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) U :=
    hFDsmooth.fderiv_of_isOpen hU (by simp)
  have hQAt : ContinuousAt (fderiv ℝ (fderiv ℝ F)) z0 :=
    hFDDsmooth.continuousOn.continuousAt (hU.mem_nhds h0U)
  have hNearQ : ∀ᶠ z in 𝓝 z0, ‖fderiv ℝ (fderiv ℝ F) z - Q‖ < m/2 := by
    have hBall : ball Q (m/2) ∈ 𝓝 (fderiv ℝ (fderiv ℝ F) z0) :=
      ball_mem_nhds Q (half_pos hm)
    filter_upwards [hQAt.preimage_mem_nhds hBall] with z hz
    have hdist : dist (fderiv ℝ (fderiv ℝ F) z) Q < m/2 := mem_ball.mp hz
    have hdistEq : dist (fderiv ℝ (fderiv ℝ F) z) Q =
        ‖fderiv ℝ (fderiv ℝ F) z-Q‖ :=
      _root_.dist_eq_norm_sub (E := E →L[ℝ] E →L[ℝ] ℝ)
        (fderiv ℝ (fderiv ℝ F) z) Q
    exact hdistEq ▸ hdist
  have hNear : {z : E | z ∈ U ∧ ‖fderiv ℝ (fderiv ℝ F) z - Q‖ < m/2} ∈ 𝓝 z0 := by
    filter_upwards [hU.mem_nhds h0U,hNearQ] with z hz hq
    exact ⟨hz,hq⟩
  obtain ⟨alpha,halpha,hRoom⟩ := Metric.mem_nhds_iff.mp hNear
  let r : ℝ := alpha/2
  have hr : 0 < r := half_pos halpha
  have hClosedRoom (z : E) (hz : z ∈ closedBall z0 r) :
      z ∈ U ∧ ‖fderiv ℝ (fderiv ℝ F) z - Q‖ < m/2 := by
    apply hRoom
    exact mem_ball.mpr ((mem_closedBall.mp hz).trans_lt (half_lt_self halpha))
  have hHessianLower (z : E) (hz : z ∈ closedBall z0 r) (W : E) :
      (m/2)*‖W‖^2 ≤ fderiv ℝ (fderiv ℝ F) z W W := by
    let Err : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) z - Q
    have hError : |fderiv ℝ (fderiv ℝ F) z W W - Q W W| ≤ ‖Err‖*‖W‖^2 := by
      calc
        _ = ‖Err W W‖ := by
          simp only [Err,sub_apply,Real.norm_eq_abs]
        _ ≤ ‖Err W‖*‖W‖ := (Err W).le_opNorm W
        _ ≤ (‖Err‖*‖W‖)*‖W‖ :=
          mul_le_mul_of_nonneg_right (Err.le_opNorm W) (norm_nonneg W)
        _ = ‖Err‖*‖W‖^2 := by ring
    have hErrorLower := neg_le_of_abs_le hError
    have hCompare : ‖Err‖*‖W‖^2 ≤ (m/2)*‖W‖^2 :=
      mul_le_mul_of_nonneg_right (hClosedRoom z hz).2.le (sq_nonneg ‖W‖)
    linarith only [hQlower W,hErrorLower,hCompare]
  have curveSecond : ∀ (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) (W : E) (t : ℝ),
      z0+t • W ∈ U →
      deriv (deriv (fun s : ℝ => f (z0+s • W))) t =
        fderiv ℝ (fderiv ℝ f) (z0+t • W) W W := by
    intro f hf W t htU
    let gamma : ℝ → E := fun s => z0+s • W
    have hGamma (s : ℝ) : HasDerivAt gamma W s := by
      simpa only [gamma,one_smul] using
        ((hasDerivAt_id' s).smul_const W).const_add z0
    have hNearGamma : ∀ᶠ s in 𝓝 t, gamma s ∈ U :=
      (hGamma t).continuousAt.preimage_mem_nhds (hU.mem_nhds htU)
    have hGerm : deriv (fun s : ℝ => f (gamma s)) =ᶠ[𝓝 t]
        (fun s : ℝ => fderiv ℝ f (gamma s) W) := by
      filter_upwards [hNearGamma] with s hs
      have hOuter : HasFDerivAt f (fderiv ℝ f (gamma s)) (gamma s) :=
        ((hf.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)).hasFDerivAt
      have hComp := HasFDerivAt.comp_hasDerivAt (f := gamma) (f' := W)
        (l := f) (l' := fderiv ℝ f (gamma s)) s hOuter (hGamma s)
      simpa only [Function.comp_def] using hComp.deriv
    have hDField : HasFDerivAt (fderiv ℝ f)
        (fderiv ℝ (fderiv ℝ f) (gamma t)) (gamma t) :=
      (((hf.fderiv_of_isOpen hU (m := ∞) (by simp)).contDiffAt
        (hU.mem_nhds htU)).differentiableAt (by simp)).hasFDerivAt
    have hFieldCurve := HasFDerivAt.comp_hasDerivAt (f := gamma) (f' := W)
      (l := fderiv ℝ f) (l' := fderiv ℝ (fderiv ℝ f) (gamma t)) t hDField (hGamma t)
    have hEval := hFieldCurve.clm_apply (hasDerivAt_const t W)
    calc
      deriv (deriv (fun s : ℝ => f (z0+s • W))) t =
          deriv (fun s : ℝ => fderiv ℝ f (gamma s) W) t := hGerm.deriv_eq
      _ = fderiv ℝ (fderiv ℝ f) (z0+t • W) W W := by
        simpa only [Function.comp_def,gamma,map_zero,add_zero] using hEval.deriv
  have hFunctionLower (z : E) (hz : z ∈ closedBall z0 r) :
      (m/4)*‖z-z0‖^2 ≤ F z := by
    let W : E := z-z0
    let gamma : ℝ → E := fun t => z0+t • W
    let h : ℝ → ℝ := fun t => F (gamma t)
    have hW : ‖W‖ ≤ r := by
      have hdist : dist z z0 ≤ r := mem_closedBall.mp hz
      rw [_root_.dist_eq_norm_sub] at hdist
      simpa only [W] using hdist
    have hGamma (t : ℝ) : HasDerivAt gamma W t := by
      simpa only [gamma,one_smul] using
        ((hasDerivAt_id' t).smul_const W).const_add z0
    have hSegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : gamma t ∈ closedBall z0 r := by
      apply mem_closedBall.mpr
      have hAbs : |t| = t := abs_of_nonneg ht.1
      have hNorm : ‖t • W‖ ≤ r := by
        rw [norm_smul,Real.norm_eq_abs,hAbs]
        exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg W)).trans (by
          simpa only [one_mul] using hW)
      rw [_root_.dist_eq_norm_sub]
      simpa only [gamma,add_sub_cancel_left] using hNorm
    have hMaps : MapsTo gamma (Icc (0 : ℝ) 1) U := fun t ht =>
      (hClosedRoom (gamma t) (hSegment t ht)).1
    have hGammaSmooth : ContDiff ℝ ∞ gamma :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hIcc : ContDiffOn ℝ 2 h (Icc (0 : ℝ) 1) :=
      (hF.comp hGammaSmooth.contDiffOn hMaps).of_le (by norm_num)
    have hSmoothCurve : ContDiffOn ℝ 2 h (uIcc (0 : ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using hIcc
    have hZero : h 0 = 0 := by
      simpa only [h,gamma,zero_smul,add_zero] using hFzero
    have hOuter0 : HasFDerivAt F (fderiv ℝ F z0) (gamma 0) := by
      have hAt : HasFDerivAt F (fderiv ℝ F z0) z0 :=
        ((hF.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasFDerivAt
      simpa only [gamma,zero_smul,add_zero] using hAt
    have hHasZero : HasDerivAt h 0 0 := by
      have hComp := HasFDerivAt.comp_hasDerivAt (f := gamma) (f' := W)
        (l := F) (l' := fderiv ℝ F z0) 0 hOuter0 (hGamma 0)
      simpa only [h,Function.comp_def,hDFzero,zero_apply] using hComp
    have hWithinZero : derivWithin h (uIcc (0 : ℝ) 1) 0 = 0 := by
      have hUnique : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
        (uniqueDiffOn_Icc zero_lt_one) 0 ⟨le_rfl,zero_le_one⟩
      have hWithin := hHasZero.hasDerivWithinAt.derivWithin hUnique
      simpa only [uIcc_of_le zero_le_one] using hWithin
    have hTaylorZero : taylorWithinEval h 1 (uIcc (0 : ℝ) 1) 0 1 = 0 := by
      rw [taylorWithinEval_succ]
      simp only [Nat.cast_zero,Nat.cast_one,Nat.factorial_zero,
        zero_add,one_mul,inv_one,sub_zero,pow_one,one_smul]
      rw [taylor_within_zero_eval,iteratedDerivWithin_one,hWithinZero,hZero]
      norm_num
    obtain ⟨t,ht,hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := h) (x₀ := (0 : ℝ)) (x := (1 : ℝ)) (n := 1) (by norm_num) hSmoothCurve
    have ht01 : t ∈ Ioo (0 : ℝ) 1 := by
      simpa only [uIoo_of_lt zero_lt_one] using ht
    have hPoint := hSegment t ⟨ht01.1.le,ht01.2.le⟩
    have hSecondAt : iteratedDeriv 2 h t =
        fderiv ℝ (fderiv ℝ F) (gamma t) W W := by
      simpa only [h,gamma,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
        curveSecond F hF W t (hMaps ⟨ht01.1.le,ht01.2.le⟩)
    have hOne : h 1 = F z := by
      change F (z0+(1 : ℝ) • W) = F z
      congr 1
      dsimp only [W]
      rw [one_smul]
      abel
    have hTaylorF : F z = fderiv ℝ (fderiv ℝ F) (gamma t) W W / 2 := by
      rw [hOne,hTaylorZero,hSecondAt] at hTaylor
      norm_num at hTaylor
      exact hTaylor
    have hLower := hHessianLower (gamma t) hPoint W
    change (m/4)*‖W‖^2 ≤ F z
    linarith only [hLower,hTaylorF]
  exact ⟨m/4, r, by positivity, hr, fun z hz => (hClosedRoom z hz).1, hFunctionLower⟩

end CalderonN
