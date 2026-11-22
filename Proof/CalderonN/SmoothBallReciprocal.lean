module

public import Proof.CalderonN.BallRegularity.NativeSmoothBallSobolev

import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-! A smooth representative of a reciprocal known to be positive on the
closed unit ball, with the quantitative first local jet. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
set_option maxHeartbeats 950000

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]

theorem exists_smoothBall_reciprocal (u : SmoothData dim) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ z ∈ closedBall (0 : X dim) 1, (1/2 : ℝ) ≤ u.1 z)
    (hD : ∀ z ∈ closedBall (0 : X dim) 1, ‖fderiv ℝ u.1 z‖ ≤ B) :
    ∃ v : SmoothData dim, EqOn v.1 (fun z => (u.1 z)⁻¹) (closedBall (0 : X dim) 1) ∧
      ∀ z ∈ closedBall (0 : X dim) 1, |v.1 z| ≤ 2 ∧ ‖fderiv ℝ v.1 z‖ ≤ 4*B := by
  let U : Set (X dim) := {z | 0 < u.1 z}
  have hU : IsOpen U := isOpen_lt continuous_const u.2.continuous
  have hBU : closedBall (0 : X dim) 1 ⊆ U := fun z hz => (by norm_num : (0 : ℝ) < 1/2).trans_le (hu z hz)
  have hInv : ContDiffOn ℝ ∞ (fun z => (u.1 z)⁻¹) U :=
    u.2.contDiffOn.inv fun z hz => (show 0 < u.1 z from hz).ne'
  obtain ⟨v,hv,_,V,hV,hBV,_,hEq⟩ := exists_contDiff_extension_near_compact hU
    (isCompact_closedBall (0 : X dim) 1) hBU hInv
  refine ⟨⟨v,hv⟩,fun z hz => hEq (hBV hz),?_⟩
  intro z hz
  have hz0 : 0 < u.1 z := hBU hz
  have hVeq : v =ᶠ[𝓝 z] fun z => (u.1 z)⁻¹ := by
    filter_upwards [hV.mem_nhds (hBV hz)] with w hw using hEq hw
  have hV : |v z| ≤ 2 := by
    rw [hVeq.eq_of_nhds,abs_of_pos (inv_pos.mpr hz0)]
    exact (inv_le_comm₀ hz0 (by norm_num : (0 : ℝ) < 2)).mpr (by simpa only [one_div] using hu z hz)
  have hL := ((hasFDerivAt_inv hz0.ne').comp z
    (u.2.differentiable (by simp) z).hasFDerivAt).fderiv
  refine ⟨hV,?_⟩
  change ‖fderiv ℝ v z‖ ≤ _
  rw [hVeq.fderiv_eq]
  change ‖fderiv ℝ ((fun x : ℝ => x⁻¹) ∘ u.1) z‖ ≤ _
  rw [hL]
  have hV' : ‖(ContinuousLinearMap.toSpanSingleton ℝ (-((u.1 z)^2)⁻¹))‖ ≤ (4 : ℝ) := by
    rw [ContinuousLinearMap.norm_toSpanSingleton,Real.norm_eq_abs,abs_neg,
      abs_of_pos (inv_pos.mpr (sq_pos_of_pos hz0))]
    have hh := (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) (hu z hz) 2)
    exact (inv_le_comm₀ (sq_pos_of_pos hz0) (by norm_num : (0 : ℝ) < 4)).mpr (by norm_num at hh ⊢; exact hh)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hV' (hD z hz) (norm_nonneg _) (by norm_num))

end CalderonN
