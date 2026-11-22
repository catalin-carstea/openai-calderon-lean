module

public import Proof.CalderonN.Chart
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

public section

open Set Metric
open scoped ContDiff RealInnerProductSpace

namespace CalderonPatch

open CalderonN (ContainsSmoothSide X)

variable {n : ℕ}

/-- An open matched set has an interior ball touching its complement
inside the coordinate chart at any chart-interior frontier. -/
theorem exists_touchingBall {V A : Set (X n)} (hV : IsOpen V) (hA : IsOpen A)
    {z : X n} (hzV : z ∈ V) (hz : z ∈ closure A) (hzA : z ∉ A) :
    ∃ (c : X n) (r : ℝ) (p : X n), c ∈ A ∧ 0 < r ∧ p ∈ V ∧ p ∉ A ∧
      dist p c = r ∧ closedBall c r ⊆ V ∧ ball c r ⊆ A := by
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV z hzV
  obtain ⟨c, hc, hzc⟩ := Metric.mem_closure_iff.mp hz (R / 3) (by positivity)
  have hne : Aᶜ.Nonempty := ⟨z, hzA⟩
  let r := infDist c Aᶜ
  have hr : 0 < r := (infDist_pos_iff_notMem_closure hne).1 (by
    rw [(isClosed_compl_iff.mpr hA).closure_eq]
    exact fun h => h hc)
  have hrR : r < R / 3 := (infDist_le_dist_of_mem (show z ∈ Aᶜ from hzA)).trans_lt
    (dist_comm z c ▸ hzc)
  obtain ⟨p, hp, hpr⟩ := (isClosed_compl_iff.mpr hA).exists_infDist_eq_dist hne c
  have hclosed : closedBall c r ⊆ V := by
    intro x hx
    apply hRV
    rw [mem_ball]
    have hxc : dist x c ≤ r := hx
    have hcz : dist c z < R / 3 := by simpa only [dist_comm c z] using hzc
    exact (dist_triangle x c z).trans_lt (by linarith)
  have hp' : dist p c = r := by simpa only [dist_comm p c] using hpr.symm
  refine ⟨c, r, p, hc, hr, hclosed hp'.le, hp, hp', hclosed, ?_⟩
  intro x hx
  by_contra h
  have hle : r ≤ dist c x := infDist_le_dist_of_mem h
  have hlt : dist x c < r := hx
  exact (not_lt_of_ge hle) (dist_comm x c ▸ hlt)

/-- The squared distance to the center defines the known side of a
touching ball after translating the contact point to the origin. -/
theorem containsSmoothSide_of_ball {Ω W : Set (X n)} (hΩ : IsOpen Ω)
    (h₀ : (0 : X n) ∈ Ω) {c : X n} {r : ℝ} (hr : 0 < r) (hc : ‖c‖ = r)
    (hball : ball c r ⊆ W) : ContainsSmoothSide Ω W := by
  let s (x : X n) := ‖x - c‖ ^ 2 - r ^ 2
  have hs : ContDiff ℝ ∞ s :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const
  have hs₀ : s 0 = 0 := by simp [s, hc]
  have hshift : HasFDerivAt (fun x : X n => x - c)
      (ContinuousLinearMap.id ℝ (X n)) 0 := (hasFDerivAt_id 0).sub_const c
  have hD : fderiv ℝ s 0 = 2 • innerSL ℝ (-c) := by
    simpa only [s, zero_sub, ContinuousLinearMap.comp_id] using
      (hshift.norm_sq.sub_const (r ^ 2)).fderiv
  refine ⟨Ω, s, hΩ, h₀, Subset.rfl, hs.contDiffOn, hs₀, ?_, ?_⟩
  · intro hzero
    have hEval := congrArg (fun L : X n →L[ℝ] ℝ => L (-c)) (hD.symm.trans hzero)
    have hsq : ‖c‖ ^ 2 = r ^ 2 := by rw [hc]
    simp only [two_nsmul, add_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      norm_neg, hsq, zero_apply] at hEval
    nlinarith [sq_pos_of_pos hr]
  · intro x hx
    apply hball
    rw [mem_ball, dist_eq_norm]
    have hlt : ‖x - c‖ ^ 2 < r ^ 2 := sub_neg.mp hx.2
    exact lt_of_not_ge fun h => (not_lt_of_ge (pow_le_pow_left₀ hr.le h 2)) hlt

end CalderonPatch
