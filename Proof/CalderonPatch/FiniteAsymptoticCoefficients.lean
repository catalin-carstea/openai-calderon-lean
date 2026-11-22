module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

import Mathlib.Tactic

public section
noncomputable section
open Filter Finset Set
open scoped Topology

namespace CalderonPatch

/-- A finite power expansion bounded by (O(h^N)) for positive (h)
has all coefficients of orders below (N) equal to zero. -/
theorem finite_power_coefficient_eq_zero {N : ℕ} {C : ℝ} {a : ℕ → ℝ}
    (hB : ∀ h : ℝ, 0 < h → h ≤ 1 → |∑ j ∈ range (N+1), h ^ j * a j| ≤ C * h ^ N) :
    ∀ k < N, a k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k hk =>
    intro hkN
    let S := (range (N+1)).filter (k ≤ ·)
    let P (h : ℝ) := ∑ j ∈ S, h ^ (j-k) * a j
    have hP : Continuous P :=
      continuous_finsetSum _ (fun j _ => (continuous_id.pow _).mul continuous_const)
    have hFactor (h : ℝ) :
        h ^ k * P h = ∑ j ∈ range (N+1), h ^ j * a j := by
      dsimp only [P,S]
      rw [Finset.mul_sum,sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hkj : k ≤ j
      · rw [ite_eq_left hkj,← mul_assoc,← pow_add,Nat.add_sub_of_le hkj]
      · rw [ite_eq_right hkj,hk j (Nat.lt_of_not_ge hkj) ((Nat.lt_of_not_ge hkj).trans hkN),mul_zero]
    have hLe (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) : |P h| ≤ C * h ^ (N-k) := by
      have hBound := hB h hh hh₁
      have he : h ^ N = h ^ k * h ^ (N-k) := by rw [← pow_add,Nat.add_sub_of_le hkN.le]
      rw [← hFactor,abs_mul,abs_of_nonneg (pow_nonneg hh.le _),he,
        mul_left_comm C] at hBound
      exact le_of_mul_le_mul_left hBound (pow_pos hh _)
    let F : Filter ℝ := 𝓝[>] (0 : ℝ)
    have : F.NeBot := by dsimp [F]; infer_instance
    have h0 : Tendsto (fun h : ℝ => |P h|) F (𝓝 |P 0|) :=
      (hP.abs.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun h : ℝ => C * h ^ (N-k)) F (𝓝 (C * (0 : ℝ) ^ (N-k))) :=
      ((continuous_const.mul (continuous_id.pow (N-k))).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hEv : ∀ᶠ h : ℝ in F, |P h| ≤ C * h ^ (N-k) := by
      have hSmall : Iio (1 : ℝ) ∈ F := nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
      filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)), hSmall] with h ha hb
      exact hLe h ha (le_of_lt hb)
    have hZ := le_of_tendsto_of_tendsto h0 h1 hEv
    have hN : N-k ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hkN)
    rw [zero_pow hN,mul_zero,abs_nonpos_iff] at hZ
    have hVal : P 0 = a k := by
      unfold P
      rw [sum_eq_single k]
      · simp
      · intro j hj hjne
        have hjk : k < j := lt_of_le_of_ne (mem_filter.mp hj).2 (Ne.symm hjne)
        rw [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hjk)),zero_mul]
      · intro h
        exact (h (mem_filter.mpr ⟨mem_range.mpr (hkN.trans (Nat.lt_succ_self N)),le_rfl⟩)).elim
    exact hVal.symm.trans hZ

end CalderonPatch
