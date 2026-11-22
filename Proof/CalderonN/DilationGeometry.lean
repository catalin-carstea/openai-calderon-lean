module

public import Proof.CalderonN.Chart

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Set Filter
open scoped Topology

namespace CalderonN

variable {n : ℕ}

/-- Every compact set in the strict negative tangent half-space maps
into the known side under all sufficiently small positive dilations. -/
theorem eventually_dilated_subset_of_negative_tangent
    {V W K : Set (X n)} (hV : IsOpen V) (h₀ : (0 : (X n)) ∈ V) (hK : IsCompact K)
    {s : (X n) → ℝ} (hs : DifferentiableAt ℝ s 0) (hs₀ : s 0 = 0)
    (hside : {x ∈ V | s x < 0} ⊆ W)
    (hnegative : ∀ y ∈ K, fderiv ℝ s 0 y < 0) :
    ∀ᶠ lam in 𝓝[Ioi (0 : ℝ)] 0, ∀ y ∈ K, lam • y ∈ W := by
  let D := fderiv ℝ s (0 : (X n))
  obtain ⟨c, hc, hlower⟩ := hK.exists_forall_le' (a := (0 : ℝ))
    D.continuous.neg.continuousOn (fun y hy => neg_pos.mpr (hnegative y hy))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let L := max M 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  let e := c / (2 * L)
  have he : 0 < e := by dsimp [e]; positivity
  have herror : ∀ᶠ x in 𝓝 (0 : (X n)), |s x - D x| ≤ e * ‖x‖ := by
    simpa only [hs₀, sub_zero, Real.norm_eq_abs, D] using hs.hasFDerivAt.isLittleO.def he
  have hnear : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K,
      lam • y ∈ V ∧ |s (lam • y) - D (lam • y)| ≤ e * ‖lam • y‖ := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have hcont : ContinuousAt (fun q : ℝ × (X n) => q.1 • q.2) ((0 : ℝ), y) :=
      (continuous_fst.smul continuous_snd).continuousAt
    have hsmul : Tendsto (fun q : ℝ × (X n) => q.1 • q.2) (𝓝 ((0 : ℝ), y)) (𝓝 0) := by
      simpa only [zero_smul] using hcont.tendsto
    have hV' : ∀ᶠ x in 𝓝 (0 : (X n)), x ∈ V := hV.mem_nhds h₀
    exact hsmul.eventually (hV'.and herror)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear, eventually_mem_nhdsWithin]
    with lam hlam hpos y hy
  obtain ⟨hmem, hrem⟩ := hlam y hy
  have hlampos : 0 < lam := hpos
  have hbound : ‖y‖ ≤ L := (hM y hy).trans (le_max_left _ _)
  have heL : e * L = c / 2 := by dsimp [e]; field_simp [hL.ne']
  have hem : e * ‖y‖ ≤ c / 2 := heL ▸ mul_le_mul_of_nonneg_left hbound he.le
  have hfirst : s (lam • y) - lam * D y ≤ lam * (c / 2) := by
    calc
      _ ≤ |s (lam • y) - lam * D y| := le_abs_self _
      _ ≤ e * (lam * ‖y‖) := by
        simpa only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hlampos] using hrem
      _ = lam * (e * ‖y‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hem hlampos.le
  have hlinear : lam * D y ≤ -(lam * c) := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (le_neg.mp (hlower y hy)) hlampos.le
  exact hside ⟨hmem, by linarith [mul_pos hlampos hc]⟩

end CalderonN
