module

public import Proof.CalderonN.NormalizedMetric
public import Proof.CalderonN.Radius

import Proof.CalderonN.Bootstrap
import Proof.CalderonN.SmallJetBounds
import Proof.CalderonN.PrincipalMetric
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

public section

open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Choose the fixed splitting radius before taking the final spatial dilation. -/
theorem exists_split_radius {C ε ρ₀ : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hρ₀ : 0 < ρ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₀ ∧ C * Real.sqrt ρ ≤ ε / 2 := by
  let q := ε / (2 * (C + 1))
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨min (ρ₀ / 2) (q ^ 2), lt_min (by positivity) (by positivity),
    (min_le_left _ _).trans_lt (by linarith), ?_⟩
  calc
    _ ≤ C * Real.sqrt (q ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (min_le_right _ _)) hC
    _ = C * q := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
    _ ≤ (C + 1) * q := mul_le_mul_of_nonneg_right (by linarith) hq.le
    _ = ε / 2 := by dsimp [q]; field_simp

theorem half_bound_of_superlinear_or_fixed {H r C ρ ε : ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hρ : C * Real.sqrt ρ ≤ ε / 2)
    (hsmall : r < ρ → H ≤ C * r ^ (3 / 2 : ℝ))
    (hlarge : ρ ≤ r → H ≤ ε / 2 * ρ) :
    H ≤ ε / 2 * r := by
  by_cases hrρ : r < ρ
  · have hp : r ^ (3 / 2 : ℝ) = r * Real.sqrt r := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hr,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    calc
      H ≤ C * (r * Real.sqrt r) := hp ▸ hsmall hrρ
      _ = (C * Real.sqrt r) * r := by ring
      _ ≤ ε / 2 * r := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrρ.le) hC).trans hρ) hr.le
  · exact (hlarge (le_of_not_gt hrρ)).trans
      (mul_le_mul_of_nonneg_left (le_of_not_gt hrρ) (by positivity))

private theorem continuousOn_smallJet {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {γ g : MetricField dim} (hγ : SmoothMetric Ω γ) (hg : SmoothMetric Ω g) :
    ContinuousOn (smallJet γ g) Ω := by
  unfold smallJet
  refine continuousOn_finsetSum _ fun a _ => ContinuousOn.sqrt ?_
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  have hF : ContDiffOn ℝ ∞ (fun x => (principal γ g x - (γ x)⁻¹) i j) Ω :=
    (contDiffOn_principal_entry hγ hg i j).sub (contDiffOn_metric_inv_entry hγ i j)
  exact (contDiffOn_chartPartial hΩ hF (fun k => (a k).val)).continuousOn.pow 2

/-- Conditional end of the shrinking argument. The metric fields are fixed
throughout the argument. The analytic producer supplies the strict gain
for the same radii and jets appearing in the initial bound. -/
theorem normalized_eq_inv_of_half_improvement
    {Ω K : Set (X dim)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {γ g : (MetricField dim)} (hγ : SmoothMetric Ω γ) (hg : SmoothMetric Ω g)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) {p : ℕ} (hp : p ≠ 0)
    {depth : (X dim) → ℝ} (hdepth : ContinuousOn depth K)
    (hinitial : ∀ y ∈ K, smallJet γ g y ≤ ε * shrinkingRadius R p depth 1 y)
    (himprove : ∀ δ ∈ Ioc (0 : ℝ) 1,
      (∀ y ∈ K, smallJet γ g y ≤ ε * shrinkingRadius R p depth δ y) →
      ∀ y ∈ K, smallJet γ g y ≤ ε / 2 * shrinkingRadius R p depth δ y) :
    EqOn (principal γ g) (fun y => (γ y)⁻¹) {y ∈ K | depth y ≤ 0} := by
  have hall := shrinking_bounds hK hε ((continuousOn_smallJet hΩ hγ hg).mono hKΩ)
    (shrinkingRadius_continuousOn R p hdepth)
    (fun δ hδ y _ => shrinkingRadius_pos hR hδ.1 p depth y) hinitial himprove
  intro y hy
  have hnonneg : 0 ≤ smallJet γ g y := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hzero := eq_zero_of_shrinking_bound hnonneg
    (shrinkingRadius_tendsto_zero R hp hy.2) (fun δ hδ => hall δ hδ y hy.1)
  ext i j
  have hi := abs_principal_sub_inverse_entry_le_smallJet γ g y i j
  rw [hzero, abs_nonpos_iff] at hi
  exact sub_eq_zero.mp hi

end CalderonN
