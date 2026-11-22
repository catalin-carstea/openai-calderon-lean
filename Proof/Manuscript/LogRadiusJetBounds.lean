module

public import Proof.CalderonN.RadiusProfileGeometry

import Proof.CalderonN.SoftplusComposition
import Mathlib.Tactic

public section

/-! Extracted from `Proof/CalderonN/ProfileBounds.lean` at the checked
release revision `4d97dc89403377fef662b4643360b2ec01be1460`. The argument
is kept at arbitrary finite order for the standalone profile lemma. -/

noncomputable section
open Set Filter
open scoped BigOperators ContDiff Topology
open CalderonN SoftplusProfile

namespace CalderonPaper

variable {dim : ℕ}

/-! The scalar-to-Fréchet bound follows the derivative budget in
`Calderon/ProfileFrechetJets.lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc. -/
private theorem norm_iteratedFDeriv_log_shrinkingRadius_le
    {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth) (x : (X dim)) {R δ B D : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) {p : ℕ} (hp : 1 ≤ p)
    {n : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hD : 0 ≤ D) (hBa : 1 ≤ B * logSlope δ (depth x))
    (hDt : ∀ k : ℕ, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k depth x‖ ≤ D ^ k) :
    ‖iteratedFDeriv ℝ n (fun y => Real.log (shrinkingRadius R p depth δ y)) x‖ ≤
      (n.factorial : ℝ) * SoftplusProfile.profileJetBoundSum n * (B * D) ^ n *
        ((p : ℝ) * logSlope δ (depth x)) ^ n := by
  let f := fun y => Real.log (softplus δ (depth y))
  have hf : ContDiff ℝ ∞ f := (SoftplusProfile.contDiff_scalar_log_softplus δ hδ).comp ht
  have he : (fun y => Real.log (shrinkingRadius R p depth δ y)) =
      (fun _ => Real.log R) + fun y => (p : ℝ) * f y := by
    funext y
    simp only [Pi.add_apply, f, shrinkingRadius,
      Real.log_mul hR.ne' (pow_ne_zero _ (softplus_pos hδ (depth y)).ne'), Real.log_pow]
  rw [he, iteratedFDeriv_add_apply contDiffAt_const ((contDiff_const.mul hf).of_le (by simp)).contDiffAt,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
  have hscale : iteratedFDeriv ℝ n (fun y => (p : ℝ) * f y) x =
      (p : ℝ) • iteratedFDeriv ℝ n f x := by
    exact iteratedFDeriv_const_smul_apply' (a := (p : ℝ)) (i := n) (x := x)
      ((hf.of_le (by simp)).contDiffAt)
  rw [hscale, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg p)]
  have hbase := SoftplusProfile.norm_iteratedFDeriv_log_softplus_comp_le
    depth ht n hn δ hδ x B D hB hBa hDt
  have h := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg p)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ n := le_self_pow₀ hpR (by omega)
  have ha : 0 ≤ logSlope δ (depth x) := (SoftplusProfile.logSlope_pos δ _ hδ).le
  have hBS := SoftplusProfile.profileJetBoundSum_nonneg n
  have hr := mul_le_mul_of_nonneg_right hpPow
    (show 0 ≤ (n.factorial : ℝ) * SoftplusProfile.profileJetBoundSum n *
      (B * logSlope δ (depth x)) ^ n * D ^ n by positivity)
  convert h.trans hr using 1
  simp only [mul_pow]
  ring

private theorem exists_uniform_depth_jet_bound {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth)
    {K : Set (X dim)} (hK : IsCompact K) (N : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ k : ℕ, 1 ≤ k → k ≤ N → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k depth x‖ ≤ D ^ k := by
  let S (x : (X dim)) := ∑ i ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ i depth x‖
  have hS : Continuous S :=
    continuous_finsetSum _ fun _ _ => (ht.continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max A 1, le_max_right _ _, fun k hk hkn x hx => ?_⟩
  have hsingle : ‖iteratedFDeriv ℝ k depth x‖ ≤ S x := by
    exact Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
      (f := fun j => ‖iteratedFDeriv ℝ j depth x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  exact hsingle.trans ((le_abs_self _).trans ((hA x hx).trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right _ _) (by omega)))))

theorem exists_log_radius_jet_bounds
    {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth) {K : Set (X dim)} (hK : IsCompact K)
    {N : ℕ} {m : ℝ} (hm : 0 < m) {T : ℝ} (hT : ∀ y ∈ K, depth y ≤ T) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ {y : (X dim)}, y ∈ K → ∀ (γ : (MetricField dim)),
      m ≤ Real.sqrt (covectorSq γ depth y) → ∀ {R δ : ℝ}, 0 < R → δ ∈ Ioc (0 : ℝ) 1 →
      ∀ {p : ℕ}, 1 ≤ p → ∀ k : ℕ, 1 ≤ k → k ≤ N →
        ‖iteratedFDeriv ℝ k (fun z => Real.log (shrinkingRadius R p depth δ z)) y‖ ≤
          J * (beta γ (shrinkingRadius R p depth δ) y)^k := by
  obtain ⟨D, hD, hDt⟩ := exists_uniform_depth_jet_bound ht hK N
  let B := 1 + Real.log (1 + Real.exp T)
  have hB : 1 ≤ B := le_add_of_nonneg_right (SoftplusProfile.log_exp_add_one_pos T).le
  let C (k : ℕ) :=
    (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D / m)^k
  have hC (k : ℕ) : 0 ≤ C k := by
    have hS := SoftplusProfile.profileJetBoundSum_nonneg k
    dsimp only [C]
    positivity
  let J := ∑ k ∈ Finset.range (N + 1), C k
  refine ⟨J, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro y hy γ hcov R δ hR hδ p hp k hk hkn
  have ha := (SoftplusProfile.logSlope_pos δ (depth y) hδ.1).le
  have hBa : 1 ≤ B * logSlope δ (depth y) :=
    (div_le_iff₀ (zero_lt_one.trans_le hB)).mp
      (SoftplusProfile.logSlope_uniform_lower_bound δ (depth y) T hδ.1 hδ.2 (hT y hy))
      |>.trans_eq (mul_comm _ _)
  let a := (p : ℝ) * logSlope δ (depth y)
  have ha' : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) ha
  let b := beta γ (shrinkingRadius R p depth δ) y
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hab : a ≤ b / m := by
    apply (le_div_iff₀ hm).2
    change a * m ≤ beta γ (shrinkingRadius R p depth δ) y
    rw [beta_shrinkingRadius (ht.differentiable (by simp) y) hR hδ.1]
    exact mul_le_mul_of_nonneg_left hcov ha'
  have hJ : C k ≤ J :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
  have hF := norm_iteratedFDeriv_log_shrinkingRadius_le ht y hR hδ.1 hp hk hB
    (zero_le_one.trans hD) hBa (fun i hi hik => hDt i hi (hik.trans hkn) y hy)
  have hscale :
      (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D)^k * (b / m)^k =
        C k * b^k := by
    dsimp only [C]
    simp only [div_eq_mul_inv, mul_pow]
    ring
  calc
    _ ≤ (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D)^k * a^k := hF
    _ ≤ (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D)^k * (b / m)^k := by
      have hS := SoftplusProfile.profileJetBoundSum_nonneg k
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha' hab k) (by positivity)
    _ = C k * b^k := hscale
    _ ≤ J * b^k := mul_le_mul_of_nonneg_right hJ (pow_nonneg hb _)

end CalderonPaper
