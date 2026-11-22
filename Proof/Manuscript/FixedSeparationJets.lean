module

public import Proof.CalderonN.RescaledProductJets
public import Proof.CalderonN.FixedTube.Initialization

import Proof.CalderonN.ScaledRadiusJetBudget
import Mathlib.Tactic

public section

open CalderonN CalderonN.FixedTube Set Filter Metric
open scoped Topology

namespace CalderonPaper

variable {n : ℕ} [NeZero n]

/-- A fixed smaller separated range has a common nonzero rectangle scale.
The affine-chain-rule loss is independent of the spatial dilation. -/
theorem exists_fixedSeparation_jetBound
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {B d : ℝ} (hd : 0 < d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ lam ∈ Icc (-1 : ℝ) 1, ∀ {O : Set ((X n) × (X n))}, IsOpen O →
      fixedSeparationSet (B+2) (d/2) ⊆ O →
      ∀ {F : (X n) × (X n) → ℝ},
        ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O F →
      ∀ M : ℝ, 0 ≤ M → (∀ q ∈ fixedSeparationSet (B+2) (d/2), |F q| ≤ M) →
      ∀ k ≤ m, ∀ q ∈ fixedSeparationSet (B+1) (3*d/4), ‖iteratedFDeriv ℝ k F q‖ ≤ C*M := by
  let s := min (1/8 : ℝ) (d/32)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have hs₁ : s ≤ 1/8 := min_le_left _ _
  have hs₂ : s ≤ d/32 := min_le_right _ _
  have hsn : s ≤ 1 := hs₁.trans (by norm_num)
  obtain ⟨C₀, hC₀, hC⟩ := exists_uniform_rescaled_product_jets hg₁ hg₂ (B+1) s m
  refine ⟨C₀ / s^m, div_nonneg hC₀ (pow_nonneg hs.le _), ?_⟩
  intro lam hlam O hO hBig F hF M hM hFbound k hk q hq
  let qmap := separateAffineChart q.1 q.2 s
  have hAffine (v : (X n) × (X n)) : qmap v = q + s • v := rfl
  have hroom : MapsTo qmap (ball (0 : X n) 2 ×ˢ ball (0 : X n) 2)
      (fixedSeparationSet (B+2) (d/2)) := by
    intro v hv
    have hbound (i : X n) (hi : i ∈ ball (0 : X n) 2) : ‖s • i‖ ≤ 2*s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_comm 2 s]
      exact mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hi).le hs.le
    have hq₁ : ‖q.1‖ ≤ B+1 := hq.1
    have hq₂ : ‖q.2‖ ≤ B+1 := hq.2.1
    have hsep : 3*d/4 ≤ ‖q.1-q.2‖ := hq.2.2
    have hv₁ := hbound v.1 hv.1
    have hv₂ := hbound v.2 hv.2
    have hx : ‖q.1+s • v.1‖ ≤ B+2 := (norm_add_le _ _).trans (by linarith)
    have hy : ‖q.2+s • v.2‖ ≤ B+2 := (norm_add_le _ _).trans (by linarith)
    have htri : dist q.1 q.2 ≤ dist q.1 (q.1+s • v.1) +
        dist (q.1+s • v.1) (q.2+s • v.2) + dist (q.2+s • v.2) q.2 :=
      dist_triangle4 _ _ _ _
    have hr₁ : dist q.1 (q.1+s • v.1) = ‖s • v.1‖ := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
    have hr₂ : dist (q.2+s • v.2) q.2 = ‖s • v.2‖ := by
      rw [dist_eq_norm, add_sub_cancel_left]
    rw [hr₁, hr₂, dist_eq_norm, dist_eq_norm] at htri
    refine ⟨hx, hy, ?_⟩
    change d/2 ≤ ‖q.1+s • v.1-(q.2+s • v.2)‖
    linarith
  obtain ⟨H, hH, hEq, hJ⟩ := hC lam hlam q.1 (mem_closedBall_zero_iff.mpr hq.1)
    q.2 (mem_closedBall_zero_iff.mpr hq.2.1) s ⟨hs.le, le_rfl⟩ 1 hO
    (hroom.mono_right hBig) hF M hM
    (fun v hv => by simpa only [one_mul] using hFbound _ (hroom hv))
  have hEq' : H =ᶠ[𝓝 0] (fun v => F (q + s • v)) :=
    hEq.mono (fun v hv => by simpa only [one_mul, ← hAffine] using hv)
  have hjet := (hEq'.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds
  have hscaled := hJ k hk
  rw [hjet, norm_iteratedFDeriv_affine_scale F q 0 s hs.ne', abs_of_pos hs,
    smul_zero, add_zero] at hscaled
  have hpower : s^m ≤ s^k := pow_le_pow_of_le_one hs.le hsn hk
  have hres : s^m * ‖iteratedFDeriv ℝ k F q‖ ≤ C₀*M :=
    (mul_le_mul_of_nonneg_right hpower (norm_nonneg _)).trans hscaled
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (pow_pos hs _)).2 (by simpa only [mul_comm] using hres)

end CalderonPaper
