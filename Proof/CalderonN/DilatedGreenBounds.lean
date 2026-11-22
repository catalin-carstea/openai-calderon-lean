module

public import Proof.CalderonN.GreenDilation
public import Proof.CalderonN.GreenCross

import Mathlib.Tactic

public section

/-! The normalization and fixed-window bounds of the original
`DilatedGreenBounds`, with the distance power for ambient dimension `n`. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace CalderonN
variable {n : ℕ}

/-- Homogeneity of the distance power under the volume normalization. -/
theorem green_power_homothety (hn : 2 ≤ n) {lam d : ℝ} (hlam : 0 < lam) (hd : 0 ≤ d) :
    lam ^ (n-2) * (lam * d) ^ (2-(n:ℝ)) = d ^ (2-(n:ℝ)) := by
  have hcast : ((n-2 : ℕ) : ℝ) = (n : ℝ)-2 := by rw [Nat.cast_sub hn, Nat.cast_ofNat]
  rw [← Real.rpow_natCast, hcast, Real.mul_rpow hlam.le hd, ← mul_assoc, ← Real.rpow_add hlam,
    sub_add_sub_cancel, sub_self, Real.rpow_zero, one_mul]

/-- The volume-normalized Green scaling makes the local estimate uniform
on each fixed coordinate window. -/
theorem eventually_dilatedGreen_distance_bound (hn : 3 ≤ n)
    {G : X n × X n → ℝ} {ρ C : ℝ} (hρ : 0 < ρ)
    (h : ∀ x ∈ closedBall (0 : X n) ρ, ∀ y ∈ closedBall (0 : X n) ρ,
      x ≠ y → |G (x,y)| ≤ C * dist x y ^ (2 - (n : ℝ))) :
    ∀ B : ℝ, ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ x ∈ closedBall (0 : X n) B, ∀ y ∈ closedBall (0 : X n) B,
        x ≠ y → |dilatedGreen G lam (x,y)| ≤ C * dist x y ^ (2 - (n : ℝ)) := by
  intro B
  let K := closedBall (0 : X n) B
  have hI : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ x ∈ K, lam • x ∈ ball (0 : X n) ρ := by
    apply (isCompact_closedBall (0 : X n) B).eventually_forall_of_forall_eventually
    intro x _
    have hF : Continuous (fun p : ℝ × X n => p.1 • p.2) := continuous_fst.smul continuous_snd
    exact hF.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (by simpa only [zero_smul] using mem_ball_self hρ))
  filter_upwards [hI] with lam hLam hp x hx y hy hxy
  have hne : lam • x ≠ lam • y := by
    intro he
    apply hxy
    simpa only [inv_smul_smul₀ hp.ne'] using congrArg (fun z : X n => lam⁻¹ • z) he
  have hD : dist (lam • x) (lam • y) = lam * dist x y := by
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
  have hpow : 0 ≤ lam ^ (n-2) := pow_nonneg hp.le _
  rw [dilatedGreen, abs_mul, abs_of_nonneg hpow]
  refine (mul_le_mul_of_nonneg_left
    (h _ (ball_subset_closedBall (hLam x hx)) _ (ball_subset_closedBall (hLam y hy)) hne) hpow).trans_eq ?_
  rw [hD]
  calc
    _ = C * (lam ^ (n-2) * (lam * dist x y) ^ (2-(n:ℝ))) := by ring
    _ = _ := by rw [green_power_homothety (by omega : 2 ≤ n) hp dist_nonneg]


/-- The two prescribed Green pieces before continuation. -/
def dilatedInitialGreen (W : Set (X n)) (G₁ G₂ : X n × X n → ℝ) (lam : ℝ) : X n × X n → ℝ :=
  initialGreenKernel {x | lam • x ∈ W} (dilatedGreen G₁ lam) (dilatedGreen G₂ lam)

theorem dilatedInitialGreen_eq_left {W : Set (X n)} (G₁ G₂ : X n × X n → ℝ)
    {lam : ℝ} {p : X n × X n} (hy : lam • p.2 ∈ W) :
    dilatedInitialGreen W G₁ G₂ lam p = dilatedGreen G₁ lam p :=
  initialGreenKernel_eq_left _ _ hy

/-- The normalized mixed seed solves the two harmonic equations on the
dilated cross, with the asserted agreement on their overlap. -/
theorem dilatedInitialGreen_productSolution [NeZero n] (hn : 2 ≤ n)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) {g₁ g₂ : MetricField n}
    (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    {G₁ G₂ : X n × X n → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {lam : ℝ} (hlam : 0 < lam) :
    ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam)
      (knownCross {x | lam • x ∈ Ω} {x | lam • x ∈ W})
      (dilatedInitialGreen W G₁ G₂ lam) := by
  have hc : Continuous (fun x : X n => lam • x) := (lam • ContinuousLinearMap.id ℝ (X n)).continuous
  apply initialGreenKernel_productSolution (hΩ.preimage hc) (hW.preimage hc)
    (smoothMetric_dilated hg₁ lam) (smoothMetric_dilated hg₂ lam)
    (hG₁.dilated hn hΩ hg₁ hlam) (hG₂.dilated hn hΩ hg₂ hlam)
  · exact fun _ hx => hmetric hx
  · intro q hq
    refine congrArg (fun v : ℝ => lam ^ (n-2) * v)
      (hgreen (x := (lam • q.1, lam • q.2)) ⟨hq.1, hq.2.1, ?_⟩)
    intro h
    apply hq.2.2
    simpa only [inv_smul_smul₀ hlam.ne'] using congrArg (fun z : X n => lam⁻¹ • z) h

theorem eventually_dilatedInitialGreen_distance_bound (hn : 3 ≤ n)
    {W : Set (X n)} {G₁ G₂ : X n × X n → ℝ} {ρ₁ ρ₂ C₁ C₂ : ℝ}
    (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂)
    (hG₁ : ∀ x ∈ closedBall (0 : X n) ρ₁, ∀ y ∈ closedBall (0 : X n) ρ₁,
      x ≠ y → |G₁ (x,y)| ≤ C₁ * dist x y ^ (2 - (n : ℝ)))
    (hG₂ : ∀ x ∈ closedBall (0 : X n) ρ₂, ∀ y ∈ closedBall (0 : X n) ρ₂,
      x ≠ y → |G₂ (x,y)| ≤ C₂ * dist x y ^ (2 - (n : ℝ))) :
    ∀ B : ℝ, ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ x ∈ closedBall (0 : X n) B, ∀ y ∈ closedBall (0 : X n) B,
        x ≠ y → |dilatedInitialGreen W G₁ G₂ lam (x,y)| ≤
          max C₁ C₂ * dist x y ^ (2 - (n : ℝ)) := by
  intro B
  filter_upwards [eventually_dilatedGreen_distance_bound hn h₁ hG₁ B,
    eventually_dilatedGreen_distance_bound hn h₂ hG₂ B] with lam hd₁ hd₂ hp x hx y hy hxy
  have hd : 0 ≤ dist x y ^ (2 - (n : ℝ)) := Real.rpow_nonneg dist_nonneg _
  unfold dilatedInitialGreen initialGreenKernel
  split_ifs
  · exact (hd₁ hp x hx y hy hxy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
  · exact (hd₂ hp x hx y hy hxy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd)

end CalderonN
