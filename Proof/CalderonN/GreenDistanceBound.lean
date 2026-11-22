module

public import Proof.CalderonN.SeparatedClassicalSource
public import Proof.CalderonN.LocalGreenL2
public import Proof.CalderonN.LocalGreenPointwise
public import Proof.CalderonN.DilatedGreenBounds
import Mathlib.Tactic

public section

/-! The dimension-dependent local singularity bound for the actual
Dirichlet Green germ and its fixed-window scaling. -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology

namespace CalderonN
variable {n : ℕ}

theorem exists_Green_distance_bound_unit (hn : 3 ≤ n)
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n} (hg : SmoothMetric univ g)
    {G : X n × X n → ℝ} (hG : GreenGerm Ω g G)
    (hCover : closedBall (0 : X n) 1 ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedBall (0 : X n) (1/8),
      ∀ y ∈ closedBall (0 : X n) (1/8), x ≠ y → |G (x,y)| ≤ C * dist x y ^ (2 - (n : ℝ)) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨N, hN, hTest⟩ := exists_Green_separated_test_bound_of_classical_source hn hΩ hg hG hCover
    (separated_classical_source_estimate hn)
  exact exists_Green_distance_bound_of_offPoleL2 hΩ hg hG hCover (sq_nonneg N)
    (fun y hy x r hr hSub hSep =>
      (offPoleLocalL2_of_separated_test_bound hΩ hG hCover hN hTest y hy x r hr hSub hSep).2)

theorem exists_Green_distance_bound (hn : 3 ≤ n)
    {Ω : Set (X n)} (hΩ : IsOpen Ω) (h₀ : (0 : X n) ∈ Ω)
    {g : MetricField n} (hg : SmoothMetric univ g) {G : X n × X n → ℝ} (hG : GreenGerm Ω g G) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ x ∈ closedBall (0 : X n) ρ,
      ∀ y ∈ closedBall (0 : X n) ρ, x ≠ y → |G (x,y)| ≤ C * dist x y ^ (2 - (n : ℝ)) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨R,hR,hRsub⟩ := Metric.isOpen_iff.mp hΩ 0 h₀
  let lam := R/2
  have hlam : 0 < lam := half_pos hR
  let Ω' := {x : X n | lam • x ∈ Ω}
  have hΩ' : IsOpen Ω' := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X n)).continuous)
  have hCover : closedBall (0 : X n) 1 ⊆ Ω' := by
    intro x hx
    apply hRsub
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hlam.le).trans_lt
      (by rw [mul_one]; exact half_lt_self hR)
  have hg' : SmoothMetric univ (dilatedMetric g lam) :=
    by simpa only [Set.mem_univ, Set.ofPred_true] using smoothMetric_dilated hg lam
  have hG' : GreenGerm Ω' (dilatedMetric g lam) (dilatedGreen G lam) :=
    hG.dilated (by omega) hΩ
      ⟨fun i j => (hg.1 i j).mono (subset_univ _), fun x _ => hg.2 x (mem_univ _)⟩ hlam
  obtain ⟨C,hC,hBound⟩ := exists_Green_distance_bound_unit hn hΩ' hg' hG' hCover
  refine ⟨lam/8,C,by positivity,hC,fun x hx y hy hxy => ?_⟩
  let u := lam⁻¹ • x
  let v := lam⁻¹ • y
  have hux : lam • u = x := smul_inv_smul₀ hlam.ne' x
  have hvy : lam • v = y := smul_inv_smul₀ hlam.ne' y
  have hUV (t : X n) (ht : t ∈ closedBall (0 : X n) (lam/8)) :
      lam⁻¹ • t ∈ closedBall (0 : X n) (1/8) := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
    refine (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp ht) (inv_nonneg.mpr hlam.le)).trans_eq ?_
    rw [← mul_div_assoc, inv_mul_cancel₀ hlam.ne']
  have hne : u ≠ v := fun h => hxy (hux.symm.trans ((congrArg (lam • ·) h).trans hvy))
  have h := hBound u (hUV x hx) v (hUV y hy) hne
  have hd : dist x y = lam * dist u v := by
    rw [← hux, ← hvy]
    simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
  have hP := green_power_homothety (by omega : 2 ≤ n) hlam (d := dist u v) dist_nonneg
  rw [← hd] at hP
  change |lam^(n-2) * G (lam • u,lam • v)| ≤ C * dist u v ^ (2-(n:ℝ)) at h
  rw [hux,hvy,abs_mul,abs_of_nonneg (pow_nonneg hlam.le _),← hP] at h
  rw [show C * (lam^(n-2) * dist x y ^ (2-(n:ℝ))) =
      lam^(n-2) * (C * dist x y ^ (2-(n:ℝ))) by ring] at h
  exact le_of_mul_le_mul_left h (pow_pos hlam _)

theorem exists_eventually_dilatedGreen_distance_bound (hn : 3 ≤ n)
    {Ω : Set (X n)} (hΩ : IsOpen Ω) (h₀ : (0 : X n) ∈ Ω)
    {g : MetricField n} (hg : SmoothMetric univ g) {G : X n × X n → ℝ} (hG : GreenGerm Ω g G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ x ∈ closedBall (0 : X n) B, ∀ y ∈ closedBall (0 : X n) B,
        x ≠ y → |dilatedGreen G lam (x,y)| ≤ C * dist x y ^ (2 - (n : ℝ)) := by
  obtain ⟨ρ,C,hρ,hC,h⟩ := exists_Green_distance_bound hn hΩ h₀ hg hG
  exact ⟨C,hC,eventually_dilatedGreen_distance_bound hn hρ h⟩

end CalderonN
