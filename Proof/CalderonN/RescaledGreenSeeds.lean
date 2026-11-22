module

public import Proof.CalderonN.RescaledProductJets
public import Proof.CalderonN.GreenDistanceBound
public import Proof.CalderonN.FixedTube.Initialization

import Proof.CalderonN.CrossProductWeak
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.FixedTube.DilatedGeometry
import Mathlib.Tactic

/-! Adapted from `RescaledGreenSeeds` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2300000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open FixedTube

theorem separateAffineChart_room_bounds
    {x y : (X dim)} (hx : ‖x‖ ≤ 3) (hy : ‖y‖ ≤ 3) {s : ℝ} (hs : 0 ≤ s) (hS : s ≤ 1/2)
    {q : (X dim) × (X dim)} (hq : q ∈ ball (0 : (X dim)) 2 ×ˢ ball (0 : (X dim)) 2) :
    let z := separateAffineChart x y s q
    ‖z.1‖ ≤ 4 ∧ ‖z.2‖ ≤ 4 ∧ dist x y ≤ dist z.1 z.2+4*s := by
  have hDev (u : (X dim)) (hu : u ∈ ball (0 : (X dim)) 2) : ‖s • u‖ ≤ 2*s := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
    simpa only [mul_comm s 2] using mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hu).le hs
  have h₁ (u c : (X dim)) (hu : u ∈ ball (0 : (X dim)) 2) (hc : ‖c‖ ≤ 3) : ‖c+s • u‖ ≤ 4 :=
    (norm_add_le _ _).trans (by linarith [hDev u hu])
  refine ⟨h₁ q.1 x hq.1 hx,h₁ q.2 y hq.2 hy,?_⟩
  change dist x y ≤ dist (x+s • q.1) (y+s • q.2)+4*s
  have hA : dist x (x+s • q.1) ≤ 2*s := by rw [dist_comm,dist_eq_norm,add_sub_cancel_left]; exact hDev q.1 hq.1
  have hB : dist (y+s • q.2) y ≤ 2*s := by rw [dist_eq_norm,add_sub_cancel_left]; exact hDev q.2 hq.2
  linarith [dist_triangle4 x (x+s • q.1) (y+s • q.2) y]

/-- A room of size proportional to the sphere radius stays uniformly
away from its pole after dilation. The lower seed is the first Green
germ and the upper seed is already bounded at fixed separation. -/
theorem exists_rescaledGreenSeed_jet_bounds (hn : 3 ≤ dim)
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) (h₀ : (0 : (X dim)) ∈ Ω)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {G₁ : (X dim) × (X dim) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁)
    {c d R : ℝ} (hc : 0 < c) (hd : 0 < d) (hR : 0 < R) {M : ℝ} (hM : 0 ≤ M)
    (n : ℕ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
      ∀ x y : (X dim), ‖x‖ ≤ 3 → ‖y‖ ≤ 3 → ∀ r ∈ Ioc 0 R,
      ∀ G : (X dim) × (X dim) → ℝ,
      ((c*r ≤ dist x y ∧ G =ᶠ[𝓝 (x,y)] dilatedGreen G₁ lam) ∨
        (d ≤ dist x y ∧ ∃ (O : Set ((X dim) × (X dim))) (F : (X dim) × (X dim) → ℝ),
          IsOpen O ∧ fixedSeparationSet 4 (d/2) ⊆ O ∧
          ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O F ∧
          (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ M) ∧ G =ᶠ[𝓝 (x,y)] F)) →
      ∃ H : (X dim) × (X dim) → ℝ, ContDiff ℝ ∞ H ∧
        H =ᶠ[𝓝 0] (fun q => r^(dim-2) * G (separateAffineChart x y (η*r) q)) ∧
        ∀ k ≤ n, ‖iteratedFDeriv ℝ k H 0‖ ≤ C := by
  let η := min (c/8) (min (1/(2*R)) (d/(8*R)))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hηc : 4*η ≤ c/2 := by linarith [min_le_left (c/8) (min (1/(2*R)) (d/(8*R)))]
  have hηR : η*R ≤ 1/2 := by
    have hi : η ≤ 1/(2*R) := (min_le_right _ _).trans (min_le_left _ _)
    have he : (1/(2*R))*R = 1/2 := by field_simp
    exact (mul_le_mul_of_nonneg_right hi hR.le).trans_eq he
  have hηd : 4*(η*R) ≤ d/2 := by
    have hi : η ≤ d/(8*R) := (min_le_right _ _).trans (min_le_right _ _)
    have h := mul_le_mul_of_nonneg_right hi hR.le
    have he : (d/(8*R))*R = d/8 := by field_simp
    rw [he] at h
    linarith
  obtain ⟨A,hA,hLowerBound⟩ := exists_eventually_dilatedGreen_distance_bound hn hΩ h₀ hg₁ hG₁
  obtain ⟨L,hL,hLowerJet⟩ := exists_uniform_rescaled_product_jets hg₁ hg₁ 3 (1/2) n
  obtain ⟨U,hU,hUpperJet⟩ := exists_uniform_rescaled_product_jets hg₁ hg₂ 3 (1/2) n
  have hChart : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ x ∈ closedBall (0 : (X dim)) 4, lam • x ∈ Ω := by
    apply (isCompact_closedBall (0 : (X dim)) 4).eventually_forall_of_forall_eventually
    intro x _
    have ht : ContinuousAt (fun q : ℝ × (X dim) => q.1 • q.2) (0,x) :=
      (continuous_fst.smul continuous_snd).continuousAt
    exact ht.preimage_mem_nhds (by simpa only [zero_smul] using hΩ.mem_nhds h₀)
  have hNear : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  refine ⟨η,max (L*(A * (c/2)^(2-(dim:ℝ)))) (U*(R^(dim-2)*M)),hη,le_max_of_le_left (by positivity),?_⟩
  filter_upwards [hChart,hNear,hLowerBound 4] with lam hChart hLam hLow hpos
  intro x y hx hy r hr G hG
  have hrpos : 0 < r := hr.1
  let s := η*r
  have hs : 0 ≤ s := mul_nonneg hη.le hr.1.le
  have hSR : s ≤ η*R := mul_le_mul_of_nonneg_left hr.2 hη.le
  have hS : s ≤ 1/2 := hSR.trans hηR
  let W := ball (0 : (X dim)) 2 ×ˢ ball (0 : (X dim)) 2
  let f := separateAffineChart x y s
  have hf : Continuous f := (contDiff_separateAffineChart _ _ _).continuous
  have hf₀ : f 0 = (x,y) := by simp [f,separateAffineChart,affineChartMap]
  have heq (F : (X dim) × (X dim) → ℝ) (he : G =ᶠ[𝓝 (x,y)] F) :
      (fun q => r^(dim-2) * F (f q)) =ᶠ[𝓝 0] fun q => r^(dim-2) * G (f q) := by
    have ht : Tendsto f (𝓝 0) (𝓝 (x,y)) := hf₀ ▸ hf.continuousAt.tendsto
    exact (he.comp_tendsto ht).symm.mono (fun q h => congrArg (r^(dim-2) * ·) h)
  rcases hG with ⟨hSep,hEq⟩ | ⟨hSep,O,F,hO,hOut,hF,hMb,hEq⟩
  · let T : Set (X dim) := {z | lam • z ∈ Ω}
    have hT : IsOpen T := hΩ.preimage (lam • ContinuousLinearMap.id ℝ (X dim)).continuous
    have hMetric : SmoothMetric T (dilatedMetric g₁ lam) :=
      smoothMetric_restrict (smoothMetric_dilatedMetric hg₁ lam) (subset_univ T)
    have hF := (hG₁.dilated (by omega : 2 ≤ dim) hΩ (smoothMetric_restrict hg₁ (subset_univ Ω)) hpos).productSolution hT hMetric
    have hRoom (q : (X dim) × (X dim)) (hq : q ∈ W) :
        ‖(f q).1‖ ≤ 4 ∧ ‖(f q).2‖ ≤ 4 ∧ c*r/2 ≤ dist (f q).1 (f q).2 := by
      obtain ⟨h₁,h₂,h₃⟩ := separateAffineChart_room_bounds hx hy hs hS hq
      have hSM : 4*s ≤ (c/2)*r := by
        dsimp only [s]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hηc hr.1.le
      exact ⟨h₁,h₂,by linarith⟩
    have hMap : MapsTo f W (OffDiagonal T) := by
      intro q hq
      obtain ⟨h₁,h₂,h₃⟩ := hRoom q hq
      exact ⟨hChart _ (mem_closedBall_zero_iff.mpr h₁),hChart _ (mem_closedBall_zero_iff.mpr h₂),
        dist_pos.mp ((by positivity : 0 < c*r/2).trans_le h₃)⟩
    have hBound (q : (X dim) × (X dim)) (hq : q ∈ W) :
        |r^(dim-2) * dilatedGreen G₁ lam (f q)| ≤ A * (c/2)^(2-(dim:ℝ)) := by
      obtain ⟨h₁,h₂,h₃⟩ := hRoom q hq
      have hrC : 0 < c*r/2 := by positivity
      have hposD : 0 < dist (f q).1 (f q).2 := hrC.trans_le h₃
      have he : (2 : ℝ) - (dim : ℝ) ≤ 0 := by exact sub_nonpos.mpr (by exact_mod_cast (show 2 ≤ dim by omega))
      rw [abs_mul,abs_of_nonneg (pow_nonneg hr.1.le _)]
      calc
        _ ≤ r^(dim-2)*(A * dist (f q).1 (f q).2 ^ (2-(dim:ℝ))) :=
          mul_le_mul_of_nonneg_left (hLow hpos _ (mem_closedBall_zero_iff.mpr h₁) _
            (mem_closedBall_zero_iff.mpr h₂) (dist_pos.mp hposD)) (pow_nonneg hr.1.le _)
        _ ≤ r^(dim-2)*(A * (c*r/2) ^ (2-(dim:ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hrC h₃ he) hA) (pow_nonneg hr.1.le _)
        _ = A * (c/2)^(2-(dim:ℝ)) := by
          rw [show c*r/2 = r*(c/2) by ring, mul_left_comm,
            green_power_homothety (by omega : 2 ≤ dim) hr.1 (by positivity)]
    obtain ⟨H,hH,hE,hJ⟩ := hLowerJet lam hLam x (mem_closedBall_zero_iff.mpr hx)
      y (mem_closedBall_zero_iff.mpr hy) s ⟨hs,hS⟩ (r^(dim-2)) (isOpen_offDiagonal hT) hMap hF
      (A * (c/2)^(2-(dim:ℝ))) (by positivity) hBound
    exact ⟨H,hH,hE.trans (heq _ hEq),fun k hk => (hJ k hk).trans (le_max_left _ _)⟩
  · have hRoom (q : (X dim) × (X dim)) (hq : q ∈ W) : f q ∈ fixedSeparationSet 4 (d/2) := by
      obtain ⟨h₁,h₂,h₃⟩ := separateAffineChart_room_bounds hx hy hs hS hq
      have hSM := (mul_le_mul_of_nonneg_left hSR (by norm_num : (0:ℝ) ≤ 4)).trans hηd
      exact ⟨h₁,h₂,by rw [← dist_eq_norm]; linarith⟩
    have hMap : MapsTo f W O := fun q hq => hOut (hRoom q hq)
    have hBound (q : (X dim) × (X dim)) (hq : q ∈ W) : |r^(dim-2) * F (f q)| ≤ R^(dim-2)*M := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg hr.1.le _)]
      exact mul_le_mul (pow_le_pow_left₀ hr.1.le hr.2 _) (hMb _ (hRoom q hq))
        (abs_nonneg _) (pow_nonneg hR.le _)
    obtain ⟨H,hH,hE,hJ⟩ := hUpperJet lam hLam x (mem_closedBall_zero_iff.mpr hx)
      y (mem_closedBall_zero_iff.mpr hy) s ⟨hs,hS⟩ (r^(dim-2)) hO hMap hF (R^(dim-2)*M) (by positivity) hBound
    exact ⟨H,hH,hE.trans (heq _ hEq),fun k hk => (hJ k hk).trans (le_max_right _ _)⟩

end CalderonN
