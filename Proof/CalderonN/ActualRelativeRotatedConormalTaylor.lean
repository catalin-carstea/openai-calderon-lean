module

public import Proof.CalderonN.ActualRelativeRotatedWeakEnergy
public import Proof.CalderonN.FixedBallWeakRotatedTaylorBudget

import Mathlib.Tactic

/-! Quadratic joint Taylor bounds for the weak form of the genuine
conormal rotation commutator. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency true
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

structure ActualRelativeRotatedConormalGerm (d : Data dim) (y : X dim) (N : ℕ) (C : ℝ) where
  budget : ℝ
  energy : ActualRelativeRotatedWeakEnergyGerm d y N budget
  remainderBound : ∀ i j : I dim, LocalSmoothJetBudget (fun p => fixedBallWeakConormalRotatedTaylor
    (d.radius y) (energy.first p) (energy.second p) (energy.rotFirst i j p) (energy.rotSecond i j p))
    (y,0) N (C*(d.radius y)^2)

theorem uniform_actual_relativeRotatedConormal_taylor (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, Nonempty (ActualRelativeRotatedConormalGerm d y N C) := by
  obtain ⟨η,B,hη,hB,hG⟩ := uniform_actual_relativeRotatedWeakEnergy_germ hn hY hΩ hYc
    N hm K ρ c₀ M Cj hK hρ
  obtain ⟨δ,C,hδ,hC,hR⟩ := exists_fixedBall_rotatedWeakConormal_family_jet_budget (dim:=dim) N B hB
  refine ⟨min η δ,C,lt_min hη hδ,hC,?_⟩
  intro floor hf ε he hs d hd hF y hy
  obtain ⟨G⟩ := hG floor hf ε he (hs.trans (min_le_left _ _)) d hd hF y hy
  let r := d.radius y
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hb := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans (hd.2.2.2.2.2 y hy).2
  have hrδ : r ∈ Icc (0:ℝ) δ := ⟨hr.le,hrε.trans (hs.trans (min_le_right _ _))⟩
  exact ⟨⟨B,G,fun i j => hR r hrδ (y,0) G.first G.second (G.rotFirst i j) (G.rotSecond i j)
    G.firstBound G.secondBound (G.rotFirstBound i j) (G.rotSecondBound i j)⟩⟩

end CalderonN
