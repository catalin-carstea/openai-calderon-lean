module

public import Proof.CalderonN.FixedBallWeakConormalFamilyJets

import Mathlib.Tactic

/-! The weak conormal Taylor budget on the actual relative-radius
coefficient germs, with the named affine coefficient. -/

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency true
namespace CalderonN

open BallDirichlet TauCeti PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

structure ActualRelativeWeakConormalGerm (d : Data dim) (y : X dim) (N : ℕ) (C : ℝ) where
  first : X dim × ℝ → FixedBallEnergyOperator dim
  second : X dim × ℝ → FixedBallEnergyOperator dim
  neighborhood : Set (X dim × ℝ)
  openNeighborhood : IsOpen neighborhood
  center_mem : (y,0) ∈ neighborhood
  first_eq : ∀ p ∈ neighborhood, ∀ u v : FixedBallH1 dim, first p u v =
    energyFormH1 (fun z => actualRelativeCoefficientFirst d (p,z)) 0 0 u v
  energy_eq : ∀ p ∈ neighborhood, ∀ u v : FixedBallH1 dim,
    (fixedBallFlatEnergyL dim+d.radius y • first p+(d.radius y)^2 • second p) u v =
      energyFormH1 (fun z => actualFramedCoefficientField d
        (actualRelativeCoefficientInput (d.radius y) (p,z))) 0 0 u v
  inverseNear : ∀ p ∈ neighborhood, (weakEnergyZeroOperatorL (fixedBallZeroInclusionL dim)
    (fixedBallFlatEnergyL dim+d.radius y • first p+(d.radius y)^2 • second p)).IsInvertible
  remainderBound : LocalSmoothJetBudget (fun p => fixedBallWeakConormalTaylor
    (d.radius y) (first p) (second p)) (y,0) N (C*(d.radius y)^2)

theorem uniform_actual_relativeWeakConormal_taylor (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, Nonempty (ActualRelativeWeakConormalGerm d y N C) := by
  have h0 := @uniform_actual_relativeWeakEnergy_germ dim ‹NeZero dim› hn Y Ω hY hΩ hYc
    m N hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,D,hη,hD,hEnergy⟩ := h0
  obtain ⟨δ,C,hδ,hC,hTaylor⟩ := exists_fixedBall_weakConormal_family_jet_budget (dim:=dim) (P:=X dim × ℝ)
    N D hD
  refine ⟨min η δ,C,lt_min hη hδ,hC,?_⟩
  intro floor hf ε he hs d hd hdFrame y hy
  let r := d.radius y
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hb := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans (hd.2.2.2.2.2 y hy).2
  have hrδ : r ∈ Icc (0:ℝ) δ := ⟨hr.le,hrε.trans (hs.trans (min_le_right _ _))⟩
  obtain ⟨E₁,E₂,V,hV,hxV,hFirst,hActual,hE₁,hE₂⟩ :=
    hEnergy floor hf ε he (hs.trans (min_le_left _ _)) d hd hdFrame y hy
  obtain ⟨hNear,hJets⟩ := hTaylor r hrδ (y,0) E₁ E₂ hE₁ hE₂
  obtain ⟨W,hWsub,hW,hW₀⟩ := mem_nhds_iff.mp hNear
  exact ⟨⟨E₁,E₂,V ∩ W,hV.inter hW,⟨hxV,hW₀⟩,fun p hp => hFirst p hp.1,
    fun p hp => hActual p hp.1,fun p hp => hWsub hp.2,hJets⟩⟩

end CalderonN
