import Proof.ParallelFirstSelfCompleteAdjointJet
import Proof.UniformEffectiveFirstLowEndpointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

structure FirstSelfLeadingLowBudget (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  eta : ℝ
  boundConstant : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  nonneg : 0 ≤ boundConstant
  bound : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ eta → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ b y,y ∈ Y → ‖P.firstCovariantCoordinateHalfL b y‖ ≤ boundConstant*ε/beta d.γ d.radius y

structure FirstSelfLeadingHighBudget (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  eta : ℝ
  boundConstant : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  nonneg : 0 ≤ boundConstant
  packet : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ eta → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ CB CS : ℝ,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,FirstSelfCompleteAdjointJetBound WF boundConstant

structure FirstSelfLeadingScalarBudget (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  boundConstant : ℝ
  nonneg : 0 ≤ boundConstant
  bound : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b y,y ∈ Y →
    |scalarPrincipalConnectionWeight d b y| ≤ boundConstant*ε

structure FirstSelfLeadingForwardBudget (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  eta : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  raw : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ eta → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ y,y ∈ Y → ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

/-- Small typed budget acquisition keeps large uniform interfaces out of
the downstream integral elaboration context. -/
theorem first_self_leading_low_budget {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    Nonempty (FirstSelfLeadingLowBudget Y Ω K ρ c₀ M Cj) := by
  obtain ⟨η,C,hη,hη1,hC,hData⟩ := uniform_effective_first_low_endpoint_data hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  exact ⟨⟨η,C,hη,hη1,hC,fun floor hf ε hε hSmall d hd CF CT P b y hy =>
    (hData floor hf ε hε hSmall d hd CF CT P b).2 y hy⟩⟩

theorem first_self_leading_high_budget {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    Nonempty (FirstSelfLeadingHighBudget Y Ω K ρ c₀ M Cj) := by
  obtain ⟨η,C,hη,hη1,hC,hData⟩ := uniform_complete_first_adjoint_covariant_higher hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  exact ⟨⟨η,C,hη,hη1,hC,hData⟩⟩

theorem first_self_leading_scalar_budget {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    Nonempty (FirstSelfLeadingScalarBudget Y Ω K ρ c₀ M Cj) := by
  obtain ⟨C,hC,hData⟩ := uniform_scalar_principal_connection_two_jets hY hΩ hm K ρ c₀ M Cj hK
  refine ⟨⟨C,hC,?_⟩⟩
  intro floor hf ε hε hε1 d hd b y hy
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  exact (((hData floor hf ε hε hε1 d hd b).2 y hy b b).1).trans
    (div_le_self (mul_nonneg hC hε) (one_le_pow₀ hβ))

theorem first_self_leading_forward_budget {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    Nonempty (FirstSelfLeadingForwardBudget Y Ω K ρ c₀ M Cj) := by
  obtain ⟨η,hη,hη1,hData⟩ := uniform_full_first_derivative_balanced_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  exact ⟨⟨η,hη,hη1,fun floor hf ε hε hSmall d hd CF CT P y hy b =>
    P.firstDerivativeCoordinate_balanced y (hData floor hf ε hε hSmall d hd CF CT P y hy) b⟩⟩

end ShrinkingSpheres.ParallelEnergy
