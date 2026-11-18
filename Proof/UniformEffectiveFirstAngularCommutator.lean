import Proof.EffectiveFirstScalarDriftCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def EffectiveFirstAngularCommutatorGraph {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} (W : PhysicalFirstCommutatorPacket P CB CS ε)
    (K : ℝ) (y : X) (b c : I) : Prop :=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
          (P.firstCovariantCoordinateHigherL c y)=
            (P.firstCovariantCoordinateHalfL c y).comp
              (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        (P.firstCovariantCoordinateHalfL b y).adjoint.comp (P.firstCovariantCoordinateHigherL c y)-
          (P.firstCovariantCoordinateHalfL c y).comp (W.covariantCoordinateAdjointHigher b y)=
            (W.coordinateCommLow b c y).comp
              (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖W.coordinateCommLow b c y‖ ≤ (9*K^2*CS)*(ε/beta d.γ d.radius y)^2

/-- Closed actual effective-first angular commutator production. The
SAME packet supplies its adjoint row and commutator; the scalar connection
drift cancels exactly and the original epsilon/beta squared norm survives. -/
theorem uniform_effective_first_angular_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : PhysicalFirstCommutatorPacket P CB CS ε,∀ y ∈ Y,∀ b c : I,
        EffectiveFirstAngularCommutatorGraph W K y b c := by
  have hWProduce := uniform_physical_first_commutator_packet hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηW,CB,CS,hηW,hηW1,hCB,hCS,hPacket⟩ := hWProduce
  have hBProduce := uniform_full_first_derivative_balanced_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,hηB,hηB1,hBalanced⟩ := hBProduce
  refine ⟨min ηW ηB,CB,CS,lt_min hηW hηB,(min_le_left _ _).trans hηW1,hCB,hCS,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W⟩ := hPacket floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  refine ⟨W,?_⟩
  intro y hy b c
  have hRaw := P.firstDerivativeCoordinate_balanced y
    (hBalanced floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P y hy) c
  exact ⟨P.firstCovariantCoordinateHigherL_balanced c y hRaw,
    W.covariantCoordinateCommLow_graph b c hy hRaw,W.norm_coordinateCommLow_le hd hK b c hy⟩

end ShrinkingSpheres
