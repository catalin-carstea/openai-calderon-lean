import Proof.UniformPhysicalFirstSmoothAdjointHigher
import Proof.UniformFullFirstAdjointCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

structure PhysicalFirstCommutatorPacket {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (CB CS ε : ℝ) where
  adjointHigh : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  commLow : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  adjoint_smooth : ∀ i,ContDiffOn ℝ ∞ (adjointHigh i) Y
  adjoint_graph : ∀ i,∀ y ∈ Y,
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (adjointHigh i y)=
      (P.firstDerivativeHalfL y i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  adjoint_bound : ∀ i,∀ y ∈ Y,‖adjointHigh i y‖ ≤ CB*ε/beta d.γ d.radius y
  comm_graph : ∀ i j,∀ y ∈ Y,
    (P.firstDerivativeHalfL y i).adjoint.comp (P.firstDerivativeHigherL y j)-
      (P.firstDerivativeHalfL y j).comp (adjointHigh i y)=
        (commLow i j y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  comm_bound : ∀ i j,∀ y ∈ Y,‖commLow i j y‖ ≤ CS*(ε/beta d.γ d.radius y)^2

theorem uniform_physical_first_commutator_packet {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      Nonempty (PhysicalFirstCommutatorPacket P CB CS ε) := by
  classical
  have hAProduce := uniform_physical_first_derivative_smooth_adjoint_higher hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηA,CB,hηA,hηA1,hCB,hAData⟩ := hAProduce
  have hCProduce := uniform_full_first_derivative_adjoint_commutator hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CS,hηC,hηC1,hCS,hCData⟩ := hCProduce
  refine ⟨min ηA ηC,CB,CS,lt_min hηA hηC,(min_le_left _ _).trans hηA1,hCB,hCS,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨A,hA⟩ := hAData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  have hRows (i j : I) (y : X) (hy : y ∈ Y) :=
    (hCData floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P y hy).2 i j
      (A i y) ((hA i).2 y hy).1
  choose S hSG hSN using hRows
  refine ⟨{
    adjointHigh := A
    commLow := fun i j y => if hy : y ∈ Y then S i j y hy else 0
    adjoint_smooth := fun i => (hA i).1
    adjoint_graph := fun i y hy => ((hA i).2 y hy).1
    adjoint_bound := fun i y hy => ((hA i).2 y hy).2
    comm_graph := ?_
    comm_bound := ?_}⟩
  · intro i j y hy
    simpa only [dif_pos hy] using hSG i j y hy
  · intro i j y hy
    simpa only [dif_pos hy] using hSN i j y hy
end ShrinkingSpheres
