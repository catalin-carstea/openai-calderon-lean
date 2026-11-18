import Proof.ParallelScalarFirstCompletePacket
import Proof.PhysicalScalarCoreDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete genuine forward two-jet packet uses the SAME WF and
arbitrary compatible baseline higher endpoint. Every family precedes tests. -/
theorem uniform_effective_first_forward_strong_half_two_jets_of_correction
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hCorrection : CorrectionStrongHalfTwoJetBound Y Ω K ρ c₀ M Cj) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ CB CS : ℝ,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      Nonempty (EffectiveFirstForwardStrongHalfTwoJets WF C) := by
  classical
  obtain ⟨ηC,C,hηC,hηC1,hC,hCoarse⟩ :=
    uniform_effective_first_coarse_strong_half_two_jets_of_correction hY hΩ hSub hm K ρ c₀ M Cj hK hρ hCorrection
  obtain ⟨ηB,CB,hηB,hηB1,hCB,hBalanced⟩ :=
    uniform_effective_first_covariant_balanced hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,hηF,hηF1,hForward⟩ :=
    uniform_full_first_derivative_balanced_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηC (min ηB ηF),C,lt_min hηC (lt_min hηB hηF),
    (min_le_left _ _).trans hηC1,hC,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P CB0 CS WF
  obtain ⟨p⟩ := hCoarse floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  obtain ⟨S,hS⟩ := hBalanced floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd CF CT P
  have hHigh (b i : I) (y : X) : ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      y ∈ Y → (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
        (p.coarse b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    by_cases hy : y ∈ Y
    · obtain ⟨hSG,L,H,hL,hH,hLN,hHN⟩ := (hS b i).2 y hy
      have hSame : S b i y=p.coarse b i y := coarseCovariantRotationGraph_unique hSG (p.first_graph b i y hy)
      exact ⟨H,fun _ => by simpa only [hSame] using hH⟩
    · exact ⟨0,fun hxy => (hy hxy).elim⟩
  choose H hH using hHigh
  have hP (b : I) (y : X) (hy : y ∈ Y) := P.firstCovariantCoordinateHigherL_balanced b y
    (P.firstDerivativeCoordinate_balanced y (hForward floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd CF CT P y hy) b)
  exact ⟨forward_strong_half_two_jets_of_coarse hY hΩ hd (zero_lt_one.trans_le hK) P WF p H hH hP
    (fun b => hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub (zero_lt_one.trans_le hK) b)⟩

end ShrinkingSpheres.ParallelEnergy
