import Proof.ParallelNormAssemblyReservedCoordinateError
import Proof.ParallelFirstSelfActualAdjointHigherGerm
import Proof.ParallelFirstSelfAdjointHigher

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The coordinate error is the SAME actual native endpoint packet.
This packages existing genuine graphs; it constructs no new native endpoint. -/
def coordinateActualErrorEndpointPacket {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (a : I) :
    FirstSelfActualErrorEndpointPacket Y d (axis a) where
  radial := P.radial
  adjoint := P.adjoint
  center := P.center a
  low := fun x => potentialCoordinateGeneratorLow P x (.inr (.inr a))
  high := fun x => potentialCoordinateGeneratorHigh P x (.inr (.inr a))
  adjoint_smooth := P.adjoint_smooth
  center_smooth := P.center_smooth a
  low_smooth := coordinate_error_low_smooth P hd a
  radial_actual := P.radial_actual
  adjoint_actual := P.adjoint_pair
  center_actual := P.center_actual a
  low_graph := fun x hx => coordinate_error_low_coarse P hx (hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)) a
  high_graph := fun x hx => coordinate_error_high_coarse P hx (hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)) a

/-- Actual canonical coordinate true-adjoint HIGH families, fixed before
all W witnesses and tests. -/
structure CoordinateErrorAdjointFamily {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (C0 : ℝ) where
  high : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  smooth : ∀ a,ContDiffOn ℝ ∞ (high a) Y
  balanced : ∀ a y,y ∈ Y →
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (high a y)=
      (potentialCoordinateGeneratorLow P y (.inr (.inr a))).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  norm_bound : ∀ a y,y ∈ Y → ‖high a y‖ ≤ C0*d.radius y

/-- Endpoint selection and actual HIGH smoothness use the SAME retained
native witnesses through the producer's genuine uniqueness theorem. -/
theorem uniform_coordinate_error_adjoint_family {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    Nonempty (CoordinateErrorAdjointFamily P C0) := by
  classical
  obtain ⟨ηE,C0,hηE,hηE1,hC0,hEndpoint⟩ := uniform_actual_error_adjoint_endpoint_family
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,hηS,hηS1,hSmooth⟩ := uniform_actual_error_adjoint_higher_smooth
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηE ηS,C0,lt_min hηE hηS,(min_le_left _ _).trans hηE1,hC0,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  let p := fun a => coordinateActualErrorEndpointPacket P hd a
  choose AH hAH using fun a : I => hEndpoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd (axis a) (p a)
  refine ⟨{ high := AH, smooth := ?_, balanced := ?_, norm_bound := ?_ }⟩
  · intro a
    exact hSmooth floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd (axis a) (p a) (AH a)
      (fun x hx => (hAH a x hx).1)
  · intro a y hy
    exact (hAH a y hy).1
  · intro a y hy
    simpa only [norm_axis,mul_one] using (hAH a y hy).2

/-- Genuine first HIGH covariant jets of the selected actual family. -/
structure CoordinateErrorAdjointFirstJets {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (C0 C1 : ℝ) extends CoordinateErrorAdjointFamily P C0 where
  jet : ∀ a y,y ∈ Y → ∀ i : I,
    ∃ N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      halfOperatorCovariantDerivativeL d (fun x => (potentialCoordinateGeneratorLow P x (.inr (.inr a))).adjoint)
        (high a) y (axis i)=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp N ∧
      ‖N‖ ≤ C1*d.radius y*beta d.γ d.radius y

/-- Existing native adjoint FIRST jets are transported to the SAME smooth
actual selected HIGH family; no higher regularity is inferred from norms. -/
theorem uniform_coordinate_error_adjoint_higher_first_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
    ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
    Nonempty (CoordinateErrorAdjointFirstJets P C0 C1) := by
  obtain ⟨ηA,C0,hηA,hηA1,hC0,hFamily⟩ := uniform_coordinate_error_adjoint_family
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηJ,C1,hηJ,hηJ1,hC1,hJet⟩ := uniform_first_self_native_adjoint_packet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηA ηJ,C0,C1,lt_min hηA hηJ,(min_le_left _ _).trans hηA1,hC0,hC1,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  obtain ⟨A⟩ := hFamily floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  refine ⟨{ toCoordinateErrorAdjointFamily := A,jet := ?_ }⟩
  intro a y hy i
  obtain ⟨q⟩ := hJet floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy (axis a)
  obtain ⟨N,hN,hNN,hNE⟩ := (coordinateActualErrorEndpointPacket P hd a).true_adjoint_jet_at hY hΩ hSub hd
    (zero_lt_one.trans_le hK) hy q (A.high a) (A.balanced a y hy) (axis i)
    (by simp only [norm_axis];exact le_refl _)
  exact ⟨N,hN,by simpa only [norm_axis,mul_one] using hNN⟩

end ShrinkingSpheres.ParallelEnergy
