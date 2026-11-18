import Proof.QuarticGeneratorThreeCombination
import Proof.PhysicalPotentialQuarticCaller
import Proof.FrameEndpointCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def nativePotentialFrameIndex : PhysicalPotentialGeneratorIndex → I → PhysicalPotentialGeneratorIndex
  | .inl u,_ => .inl u
  | .inr (.inl i),_ => .inr (.inl i)
  | .inr (.inr _),j => .inr (.inr j)

def nativePotentialFrameCoefficient (d : Data) (y : X) : PhysicalPotentialGeneratorIndex → I → ℝ
  | .inl _,j => if j=0 then 1 else 0
  | .inr (.inl _),j => if j=0 then 1 else 0
  | .inr (.inr i),j => d.frame y i j

lemma nativePotentialFrameIndex_weight (r : ℝ) (a : PhysicalPotentialGeneratorIndex) (j : I) :
    potentialGeneratorWeight r (nativePotentialFrameIndex a j)=potentialGeneratorWeight r a := by
  rcases a with u | (i | i) <;> rfl

lemma Admissible.nativePotentialFrameCoefficient_abs_le {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y)
    (a : PhysicalPotentialGeneratorIndex) (j : I) : |nativePotentialFrameCoefficient d y a j| ≤ K := by
  rcases a with u | (i | i)
  · dsimp only [nativePotentialFrameCoefficient]
    split_ifs <;> first | exact (by simpa only [abs_one] using hK) | exact (by simpa only [abs_zero] using zero_le_one.trans hK)
  · dsimp only [nativePotentialFrameCoefficient]
    split_ifs <;> first | exact (by simpa only [abs_one] using hK) | exact (by simpa only [abs_zero] using zero_le_one.trans hK)
  · exact hd.1.1.frame_component_abs_le hK d.frame (hd.2.1.center_mem hy)
      (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) i j

/-- SAME physical generator endpoints are exactly the finite frame change
of compatible actual axis endpoints. Only genuine coarse identities are used. -/
lemma PhysicalPrincipalData.potential_generators_frame_change {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (EL : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (EH : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hEL : ∀ j,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis j) P.adjoint (P.center j) y)=
        (EL j).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hEH : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (EH j)=
      (actualFirstAdjointErrorFamily d (axis j) P.adjoint (P.center j) y).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    (∀ a,P.potentialGeneratorLow y a=∑ j : I,nativePotentialFrameCoefficient d y a j •
      nativePotentialGeneratorLow EL (nativePotentialFrameIndex a j)) ∧
    (∀ a,P.potentialGeneratorHigh y a=∑ j : I,nativePotentialFrameCoefficient d y a j •
      nativePotentialGeneratorHigh EH (nativePotentialFrameIndex a j)) := by
  constructor
  · intro a
    rcases a with u | (i | i)
    · simp [nativePotentialFrameCoefficient,nativePotentialFrameIndex,nativePotentialGeneratorLow,
        PhysicalPrincipalData.potentialGeneratorLow,degreeHalfL]
    · simp [nativePotentialFrameCoefficient,nativePotentialFrameIndex,nativePotentialGeneratorLow,
        PhysicalPrincipalData.potentialGeneratorLow,degreeHalfL]
    · exact half_endpoint_unique_of_coarse (actualFrameFirstAdjointErrorFamily d P.adjoint P.center i y)
        (P.first.low i y) (∑ j : I,d.frame y i j • EL j) (P.first.low_coarse i y hy)
        (frame_low_endpoint_combination d P.adjoint P.center i y EL hEL)
  · intro a
    rcases a with u | (i | i)
    · simp [nativePotentialFrameCoefficient,nativePotentialFrameIndex,nativePotentialGeneratorHigh,
        PhysicalPrincipalData.potentialGeneratorHigh,degreeHigherL]
    · simp [nativePotentialFrameCoefficient,nativePotentialFrameIndex,nativePotentialGeneratorHigh,
        PhysicalPrincipalData.potentialGeneratorHigh,degreeHigherL]
    · exact higher_endpoint_unique_of_coarse (actualFrameFirstAdjointErrorFamily d P.adjoint P.center i y)
        (P.first.high i y) (∑ j : I,d.frame y i j • EH j) (P.first.high_coarse i y hy)
        (frame_high_endpoint_combination d P.adjoint P.center i y EH hEH)

/-- Closed actual-frame transfer of ALL49 native mixed-adjoint quartic
blocks. The coefficient comparison retains ANY selected physical endpoints. -/
lemma PhysicalPrincipalData.quartic_data_of_axis_generators {Y Ω : Set X} {d : Data} {CF CT : ℝ}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hK : 1 ≤ K) {y : X} (hy : y ∈ Y)
    (EL : I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (EH : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hEL : ∀ j,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d (axis j) P.adjoint (P.center j) y)=
        (EL j).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hEH : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (EH j)=
      (actualFirstAdjointErrorFamily d (axis j) P.adjoint (P.center j) y).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    {CA CK : ℝ} (hCK : 0 ≤ CK)
    (W : SphereQuarticGeneratorData (nativePotentialGeneratorLow EL) (nativePotentialGeneratorHigh EH)
      (potentialGeneratorWeight (d.radius y)) CA CK) :
    Nonempty (PhysicalPotentialQuarticData P y (3*K*CA) (9*K^2*CK)) := by
  obtain ⟨V⟩ := W.three_linear_combinations nativePotentialFrameIndex (nativePotentialFrameCoefficient d y)
    (potentialGeneratorWeight (d.radius y)) K (zero_le_one.trans hK) hCK
    (potentialGeneratorWeight_nonneg (hd.2.2.2.2.1.2 y hy).1.le)
    (hd.nativePotentialFrameCoefficient_abs_le hK hy) (nativePotentialFrameIndex_weight (d.radius y))
  obtain ⟨hLow,hHigh⟩ := P.potential_generators_frame_change hy EL EH hEL hEH
  have hL : (fun a => ∑ j : I,nativePotentialFrameCoefficient d y a j •
      nativePotentialGeneratorLow EL (nativePotentialFrameIndex a j))=P.potentialGeneratorLow y :=
    funext (fun a => (hLow a).symm)
  have hH : (fun a => ∑ j : I,nativePotentialFrameCoefficient d y a j •
      nativePotentialGeneratorHigh EH (nativePotentialFrameIndex a j))=P.potentialGeneratorHigh y :=
    funext (fun a => (hHigh a).symm)
  have V' : SphereQuarticGeneratorData (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y)
      (potentialGeneratorWeight (d.radius y)) (3*K*CA) (9*K^2*CK) := by
    rw [←hL,←hH]
    exact V
  exact ⟨{ adjointHigh := V'.adjointHigh
           commLow := V'.commLow
           commHigh := V'.commHigh
           adjoint_compatible := V'.adjoint_compatible
           commutator_compatible := V'.commutator_compatible
           commutator_balanced := V'.commutator_balanced
           adjoint_bound := V'.adjoint_bound
           commLow_bound := V'.commLow_bound
           commHigh_bound := V'.commHigh_bound }⟩
end ShrinkingSpheres
