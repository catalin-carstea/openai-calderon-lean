import Proof.PrincipalFirstErrorCoordinateWeights
import Proof.PrincipalFirstErrorCoordinateSecondWeight

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

def principalFirstErrorCoordinateTwoJetBudget (K M1 M2 C2 : ℝ) : ℝ :=
  principalFirstErrorCoordinateWeightBudget K M1+2*principalSecondBudget K M1 M2 C2

lemma principalFirstErrorCoordinateTwoJetBudget_nonneg (K M1 M2 C2 : ℝ)
    (hK : 0 ≤ K) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) :
    0 ≤ principalFirstErrorCoordinateTwoJetBudget K M1 M2 C2 := by
  have hB := principalFirstErrorCoordinateWeightBudget_nonneg K M1 hK hM1
  unfold principalFirstErrorCoordinateTwoJetBudget principalSecondBudget
  positivity

/-- The actual coordinate weights have common ordinary jets through two.
They depend on the metric and radius, and contain no chosen frame jets. -/
theorem Admissible.principalFirstErrorCoordinateWeight_two_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i j : I) :
    let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
    |principalFirstErrorCoordinateWeight d a b y| ≤ B ∧
      |fderiv ℝ (principalFirstErrorCoordinateWeight d a b) y (axis i)| ≤ B*beta d.γ d.radius y ∧
      |fderiv ℝ (fun x => fderiv ℝ (principalFirstErrorCoordinateWeight d a b) x (axis i))
        y (axis j)| ≤ B*(beta d.γ d.radius y)^2 := by
  let A2 := principalSecondBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let B1 := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let B := principalFirstErrorCoordinateTwoJetBudget K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| (Cj 2)
  let β := beta d.γ d.radius y
  have hK0 := zero_le_one.trans hK
  have hA2 : 0 ≤ A2 := by dsimp only [A2,principalSecondBudget];positivity
  have hB1 : 0 ≤ B1 := principalFirstErrorCoordinateWeightBudget_nonneg _ _ hK0 (abs_nonneg _)
  have hB1B : B1 ≤ B := by change B1 ≤ B1+2*A2;linarith only [hA2]
  have h2B : 2*A2 ≤ B := by change 2*A2 ≤ B1+2*A2;linarith only [hB1]
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have h01 := hd.principalFirstErrorCoordinateWeight_bounds hY (by omega) hK hf hε hε1 hy a b i
  refine ⟨h01.1.trans hB1B,?_,?_⟩
  · exact h01.2.trans (mul_le_mul_of_nonneg_right hB1B hβ0)
  · have hh := hd.principalFirstErrorCoordinateWeight_second_small_bound hY hm hK hf hε hε1 hy a b i j
    calc
      _ ≤ (2*A2)*ε := hh
      _ ≤ 2*A2 := by
        have h2A : 0 ≤ 2*A2 := by positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hε1 h2A
      _ ≤ B := h2B
      _ ≤ B*β^2 := by
        have hB : 0 ≤ B := hB1.trans hB1B
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hβ : 1 ≤ β^2) hB

end ShrinkingSpheres
