import Proof.PrincipalFirstErrorCoordinateSharpWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

/-- Small coordinate weights for bounded physical background operators.
The original profile smallness supplies the gain; no frame jet is bounded. -/
theorem Admissible.principalFirstErrorCoordinateWeight_small_bounds {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} (hm : 1 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b i : I) :
    let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
    |principalFirstErrorCoordinateWeight d a b y| ≤ B*ε/beta d.γ d.radius y ∧
      |directionalFDeriv (axis i) (principalFirstErrorCoordinateWeight d a b) y| ≤ B*ε := by
  have hSharp := hd.principalFirstErrorCoordinateWeight_sharp_zero_first_bounds hY hm hK hf hε hε1 hy a b i
  let B := principalFirstErrorCoordinateWeightBudget K |M ⟨1,by omega⟩|
  let β := beta d.γ d.radius y
  have hB : 0 ≤ B := principalFirstErrorCoordinateWeightBudget_nonneg _ _ (zero_le_one.trans hK) (abs_nonneg _)
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  refine ⟨hSharp.1.trans ?_,hSharp.2.trans ?_⟩
  · change B*ε/β^2 ≤ B*ε/β
    gcongr
    nlinarith only [hβ]
  · exact div_le_self (mul_nonneg hB hε) hβ
end ShrinkingSpheres
