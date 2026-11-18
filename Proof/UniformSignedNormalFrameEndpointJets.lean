import Proof.NormalFrameSignedRadiusControl
import Proof.NormalVerticalJacobianHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The same actual endpoint/vertical-Jacobian budgets hold on the entire
    signed radial segment in every pointwise orthonormal frame. -/
theorem uniform_signed_normalFrame_endpoint_jets {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ s : ℝ,|s| ≤ d.radius y → ∀ z : X,‖z‖ ≤ Z →
        (∀ n : ℕ,1 ≤ n → n ≤ N+1 → ‖iteratedFDeriv ℝ n d.expMap (y,s • L z)‖ ≤ C) ∧
        (∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n
          (fun p : X × X => normalVerticalJacobian d.expMap p.1 p.2) (y,s • L z)‖ ≤ C) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨η,hη,hη1,hControl⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨C,hC,hEndpoint⟩ := uniform_normalMap_higher_jet_bounds hΩ K hKpos M (N+1) (by omega)
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he s hs z hz
  have hPack := hControl floor hf ε hε hSmall d hd y hy L he s hs z hz
  have hE (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N+1) : ‖iteratedFDeriv ℝ n d.expMap (y,s • L z)‖ ≤ C :=
    (hEndpoint d.γ d.g₁ d.g₂ d.frame hd.1 Y hY d.expMap (fun x => max ρ (d.radius x)) hd.2.1
      y hy (hd.normal_radius_continuousAt hY hy) (s • L z) hPack.1.1 hPack.1.2 n hn hnN).2
  refine ⟨hE,?_⟩
  intro n hn
  exact (norm_iteratedFDeriv_normalVerticalJacobian_le d.expMap (y,s • L z) hPack.2.2.1 n).trans
    (hE (n+1) (by omega) (by omega))

end ShrinkingSpheres
