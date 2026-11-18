import Proof.UniformRelativeRadiusCoefficientRemainderJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- One admissibility threshold and one constant control the whole finite jet,
    so downstream compositions may use all lower orders at the same data. -/
theorem uniform_relative_radius_coefficient_remainder_finite_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ r : ℝ,|r| ≤ d.radius y → ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (fun q : NormalFrameSpatialParameter × ℝ =>
          normalFrameRadialRemainder d.γ d.g₁ d.expMap (q.1,(1+q.2)*r)) (((y,L),z),0)‖ ≤ C*r^2 := by
  revert hNm
  induction N with
  | zero =>
    intro hNm
    obtain ⟨η,C,hη,hη1,hC,hBound⟩ := uniform_relative_radius_coefficient_remainder_parameter_jets
      hY hΩ 0 hNm K ρ c₀ M Cj hK hρ Z hZ
    refine ⟨η,C,hη,hη1,hC,?_⟩
    intro floor hf ε hε hSmall d hd y hy L he z hz r hr n hn
    have hn0 : n=0 := by omega
    subst n
    exact hBound floor hf ε hε hSmall d hd y hy L he z hz r hr
  | succ N ih =>
    intro hNm
    obtain ⟨ηA,CA,hηA,hηA1,hCA,hBoundA⟩ := ih (by omega)
    obtain ⟨ηB,CB,hηB,hηB1,hCB,hBoundB⟩ := uniform_relative_radius_coefficient_remainder_parameter_jets
      hY hΩ (N+1) hNm K ρ c₀ M Cj hK hρ Z hZ
    refine ⟨min ηA ηB,max CA CB,lt_min hηA hηB,(min_le_left _ _).trans hηA1,
      hCA.trans (le_max_left _ _),?_⟩
    intro floor hf ε hε hSmall d hd y hy L he z hz r hr n hn
    by_cases hnN : n ≤ N
    · exact (hBoundA floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he z hz r hr n hnN).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg r))
    · have hnEq : n=N+1 := by omega
      subst n
      exact (hBoundB floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy L he z hz r hr).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg r))

end ShrinkingSpheres
