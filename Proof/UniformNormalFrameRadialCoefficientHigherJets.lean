import Proof.UniformOrthonormalCoefficientHigherJets
import Proof.UniformRadialCoefficientDomains
import Proof.NormalFrameRadialReorder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Uniform joint jets after moving radius to the last coordinate.
    This is the shared input for ordinary and relative-radius Taylor. -/
theorem uniform_normalFrameRadialCoefficient_higher_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ s : ℝ,|s| ≤ d.radius y → ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (normalFrameRadialCoefficient d.γ d.g₁ d.expMap) (((y,L),z),s)‖ ≤ C := by
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hCoeff⟩ := uniform_orthonormalNormalFrameCoefficient_higher_jet_bounds hY hΩ
    N hNm K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,hηD,hηD1,hDomains⟩ := uniform_orthonormal_coefficient_smooth_domains (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ Z hZ
  have hCA0 : 0 ≤ CA := zero_le_one.trans hCA
  let C := 1+(N.factorial:ℝ)*CA
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*CA := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨min ηA ηD,C,lt_min hηA hηD,(min_le_left _ _).trans hηA1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz s hs n hn
  let p : NormalFrameSpatialParameter := ((y,L),z)
  obtain ⟨U,hU,hMem,hA⟩ := hDomains floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy L he z hz s hs
  have hOuter (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (orthonormalNormalFrameCoefficient d.γ d.g₁ d.expMap)
        (normalFrameRadialReorderL (p,s))‖ ≤ CA :=
    hCoeff floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he s hs z hz j hj
  have hh := iteratedFDeriv_comp_common_bound normalFrameRadialReorderL
    (orthonormalNormalFrameCoefficient d.γ d.g₁ d.expMap) (p,s)
    normalFrameRadialReorderL.contDiff.contDiffAt (hA.contDiffAt (hU.mem_nhds hMem)) N CA 1 hCA0 le_rfl hOuter
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one normalFrameRadialReorderL
      norm_normalFrameRadialReorderL_le_one (p,s) j hj) n hn
  simp only [one_pow,mul_one] at hh
  exact hh.trans (by change (N.factorial:ℝ)*CA ≤ C;dsimp only [C];linarith)

end ShrinkingSpheres
