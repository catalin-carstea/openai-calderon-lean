import Proof.NormalFrameRelativeJetInput
import Proof.UniformNormalFrameRadialCoefficientHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

theorem uniform_normalFrameRelativeCoefficient_joint_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ r : ℝ,|r| ≤ d.radius y → ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r) (((y,L),0),z)‖ ≤ C := by
  obtain ⟨ηA,B,hηA,hηA1,hB,hCoeff⟩ := uniform_normalFrameRadialCoefficient_higher_jet_bounds
    hY hΩ N hNm K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,hηD,hηD1,hDomains⟩ := uniform_orthonormal_coefficient_smooth_domains (Y:=Y)
    hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  let C : ℝ := 1+(N.factorial:ℝ)*B
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC : 1 ≤ C := by
    have hProduct : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [C]
    linarith only [hProduct]
  refine ⟨min ηA ηD,C,lt_min hηA hηD,(min_le_left _ _).trans hηA1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz r hr n hn
  have hRpos := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hRpos.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : |r| ≤ 1 := hr.trans (hrε.trans (hSmall.trans ((min_le_left _ _).trans hηA1)))
  obtain ⟨U,hU,hMem,hA⟩ := hDomains floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd
    y hy L he z hz r hr
  have hOuter : ContDiffAt ℝ ∞ (orthonormalNormalFrameCoefficient d.γ d.g₁ d.expMap)
      (normalFrameRadialReorderL (((y,L),z),r)) := hA.contDiffAt (hU.mem_nhds hMem)
  have hF : ContDiffAt ℝ ∞ (normalFrameRadialCoefficient d.γ d.g₁ d.expMap) (((y,L),z),r) :=
    hOuter.comp (((y,L),z),r) normalFrameRadialReorderL.contDiff.contDiffAt
  have hJets (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (normalFrameRadialCoefficient d.γ d.g₁ d.expMap) (((y,L),z),r)‖ ≤ B :=
    hCoeff floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he z hz r hr j hj
  have hh := norm_iteratedFDeriv_relative_coefficient_of_joint_bound
    (normalFrameRadialCoefficient d.γ d.g₁ d.expMap) (y,L) z r hr1 N B hB0 hF hJets n hn
  exact hh.trans (by dsimp only [C];linarith)

end ShrinkingSpheres
