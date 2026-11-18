import Proof.NormalFrameParallelCenterSmoothDomain
import Proof.NormalFrameRadialParallelCenterZeroGerms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- One uniform finite budget and genuine smooth neighborhoods along the
    signed radial segment of the actual parallel-center family. -/
theorem uniform_normalFrameRadialParallelCenter_higher_jet_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ s : ℝ,|s| ≤ d.radius y →
      (∃ U : Set (NormalFrameSpatialParameter × ℝ),IsOpen U ∧ (((y,L),z),s) ∈ U ∧
        ContDiffOn ℝ ∞ (normalFrameRadialParallelCenter d.γ d.expMap) U) ∧
      ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameRadialParallelCenter d.γ d.expMap) (((y,L),z),s)‖ ≤ C := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨ηG,CG,hηG,hηG1,hCG,hG⟩ := uniform_normalFrameParallelCenter_higher_jet_bounds hY hΩ N hNm
    K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,hηD,hηD1,hGeometry⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ Z hZ
  let C := 1+(N.factorial:ℝ)*CG
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*CG := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨min ηG ηD,C,lt_min hηG hηD,(min_le_left _ _).trans hηG1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz s hs
  let p : NormalFrameSpatialParameter := ((y,L),z)
  have hPack := hGeometry floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy L he s hs z hz
  obtain ⟨U,hU,hMem,hRaw⟩ := hd.1.exists_normalFrameParallelCenter_smooth_domain hΩ hKpos hd.2.1
    hy s L z hPack.1.1.le
  have hLocal : ∃ V : Set (NormalFrameSpatialParameter × ℝ),IsOpen V ∧ (p,s) ∈ V ∧
      ContDiffOn ℝ ∞ (normalFrameRadialParallelCenter d.γ d.expMap) V := by
    refine ⟨normalFrameRadialReorderL ⁻¹' U,hU.preimage normalFrameRadialReorderL.continuous,hMem,?_⟩
    exact hRaw.comp normalFrameRadialReorderL.contDiff.contDiffOn (fun q hq => hq)
  refine ⟨hLocal,?_⟩
  have hOuter := hG floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he s hs z hz
  intro n hn
  have hh := iteratedFDeriv_comp_common_bound normalFrameRadialReorderL
    (normalFrameParallelCenterJacobian d.γ d.expMap) (p,s)
    normalFrameRadialReorderL.contDiff.contDiffAt hOuter.1 N CG 1 hCG0 le_rfl hOuter.2
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one normalFrameRadialReorderL
      norm_normalFrameRadialReorderL_le_one (p,s) j hj) n hn
  simp only [one_pow,mul_one] at hh
  exact hh.trans (by change (N.factorial:ℝ)*CG ≤ C;dsimp only [C];linarith)

end ShrinkingSpheres
