import Proof.UniformBackgroundConnectionHigherJets
import Proof.NormalizedParallelCenterHigherJets
import Proof.UniformSignedNormalFrameEndpointJets
import Proof.NormalFrameInputHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def normalFrameParallelCenterJacobian (g : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) : X →L[ℝ] X :=
  normalizedParallelCenterJacobian g E (normalFrameInput q).1 (normalFrameInput q).2

/-- Every finite joint center/radius/frame/angular jet of the actual Jacobi
    center velocity has one uniform bound on the whole signed radial segment. -/
theorem uniform_normalFrameParallelCenter_higher_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ s : ℝ,|s| ≤ d.radius y → ∀ z : X,‖z‖ ≤ Z →
      ContDiffAt ℝ ∞ (normalFrameParallelCenterJacobian d.γ d.expMap) ((y,(s,L)),z) ∧
      ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameParallelCenterJacobian d.γ d.expMap) ((y,(s,L)),z)‖ ≤ C := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨CG,hCG,hConnection⟩ := uniform_background_connection_higher_jet_bounds hΩ N (by omega) K M hKpos
  obtain ⟨ηE,CE,hηE,hηE1,hCE,hEndpoint⟩ := uniform_signed_normalFrame_endpoint_jets hY hΩ N hNm K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηG,hηG,hηG1,hGeometry⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨Ci,hCi,hInput⟩ := uniform_normalFrameInput_positive_jet_bounds K Z N
  let B := 1+|normalizedParallelCenterHigherJetBudget N CE CG|
  let C := 1+(N.factorial:ℝ)*B*Ci^N
  have hB : 1 ≤ B := by dsimp only [B];linarith only [abs_nonneg (normalizedParallelCenterHigherJetBudget N CE CG)]
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hCE0 : 0 ≤ CE := zero_le_one.trans hCE
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*B*Ci^N := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨min ηE ηG,C,lt_min hηE hηG,(min_le_left _ _).trans hηE1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he s hs z hz
  let q : NormalFrameParameter × X := ((y,(s,L)),z)
  let p := normalFrameInput q
  let W := fun p : X × X => normalizedParallelCenterJacobian d.γ d.expMap p.1 p.2
  have hPack := hGeometry floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy L he s hs z hz
  have hEnd := hEndpoint floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he s hs z hz
  have hCenter := hd.2.1.center_mem hy
  have hΓ : ContDiffAt ℝ ∞ (connectionBilinear d.γ) y :=
    (hd.1.1.contDiffOn_connectionBilinear hΩ hKpos).contDiffAt (hΩ.mem_nhds hCenter)
  have hInv : (normalVerticalJacobian d.expMap y (s • L z)).IsInvertible :=
    hd.2.1.normalVerticalJacobian_isInvertible hy _ hPack.1.1.le
  obtain ⟨hW,hWJets⟩ := normalizedParallelCenter_higher_jets_of_data d.γ d.expMap p hPack.2.2.1 hΓ
    N CE CG hCE0 hCG0 hPack.1.2 hEnd.1
    (fun j hj => hConnection d.γ d.g₁ d.g₂ d.frame hd.1 y hCenter j hj) hInv hPack.2.2.2.2
  have hRaw (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j W p‖ ≤ B :=
    (hWJets j hj).trans ((le_abs_self _).trans (by dsimp only [B];linarith only [abs_nonneg (normalizedParallelCenterHigherJetBudget N CE CG)]))
  let eL : Frame := fun _ i => L (axis i)
  have hLeq : frameVectorLinear eL y = L := by
    apply ContinuousLinearMap.ext
    intro v
    exact frameVector_linear_axes L y v
  have hL : ‖L‖ ≤ K := by rw [← hLeq];exact hd.1.1.norm_frameVectorLinear_le hK hCenter eL he
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hs1 : |s| ≤ 1 := hs.trans (hrε.trans (hSmall.trans ((min_le_left _ _).trans hηE1)))
  have hSmooth : ContDiffAt ℝ ∞ (normalFrameParallelCenterJacobian d.γ d.expMap) q := by
    change ContDiffAt ℝ ∞ (W ∘ normalFrameInput) q
    exact hW.comp (f:=normalFrameInput) (g:=W) q contDiff_normalFrameInput.contDiffAt
  refine ⟨hSmooth,?_⟩
  intro n hn
  have hh := iteratedFDeriv_comp_common_bound normalFrameInput W q contDiff_normalFrameInput.contDiffAt hW
    N B Ci hB0 hCi hRaw (fun j hj hjN => hInput q hs1 hL hz j hj hjN) n hn
  exact hh.trans (by dsimp only [C];linarith)

end ShrinkingSpheres
