import Proof.NormalFrameNormalizationLiftJets
import Proof.UniformNormalFrameCoefficientHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

lemma Background.contDiffAt_normalFrameCoefficient_of_control {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (E : X × X → X)
    (q : NormalFrameParameter × X) (hq : q.1.1 ∈ Ω)
    (hE : ContDiffAt ℝ ∞ E (normalFrameInput q)) (hImage : E (normalFrameInput q) ∈ Ω)
    (hPos : 0 < (normalFrameMetric g₁ E q).det) :
    ContDiffAt ℝ ∞ (normalFrameNormalizedCoefficient g g₁ E) q := by
  have hg (i j : I) := (h.2.1.1 i j).contDiffAt (hΩ.mem_nhds hImage)
  have hT := contDiffAt_normalJointMetricTensor g₁ E (normalFrameInput q) hE hg
  exact contDiffAt_normalFrameNormalizedCoefficient g g₁ E q hT
    ((h.firstMetricDensityFactor_smooth hK).contDiffAt (hΩ.mem_nhds hq)) hPos

/-- Uniform finite joint jets of the genuine orthonormal independent
    coefficient extension, including higher frame-parameter directions. -/
theorem uniform_orthonormalNormalFrameCoefficient_higher_jet_bounds {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ s : ℝ,|s| ≤ d.radius y → ∀ z : X,‖z‖ ≤ Z →
      ∀ n : ℕ,n ≤ N →
        ‖iteratedFDeriv ℝ n (orthonormalNormalFrameCoefficient d.γ d.g₁ d.expMap) ((y,(s,L)),z)‖ ≤ C := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hRaw⟩ := uniform_normalFrameCoefficient_higher_jet_bounds hY hΩ N hNm
    K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨D,hD,hLift⟩ := uniform_normalFrameOrthonormalLift_positive_jet_bounds hΩ K M hK N (by omega)
  obtain ⟨ηG,hηG,hηG1,hGeometry⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ Z hZ
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  let C := 1+(N.factorial:ℝ)*CR*D^N
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*CR*D^N := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨min ηR ηG,C,lt_min hηR hηG,(min_le_left _ _).trans hηR1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he s hs z hz n hn
  let q : NormalFrameParameter × X := ((y,(s,L)),z)
  have hSmallR := hSmall.trans (min_le_left _ _)
  have hSmallG := hSmall.trans (min_le_right _ _)
  have hCenter := hd.2.1.center_mem hy
  have hPack := hGeometry floor hf ε hε hSmallG d hd y hy L he s hs z hz
  have hPoint : ‖normalFrameMetric d.g₁ d.expMap q‖ ≤ 4*K^2 ∧
      (((metricDensityBudget (4*K^2))⁻¹)^2) ≤ (normalFrameMetric d.g₁ d.expMap q).det := by
    rw [normalFrameMetric_eq_universal_pullback]
    exact hd.1.1.universalPullbackMetricMatrix_point_bounds hd.1.2.1 hKpos y
      (d.expMap (normalFrameInput q)) hCenter hPack.2.1
      (normalVerticalJacobian d.expMap y (s • L z)) L he hPack.2.2.2.1
  have hPos : 0 < (normalFrameMetric d.g₁ d.expMap q).det :=
    (show 0 < (((metricDensityBudget (4*K^2))⁻¹)^2) by unfold metricDensityBudget;positivity).trans_le hPoint.2
  have hRawSmooth := hd.1.contDiffAt_normalFrameCoefficient_of_control hΩ hKpos d.expMap q
    hCenter hPack.2.2.1 hPack.2.1 hPos
  have hN := contDiffAt_normalization_at_orthonormal d.γ q.1
    (fun i j => (hd.1.1.1 i j).contDiffAt (hΩ.mem_nhds hCenter)) he
  have hSmooth := contDiffAt_normalFrameOrthonormalLift d.γ q hN
  have hFix : normalFrameOrthonormalLift d.γ q = q := normalFrameOrthonormalLift_eq_self d.γ q he
  have hOuterSmooth : ContDiffAt ℝ ∞ (normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
      (normalFrameOrthonormalLift d.γ q) := by rwa [hFix]
  have hOuter (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
        (normalFrameOrthonormalLift d.γ q)‖ ≤ CR := by
    rw [hFix]
    exact hRaw floor hf ε hε hSmallR d hd y hy L he s hs z hz j hj
  rw [orthonormalNormalFrameCoefficient_eq_comp]
  have hh := iteratedFDeriv_comp_common_bound (normalFrameOrthonormalLift d.γ)
    (normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) q hSmooth hOuterSmooth N CR D hCR0 hD hOuter
    (fun j hj hjN => hLift d.γ d.g₁ d.g₂ d.frame hd.1 q hCenter he j hj hjN) n hn
  exact hh.trans (by change (N.factorial:ℝ)*CR*D^N ≤ C;dsimp only [C];linarith)

end ShrinkingSpheres
