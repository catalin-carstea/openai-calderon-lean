import Proof.UniformNormalFrameMetricHigherJets
import Proof.PullbackMatrixPointEllipticity
import Proof.UniversalNormalizedMatrixCoefficientJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Uniform finite joint derivatives of the actual normalized first
    coefficient on the independent center/radius/frame/spatial family. -/
theorem uniform_normalFrameCoefficient_higher_jet_bounds {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ s : ℝ,|s| ≤ d.radius y → ∀ z : X,‖z‖ ≤ Z →
      ∀ n : ℕ,n ≤ N →
        ‖iteratedFDeriv ℝ n (normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) ((y,(s,L)),z)‖ ≤ C := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  let B := backgroundAllMetricJetBudget M
  let CN := (N.factorial:ℝ)*B
  have hCN : 0 ≤ CN := by
    have hB : 0 ≤ B := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
    dsimp only [CN]
    positivity
  obtain ⟨ηM,CM,hηM,hηM1,hCM,hMetric⟩ := uniform_normalFrameMetric_higher_jet_bounds hY hΩ N hNm
    K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηG,hηG,hηG1,hGeometry⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ Z hZ
  let delta := ((metricDensityBudget (4*K^2))⁻¹)^2
  have hDelta : 0 < delta := by dsimp only [delta,metricDensityBudget];positivity
  obtain ⟨Cu,hCu,hUniversal⟩ := exists_universalNormalizedMatrixCoefficient_jet_bound K⁻¹ K (4*K^2) delta
    (inv_pos.mpr hKpos) hDelta N
  let D := 1+CM+CN
  have hCM0 : 0 ≤ CM := zero_le_one.trans hCM
  have hD : 1 ≤ D := by dsimp only [D];linarith only [hCM0,hCN]
  have hCu0 : 0 ≤ Cu := zero_le_one.trans hCu
  let C := 1+(N.factorial:ℝ)*Cu*D^N
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*Cu*D^N := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨min ηM ηG,C,lt_min hηM hηG,(min_le_left _ _).trans hηM1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he s hs z hz n hn
  let q : NormalFrameParameter × X := ((y,(s,L)),z)
  let F : NormalFrameParameter × X → NormalizedMatrixCoefficientInput :=
    fun p => (normalFrameCentralEntries d.γ d.g₁ p,normalFrameMetric d.g₁ d.expMap p)
  have hSmallM := hSmall.trans (min_le_left _ _)
  have hSmallG := hSmall.trans (min_le_right _ _)
  have hCenter := hd.2.1.center_mem hy
  have hPack := hGeometry floor hf ε hε hSmallG d hd y hy L he s hs z hz
  have hPoint : ‖normalFrameMetric d.g₁ d.expMap q‖ ≤ 4*K^2 ∧
      delta ≤ (normalFrameMetric d.g₁ d.expMap q).det := by
    rw [normalFrameMetric_eq_universal_pullback]
    exact hd.1.1.universalPullbackMetricMatrix_point_bounds hd.1.2.1 hKpos y
      (d.expMap (normalFrameInput q)) hCenter hPack.2.1
      (normalVerticalJacobian d.expMap y (s • L z)) L he hPack.2.2.2.1
  have hDiag0 := hd.1.1.diagonal_entry_mem_Icc hKpos hCenter 0
  have hDiag1 := hd.1.2.1.diagonal_entry_mem_Icc hKpos hCenter 0
  have hMem : F q ∈ universalNormalizedMatrixCoefficientSet K⁻¹ K (4*K^2) delta :=
    ⟨hDiag0,hDiag1,hPoint.1,hPoint.2⟩
  have hCentral := hd.1.contDiffAt_normalFrameCentralEntries hΩ (q:=q) hCenter
  have hg (i j : I) : ContDiffAt ℝ ∞ (fun x => d.g₁ x i j) (d.expMap (normalFrameInput q)) :=
    (hd.1.2.1.1 i j).contDiffAt (hΩ.mem_nhds hPack.2.1)
  have hRawMetric : ContDiffAt ℝ ∞ (normalFrameMetric d.g₁ d.expMap) q :=
    contDiffAt_normalFrameMetric d.g₁ d.expMap q
      (contDiffAt_normalJointMetricTensor d.g₁ d.expMap (normalFrameInput q) hPack.2.2.1 hg)
  have hF : ContDiffAt ℝ ∞ F q := hCentral.prodMk hRawMetric
  have hInput (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j F q‖ ≤ D := by
    rw [iteratedFDeriv_prodMk hCentral hRawMetric (i:=j) (by simp),ContinuousMultilinearMap.opNorm_prod]
    apply max_le
    · exact (hd.1.normalFrameCentralEntries_jet_bound hΩ N (by omega) hCenter j hj).trans
        (by change CN ≤ D;dsimp only [D];linarith only [hCM0])
    · exact (hMetric floor hf ε hε hSmallM d hd y hy L he s hs z hz j hj).trans
        (by change CM ≤ D;dsimp only [D];linarith only [hCN])
  have hOuterSmooth := contDiffAt_universalNormalizedMatrixCoefficient (F q)
    ((inv_pos.mpr hKpos).trans_le hDiag0.1) ((inv_pos.mpr hKpos).trans_le hDiag1.1)
    (hDelta.trans_le hPoint.2)
  have hEq : normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap = universalNormalizedMatrixCoefficient ∘ F := by
    funext p
    exact normalFrameNormalizedCoefficient_eq_universal d.γ d.g₁ d.expMap p
  rw [hEq]
  have hh := iteratedFDeriv_comp_common_bound F universalNormalizedMatrixCoefficient q hF hOuterSmooth
    N Cu D hCu0 hD (fun j hj => hUniversal j hj _ hMem) (fun j _ hj => hInput j hj) n hn
  exact hh.trans (by change (N.factorial:ℝ)*Cu*D^N ≤ C;dsimp only [C];linarith)

end ShrinkingSpheres
