import Proof.NormalFramePullbackInputJets
import Proof.NormalFrameInputHigherJets
import Proof.UniformSignedNormalFrameEndpointJets
import Proof.BackgroundFirstMetricHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- All finite joint derivatives of the actual first pullback metric are
    uniform on the signed radial segment and arbitrary orthonormal frames.
    The center, radius, frame and spatial variables remain independent. -/
theorem uniform_normalFrameMetric_higher_jet_bounds {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N+2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ s : ℝ,|s| ≤ d.radius y → ∀ z : X,‖z‖ ≤ Z →
      ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameMetric d.g₁ d.expMap) ((y,(s,L)),z)‖ ≤ C := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hK0 : 0 ≤ K := hKpos.le
  let B := backgroundAllMetricJetBudget M
  have hB0 : 0 ≤ B := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
  obtain ⟨Ci,hCi,hInput⟩ := uniform_normalFrameInput_positive_jet_bounds K Z N
  obtain ⟨ηE,Ce,hηE,hηE1,hCe,hEndpoint⟩ := uniform_signed_normalFrame_endpoint_jets hY hΩ N hNm
    K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηG,hηG,hηG1,hGeometry⟩ := uniform_normalFrame_signed_radius_control (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨Cu,hCu,hUniversal⟩ := exists_universalPullbackMetricMatrix_jet_bound K Ce K N
  let D := normalFramePullbackInputJetBudget N B Ci Ce K
  have hCe0 : 0 ≤ Ce := zero_le_one.trans hCe
  have hCu0 : 0 ≤ Cu := zero_le_one.trans hCu
  have hD : 1 ≤ D := normalFramePullbackInputJetBudget_ge_one N B Ci Ce K hB0
    (zero_le_one.trans hCi) hCe0 hK0
  let C := 1+(N.factorial:ℝ)*Cu*D^N
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*Cu*D^N := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨min ηE ηG,C,lt_min hηE hηG,(min_le_left _ _).trans hηE1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he s hs z hz n hn
  let q : NormalFrameParameter × X := ((y,(s,L)),z)
  have hSmallE := hSmall.trans (min_le_left _ _)
  have hSmallG := hSmall.trans (min_le_right _ _)
  have hPack := hGeometry floor hf ε hε hSmallG d hd y hy L he s hs z hz
  have hEnd := hEndpoint floor hf ε hε hSmallE d hd y hy L he s hs z hz
  have hCenter := hd.2.1.center_mem hy
  let eL : Frame := fun _ i => L (axis i)
  have hLeq : frameVectorLinear eL y = L := by
    apply ContinuousLinearMap.ext
    intro v
    exact frameVector_linear_axes L y v
  have hL : ‖L‖ ≤ K := by
    rw [← hLeq]
    exact hd.1.1.norm_frameVectorLinear_le hK hCenter eL he
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hs1 : |s| ≤ 1 := hs.trans (hrε.trans (hSmallE.trans hηE1))
  have hI (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) : ‖iteratedFDeriv ℝ j normalFrameInput q‖ ≤ Ci :=
    hInput q hs1 hL hz j hj hjN
  have hE : ContDiffAt ℝ ∞ d.expMap (normalFrameInput q) := hPack.2.2.1
  have hg : ContDiffAt ℝ ∞ d.g₁ (d.expMap (normalFrameInput q)) :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j =>
      (hd.1.2.1.1 i j).contDiffAt (hΩ.mem_nhds hPack.2.1)))
  have hM (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j d.g₁ (d.expMap (normalFrameInput q))‖ ≤ B :=
    (hd.1.first_matrix_jet_bound hΩ ⟨j,by omega⟩ hPack.2.1).trans (abs_metricJet_le_all_budget M _)
  have hP (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j (normalFramePullbackInput d.g₁ d.expMap) q‖ ≤ D :=
    norm_iteratedFDeriv_normalFramePullbackInput_le d.g₁ d.expMap q N B Ci Ce K hB0 hCi hCe0 hK0
      hE hg hI hEnd.1 hM hL j hj
  have hA0 : ‖d.g₁ (d.expMap (normalFrameInput q))‖ ≤ K :=
    (Matrix.norm_le_iff hK0).mpr (fun i j => hd.1.2.1.entry_abs_bound hKpos hPack.2.1 i j)
  have hJ0 : ‖normalVerticalJacobian d.expMap y (s • L z)‖ ≤ Ce := by
    have hh := hEnd.2 0 (Nat.zero_le N)
    simpa only [norm_iteratedFDeriv_zero] using hh
  have hSmooth := contDiffAt_normalFramePullbackInput d.g₁ d.expMap q hE hg
  have hOuter (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j universalPullbackMetricMatrix (normalFramePullbackInput d.g₁ d.expMap q)‖ ≤ Cu :=
    hUniversal j hj _ hA0 hJ0 hL
  have hEq : normalFrameMetric d.g₁ d.expMap = universalPullbackMetricMatrix ∘ normalFramePullbackInput d.g₁ d.expMap := by
    funext p
    exact normalFrameMetric_eq_universal_pullback d.g₁ d.expMap p
  rw [hEq]
  have hh := iteratedFDeriv_comp_common_bound (normalFramePullbackInput d.g₁ d.expMap)
    universalPullbackMetricMatrix q hSmooth contDiff_universalPullbackMetricMatrix.contDiffAt
    N Cu D hCu0 hD hOuter (fun j _ hj => hP j hj) n hn
  exact hh.trans (by change (N.factorial:ℝ)*Cu*D^N ≤ C;dsimp only [C];linarith)

end ShrinkingSpheres
