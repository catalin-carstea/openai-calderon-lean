import Proof.RelativeAngularNormalizationJets
import Proof.NormalizedDirectionalHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalized angular derivatives retain a common small factor in all
    finite mixed jets, with constants depending only on finite metric data. -/
theorem uniform_relative_angular_derivative_higher_jets {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ y ∈ Ω,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ F : NormalFrameRelativeParameter → E,ContDiffAt ℝ ∞ F ((y,L),0) →
      ∀ B : ℝ,0 ≤ B →
      (∀ n : ℕ,n ≤ N+1 → ‖iteratedFDeriv ℝ n F ((y,L),0)‖ ≤ B) →
      ∀ i j : I,ContDiffAt ℝ ∞ (normalFrameRelativeAngularDerivative g F i j) ((y,L),0) ∧
        ∀ n : ℕ,n ≤ N →
          ‖iteratedFDeriv ℝ n (normalFrameRelativeAngularDerivative g F i j) ((y,L),0)‖ ≤ C*B := by
  obtain ⟨D,hD,hJets⟩ := uniform_relative_angular_normalization_jets hΩ N hNm K M hK
  let C := 1+2^N*(2*D)*(N.factorial:ℝ)*D^N
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hC : 1 ≤ C := by
    have hh : 0 ≤ 2^N*(2*D)*(N.factorial:ℝ)*D^N := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e h y hy L he F hF B hB hFJets i j
  let p0 : NormalFrameRelativeParameter := ((y,L),0)
  have hFix : normalFrameRelativeNormalization g p0 = p0 := normalFrameRelativeNormalization_eq_self g p0 he
  obtain ⟨hQ,hQJets,hVJets⟩ := hJets g g₁ g₂ e h y hy L he
  have hFN : ContDiffAt ℝ ∞ F (normalFrameRelativeNormalization g p0) := by rw [hFix];exact hF
  have hDF := hFN.fderiv_right (m:=∞) (by simp)
  have hFNJets (n : ℕ) (hn : n ≤ N+1) :
      ‖iteratedFDeriv ℝ n F (normalFrameRelativeNormalization g p0)‖ ≤ B := by rw [hFix];exact hFJets n hn
  refine ⟨(hDF.comp p0 hQ).clm_apply (hVJets i j).1,?_⟩
  intro n hn
  have hh := norm_iteratedFDeriv_normalizedDirectional_common_bound F
    (normalFrameRelativeNormalization g) (fun p => normalFrameRelativeAngularTangent g p i j) p0
    hFN hQ (hVJets i j).1 N B D (2*D) hB hD (by positivity)
    hFNJets hQJets (hVJets i j).2 n hn
  exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp only [C];linarith) hB)

end ShrinkingSpheres
