import Proof.UniformNormalFrameRelativeCoframeJets
import Proof.Archive.ClosedCoefficientJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

def normalFrameRelativeClosedCoframeMultiplier (Q : SmoothCoefficientJets 3) (g : MetricField) (v : X) (j : I)
    (p : NormalFrameRelativeParameter) : ClosedCoefficientJets 3 :=
  normalFrameRelativeCoframeValue g v j p • smoothCoefficientClosureInclusionL 3 Q

theorem uniform_normalFrameRelativeClosedCoframe_higher_jets {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ y ∈ Ω,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ (Q : SmoothCoefficientJets 3) (v : X) (j : I),
        ContDiffAt ℝ ∞ (normalFrameRelativeClosedCoframeMultiplier Q g v j) ((y,L),0) ∧
        ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameRelativeClosedCoframeMultiplier Q g v j) ((y,L),0)‖ ≤
          C*‖v‖*‖Q‖ := by
  obtain ⟨C,hC,hScalar⟩ := uniform_normalFrameRelativeCoframe_higher_jets hΩ N hNm K M hK
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e h y hy L he Q v j
  obtain ⟨hSmooth,hJets⟩ := hScalar g g₁ g₂ e h y hy L he v j
  let S : ℝ →L[ℝ] ClosedCoefficientJets 3 := (ContinuousLinearMap.id ℝ ℝ).smulRight (smoothCoefficientClosureInclusionL 3 Q)
  have hNormS : ‖S‖ ≤ ‖Q‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q)
    intro c
    change ‖c • smoothCoefficientClosureInclusionL 3 Q‖ ≤ ‖Q‖*‖c‖
    rw [norm_smul,norm_smoothCoefficientClosureInclusionL]
    exact le_of_eq (mul_comm _ _)
  have hEq : normalFrameRelativeClosedCoframeMultiplier Q g v j = S ∘ normalFrameRelativeCoframeValue g v j := rfl
  rw [hEq]
  refine ⟨S.contDiff.contDiffAt.comp _ hSmooth,?_⟩
  intro n hn
  exact (norm_iteratedFDeriv_clm_comp_le S (normalFrameRelativeCoframeValue g v j) ((y,L),0) hSmooth n).trans
    ((mul_le_mul hNormS (hJets n hn) (norm_nonneg _) (norm_nonneg Q)).trans_eq (by ring))

theorem normalFrameRelativeClosedCoframeMultiplier_actual
    {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) {y : X} (hy : y ∈ Ω)
    (Q : SmoothCoefficientJets 3) (v : X) (j : I) :
    normalFrameRelativeClosedCoframeMultiplier Q d.γ v j ((y,frameVectorLinear d.frame y),0) =
      smoothCoefficientClosureInclusionL 3 (frameCoordinateLinear d.γ d.frame y j v • Q) := by
  have he (i k : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis k)) = if i=k then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 y hy i k
  rw [normalFrameRelativeClosedCoframeMultiplier,normalFrameRelativeCoframeValue_orthonormal _ _ _ _ _ he,
    (smoothCoefficientClosureInclusionL 3).map_smul]
  rw [frameCoordinateLinear_apply]
  simp only [frameVectorLinear_apply,frameVector_axis]

end ShrinkingSpheres
