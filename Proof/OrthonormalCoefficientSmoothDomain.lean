import Proof.NormalFrameNormalizationLiftJets
import Proof.NormalFrameCoefficientFamily
import Proof.NormalFrameNormalizationDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- True local smooth domains for the genuine orthonormal extension.
    Pointwise C-infinity is not used as a substitute for such a domain. -/
theorem Background.exists_orthonormalFrame_coefficient_domain {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (s : ℝ) (L : X →L[ℝ] X) (z : X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0)
    (hv : s • L z ∈ disk g y (R y))
    (hPos : 0 < (normalFrameMetric g₁ E ((y,(s,L)),z)).det) :
    ∃ U : Set (NormalFrameParameter × X),IsOpen U ∧ ((y,(s,L)),z) ∈ U ∧
      ContDiffOn ℝ ∞ (orthonormalNormalFrameCoefficient g g₁ E) U := by
  obtain ⟨S,hS,hHere,hRaw⟩ := h.exists_normalFrame_coefficient_domain hΩ hK hN hy s L z hv hPos
  obtain ⟨hP,hNorm,_⟩ := h.1.normalFrame_normalization_open_domain hΩ hK
  let D : Set (NormalFrameParameter × X) := normalFramePositiveDomain Ω ×ˢ (Set.univ:Set X)
  have hD : IsOpen D := hP.prod isOpen_univ
  have hLift : ContDiffOn ℝ ∞ (normalFrameOrthonormalLift g) D :=
    (hNorm.comp contDiffOn_fst (fun p hp => hp.1)).prodMk contDiffOn_snd
  let U := D ∩ normalFrameOrthonormalLift g ⁻¹' S
  have hU : IsOpen U := hLift.continuousOn.isOpen_inter_preimage hD hS
  have hPD : (y,(s,L)) ∈ normalFramePositiveDomain Ω :=
    normalFramePositiveDomain_mem_of_orthonormal g (y,(s,L)) (hN.center_mem hy) he
  have hFix := normalFrameOrthonormalLift_eq_self g ((y,(s,L)),z) he
  have hMem : ((y,(s,L)),z) ∈ U := ⟨⟨hPD,mem_univ z⟩,by simpa only [mem_preimage,hFix] using hHere⟩
  refine ⟨U,hU,hMem,?_⟩
  rw [orthonormalNormalFrameCoefficient_eq_comp]
  exact hRaw.comp (hLift.mono inter_subset_left) (fun p hp => hp.2)

end ShrinkingSpheres
