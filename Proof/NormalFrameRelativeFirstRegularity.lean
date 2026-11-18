import Proof.NormalFrameRelativeGeometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

theorem Background.contDiffOn_normalFrameRelativeFirstCovector {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (normalFrameRelativeFirstCovector g g₁) (normalFrameRelativePositiveDomain Ω) := by
  obtain ⟨hD,hNorm,_⟩ := h.1.normalFrame_normalization_open_domain hΩ hK
  intro p hp
  let κ := fun q : NormalFrameRelativeParameter => (q.1.1,((0:ℝ),q.1.2))
  have hκ : ContDiffAt ℝ ∞ κ p := contDiff_normalFrameRelativeZeroInput.contDiffAt
  have hpD : κ p ∈ normalFramePositiveDomain Ω := hp
  have hParam : ContDiffAt ℝ ∞ (fun q => normalizedOrthonormalFrameParameter g (κ q)) p :=
    (hNorm.contDiffAt (hD.mem_nhds hpD)).comp p hκ
  have hLinear : ContDiffAt ℝ ∞ (fun q => (normalizedOrthonormalFrameParameter g (κ q)).2.2) p := hParam.snd.snd
  have hDensity : ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter =>
      firstDensityLogDifferential g g₁ q.1.1) p :=
    ((h.firstDensityLogDifferential_smooth hK hΩ).contDiffAt (hΩ.mem_nhds hpD.1)).comp p contDiffAt_fst.fst
  have hCov := hDensity.clm_comp hLinear
  have hScalar : ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter => (1:ℝ)+q.2) p :=
    contDiffAt_const.add contDiffAt_snd
  have hResult := hScalar.smul hCov
  exact hResult.contDiffWithinAt

theorem Background.contDiffOn_normalFrameRelativeFirstModel {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (normalFrameRelativeFirstModel g g₁)
      (normalFrameRelativePositiveDomain Ω ×ˢ (Set.univ:Set X)) := by
  have hBase : ContDiffOn ℝ ∞ (fun q : NormalFrameRelativeParameter × X =>
      normalFrameRelativeFirstCovector g g₁ q.1)
      (normalFrameRelativePositiveDomain Ω ×ˢ (Set.univ:Set X)) :=
    (h.contDiffOn_normalFrameRelativeFirstCovector hΩ hK).comp contDiffOn_fst
    (fun q hq => hq.1)
  have hResult := (hBase.clm_apply contDiffOn_snd).smul
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : NormalFrameRelativeParameter × X => (1:Mat))
      (normalFrameRelativePositiveDomain Ω ×ˢ (Set.univ:Set X)))
  apply hResult.congr
  intro q _
  exact normalFrameRelativeFirstModel_scalar g g₁ q

end ShrinkingSpheres
