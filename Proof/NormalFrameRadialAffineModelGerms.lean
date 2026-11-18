import Proof.NormalFrameRadialReorder
import Proof.NormalizedFrameRadialTaylorZeroJets
import Proof.Archive.CompactRadialRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

def normalFrameRadialFirstModel (g g₁ : MetricField) (p : NormalFrameSpatialParameter) : Mat :=
  orthonormalFirstRadialModel g g₁ ((p.1.1,(0,p.1.2)),p.2)

def normalFrameRadialRemainder (g g₁ : MetricField) (E : X × X → X)
    (q : NormalFrameSpatialParameter × ℝ) : Mat :=
  orthonormalCoefficientRadialRemainder g g₁ E (normalFrameRadialReorderL q)

lemma normalFrameRadialRemainder_apply (g g₁ : MetricField) (E : X × X → X)
    (p : NormalFrameSpatialParameter) (r : ℝ) :
    normalFrameRadialRemainder g g₁ E (p,r) =
      normalFrameRadialCoefficient g g₁ E (p,r)-(1:Mat)-r • normalFrameRadialFirstModel g g₁ p := rfl

/-- The affine Taylor model is exactly the previously proved geometric
    first model as a germ in all center/frame/spatial parameters. -/
theorem Background.normalFrameRadial_affine_model_germs {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    (p : NormalFrameSpatialParameter) (hy : p.1.1 ∈ Y)
    (hp : (p.1.1,(0,p.1.2)) ∈ normalFramePositiveDomain Ω)
    {U : Set (NormalFrameSpatialParameter × ℝ)} (hU : IsOpen U) (hMem : (p,0) ∈ U)
    (hF : ContDiffOn ℝ ∞ (normalFrameRadialCoefficient g g₁ E) U) :
    ((fun q => normalFrameRadialCoefficient g g₁ E (q,0)) =ᶠ[𝓝 p] (fun _ => (1:Mat))) ∧
    ((fun q => radialFirstDerivative (normalFrameRadialCoefficient g g₁ E) (q,0)) =ᶠ[𝓝 p]
      normalFrameRadialFirstModel g g₁) := by
  have hCenter : Continuous (fun q : NormalFrameSpatialParameter => q.1.1) := continuous_fst.fst
  have hPositive : Continuous (fun q : NormalFrameSpatialParameter => (q.1.1,((0:ℝ),q.1.2))) :=
    continuous_fst.fst.prodMk (continuous_const.prodMk continuous_fst.snd)
  have hTime : Continuous (fun q : NormalFrameSpatialParameter => (q,(0:ℝ))) := continuous_id.prodMk continuous_const
  have hNearY : ∀ᶠ q in 𝓝 p,q.1.1 ∈ Y := hCenter.continuousAt.eventually (hY.mem_nhds hy)
  have hNearP : ∀ᶠ q in 𝓝 p,(q.1.1,(0,q.1.2)) ∈ normalFramePositiveDomain Ω :=
    hPositive.continuousAt.eventually ((isOpen_normalFramePositiveDomain hΩ).mem_nhds hp)
  have hNearU : ∀ᶠ q in 𝓝 p,(q,0) ∈ U := hTime.continuousAt.eventually (hU.mem_nhds hMem)
  have hData : ∀ᶠ q in 𝓝 p,
      normalFrameRadialCoefficient g g₁ E (q,0) = (1:Mat) ∧
      radialFirstDerivative (normalFrameRadialCoefficient g g₁ E) (q,0) = normalFrameRadialFirstModel g g₁ q := by
    filter_upwards [hNearY,hNearP,hNearU] with q hqy hqp hqu
    have hZero := h.orthonormalCoefficient_radius_zero hK hN hqy hqp q.2
    have hFirst := h.orthonormalCoefficient_first_radial hY hΩ hK hN hqy hqp q.2
    have hDiff := (hF.contDiffAt (hU.mem_nhds hqu)).differentiableAt (by simp)
    have hTimeDeriv := hasDerivAt_time_slice (normalFrameRadialCoefficient g g₁ E) q 0 hDiff
    change HasDerivAt (fun s => normalFrameRadialCoefficient g g₁ E (q,s))
      (normalFrameRadialFirstModel g g₁ q) 0 at hFirst
    exact ⟨hZero,hTimeDeriv.unique hFirst⟩
  exact ⟨hData.mono (fun _ hq => hq.1),hData.mono (fun _ hq => hq.2)⟩

theorem normalFrameRadialRemainder_eq_affine_germ
    (g g₁ : MetricField) (E : X × X → X) (p : NormalFrameSpatialParameter) (r : ℝ)
    (hZero : (fun q => normalFrameRadialCoefficient g g₁ E (q,0)) =ᶠ[𝓝 p] (fun _ => (1:Mat)))
    (hFirst : (fun q => radialFirstDerivative (normalFrameRadialCoefficient g g₁ E) (q,0)) =ᶠ[𝓝 p]
      normalFrameRadialFirstModel g g₁) :
    (fun q => normalFrameRadialRemainder g g₁ E (q,r)) =ᶠ[𝓝 p]
      (fun q => normalFrameRadialCoefficient g g₁ E (q,r)-normalFrameRadialCoefficient g g₁ E (q,0)-
        r • radialFirstDerivative (normalFrameRadialCoefficient g g₁ E) (q,0)) := by
  filter_upwards [hZero,hFirst] with q hq0 hq1
  rw [normalFrameRadialRemainder_apply,hq0,hq1]

end ShrinkingSpheres
