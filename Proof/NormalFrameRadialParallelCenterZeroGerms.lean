import Proof.NormalizedParallelCenterZeroJets
import Proof.UniformNormalFrameParallelCenterHigherJets
import Proof.NormalFrameRadialReorder
import Proof.Archive.CompactRadialRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

def normalFrameRadialParallelCenter (g : MetricField) (E : X × X → X) :
    NormalFrameSpatialParameter × ℝ → (X →L[ℝ] X) :=
  normalFrameParallelCenterJacobian g E ∘ normalFrameRadialReorderL

/-- Both lower radial coefficients vanish identically near the chosen
    center/frame/spatial parameter. No orthonormality of nearby frames is needed. -/
theorem Background.normalFrameRadialParallelCenter_zero_germs {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 3 ≤ m) {E : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g E R) (hR : ∀ y ∈ Y,ContinuousAt R y)
    (p : NormalFrameSpatialParameter) (hy : p.1.1 ∈ Y)
    {U : Set (NormalFrameSpatialParameter × ℝ)} (hU : IsOpen U) (hMem : (p,0) ∈ U)
    (hF : ContDiffOn ℝ ∞ (normalFrameRadialParallelCenter g E) U) :
    ((fun q => normalFrameRadialParallelCenter g E (q,0)) =ᶠ[𝓝 p]
      (fun _ => ContinuousLinearMap.id ℝ X)) ∧
    ((fun q => radialFirstDerivative (normalFrameRadialParallelCenter g E) (q,0)) =ᶠ[𝓝 p]
      (fun _ => 0)) := by
  have hNearY : ∀ᶠ q : NormalFrameSpatialParameter in 𝓝 p,q.1.1 ∈ Y :=
    (continuous_fst.fst.continuousAt).eventually (hY.mem_nhds hy)
  have hNearU : ∀ᶠ q : NormalFrameSpatialParameter in 𝓝 p,(q,0) ∈ U :=
    (continuous_id.prodMk continuous_const).continuousAt.eventually (hU.mem_nhds hMem)
  have hData : ∀ᶠ q : NormalFrameSpatialParameter in 𝓝 p,
      normalFrameRadialParallelCenter g E (q,0) = ContinuousLinearMap.id ℝ X ∧
      radialFirstDerivative (normalFrameRadialParallelCenter g E) (q,0) = 0 := by
    filter_upwards [hNearY,hNearU] with q hqy hqu
    obtain ⟨hZero,hFirst⟩ := h.normalizedParallelCenter_zero_jets hY hΩ hK hm hN hqy (hR _ hqy)
    have hG : DifferentiableAt ℝ (normalizedParallelCenterJacobian g E q.1.1) 0 :=
      (hN.contDiffAt_normalizedParallelCenterJacobian hqy 0 (zero_mem_disk _ _ _)).differentiableAt (by simp)
    have hScaled : HasDerivAt (fun s : ℝ => s • q.1.2 q.2) (q.1.2 q.2) 0 := by
      simpa only [Function.id_def,one_smul] using (hasDerivAt_id (0:ℝ)).smul_const (q.1.2 q.2)
    have hG0 : HasFDerivAt (normalizedParallelCenterJacobian g E q.1.1) (0 : X →L[ℝ] (X →L[ℝ] X)) (0:X) := by
      rw [← hFirst]
      exact hG.hasFDerivAt
    have hG0' : HasFDerivAt (normalizedParallelCenterJacobian g E q.1.1)
        (0 : X →L[ℝ] (X →L[ℝ] X)) ((0:ℝ) • q.1.2 q.2) := by simpa only [zero_smul] using hG0
    have hActual := hG0'.comp_hasDerivAt 0 hScaled
    have hActual0 : HasDerivAt (fun s : ℝ => normalFrameRadialParallelCenter g E (q,s)) 0 0 := by
      change HasDerivAt (fun s : ℝ => normalizedParallelCenterJacobian g E q.1.1 (s • q.1.2 q.2)) 0 0
      simpa only [zero_smul,Function.comp_def,zero_apply] using hActual
    have hTime := hasDerivAt_time_slice (normalFrameRadialParallelCenter g E) q 0
      ((hF.contDiffAt (hU.mem_nhds hqu)).differentiableAt (by simp))
    refine ⟨?_,hTime.unique hActual0⟩
    change normalizedParallelCenterJacobian g E q.1.1 (0 • q.1.2 q.2) = _
    simpa only [zero_smul] using hZero
  exact ⟨hData.mono (fun _ hq => hq.1),hData.mono (fun _ hq => hq.2)⟩

end ShrinkingSpheres
