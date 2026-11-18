import Proof.StrictNormalSegmentBounds
import Proof.NormalJointMetricZeroJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Shared actual segment geometry and tensor jets for both center and vertical
    Taylor callers, with the same map, metrics and tangent witnesses. -/
theorem Background.joint_normal_metric_segment_jets {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v u w : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    (g' : MetricField) (hmem : g' ∈ ({g,g₁}:Set MetricField)) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ContDiffAt ℝ ∞ (jointNormalMetricPair g' expMap u w) (y,t • v) ∧
      ∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (jointNormalMetricPair g' expMap u w) (y,t • v)‖ ≤
        backgroundJointNormalMetricJetBudget hm K M*‖u‖*‖w‖ := by
  have hg' : Elliptic Ω K g' := by
    simp only [mem_insert_iff,mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact h.1
    · exact h.2.1
  intro t ht
  have htV := smul_mem_disk_of_mem g y v (R y) t hv.le ht
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hExp : ContDiffAt ℝ ∞ expMap (y,t • v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,htV⟩))
  refine ⟨contDiffAt_jointNormalMetricPair g' expMap (y,t • v) u w hExp
    (fun i j => (hg'.1 i j).contDiffAt (hΩ.mem_nhds (hN.path_image hy v hv.le ht))),?_⟩
  obtain ⟨htStrict,htNorm⟩ := h.1.strict_normal_segment_bounds hK (hN.center_mem hy) v (R y) hv hv1 ht
  exact h.joint_normal_metric_jet_bound hY hΩ hK hm hN hR hy (t • v) u w htStrict htNorm g' hmem

end ShrinkingSpheres
