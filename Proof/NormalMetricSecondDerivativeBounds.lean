import Proof.MetricPullbackSecondDerivativeBounds
import Proof.NormalVerticalThirdDerivative
import Proof.NormalMetricDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Uniform second initial-velocity derivative of the actual normal pullback
    metric, before angular scaling. -/
theorem Background.normal_metric_velocity_second_derivative_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 4 ≤ m) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (v u w : X) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    (hJNorm : ‖normalVerticalJacobian expMap y v‖ ≤ 2)
    (g' : MetricField) (hg' : Elliptic Ω K g') (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hMetric1 : ∀ i j,‖fderiv ℝ (fun x => g' x i j) (expMap (y,v))‖ ≤ M1)
    (hMetric2 : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g' x i j)) (expMap (y,v))‖ ≤ M2) :
    ‖fderiv ℝ (fderiv ℝ (fun z => metricPair g' (expMap (y,z))
      (normalVerticalJacobian expMap y z u) (normalVerticalJacobian expMap y z w))) v‖ ≤
      9*(16*M2+20*M1*backgroundSecondNormalVariationBudget (by omega) K M+
        4*K*backgroundThirdNormalVariationBudget hm K M+
        2*K*(backgroundSecondNormalVariationBudget (by omega) K M)^2)*‖u‖*‖w‖ := by
  let S := interior (disk g y (R y))
  let E : X → X := fun z => expMap (y,z)
  let J := normalVerticalJacobian expMap y
  let N2 := backgroundSecondNormalVariationBudget (show 3 ≤ m by omega) K M
  let N3 := backgroundThirdNormalVariationBudget hm K M
  have hvS : v ∈ S := mem_interior_disk_of_metricPair_lt g y v (R y) hv
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffOn ℝ ∞ E S := by
    intro z hz
    have hzU : (y,z) ∈ U := hTube ⟨hy,interior_subset hz⟩
    have hExp : ContDiffAt ℝ ∞ expMap (y,z) := hReg.contDiffAt (hU.mem_nhds hzU)
    have hSlice : ContDiffAt ℝ ∞ E z :=
      hExp.comp z (contDiffAt_const.prodMk contDiffAt_id)
    exact hSlice.contDiffWithinAt
  have hJ : ContDiffOn ℝ ∞ J S := fun z hz =>
    (hN.contDiffAt_normalVerticalJacobian hy z (interior_subset hz)).contDiffWithinAt
  have hImage : ∀ z ∈ S,E z ∈ Ω := by
    intro z hz
    simpa only [E,one_smul] using hN.path_image hy z (interior_subset hz)
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hDE : fderiv ℝ E v = J v :=
    (hN.hasFDerivAt_velocity_slice hy v hv.le).fderiv
  have hDDE : fderiv ℝ (fderiv ℝ E) v = fderiv ℝ J v := by
    have hEq : fderiv ℝ E =ᶠ[𝓝 v] J := by
      filter_upwards [isOpen_interior.mem_nhds hvS] with z hz
      exact (hN.hasFDerivAt_velocity_slice hy z (interior_subset hz)).fderiv
    exact hEq.fderiv_eq
  have hN2 : 0 ≤ N2 := by
    dsimp [N2,backgroundSecondNormalVariationBudget,secondNormalVariationBudget,
      backgroundSecondConnectionBudget,secondConnectionBudget,backgroundConnectionDerivativeBudget]
    positivity
  have hN3 : 0 ≤ N3 := by
    dsimp [N3,backgroundThirdNormalVariationBudget,thirdNormalVariationBudget,secondNormalVariationBudget,
      backgroundThirdConnectionBudget,thirdConnectionBudget,backgroundSecondConnectionBudget,
      secondConnectionBudget,backgroundConnectionDerivativeBudget]
    positivity
  have hDJ : ‖fderiv ℝ J v‖ ≤ N2 :=
    h.normalVerticalJacobian_derivative_bound hΩ hK (by omega) hN hy v hvS hv1
  have hDDJ : ‖fderiv ℝ (fderiv ℝ J) v‖ ≤ N3 :=
    h.normalVerticalJacobian_second_derivative_bound hY hΩ hK hm hN hR hy v hv hv1
  have hb := norm_second_fderiv_metric_pullback_le isOpen_interior hΩ hg' hK E J hE hJ hImage hvS u w
    M1 M2 2 N2 2 N2 N3 hM1 hM2 (by norm_num) hN2 (by norm_num) hN2 hN3
    hMetric1 hMetric2 (by rw [hDE];exact hJNorm) (by rw [hDDE];exact hDJ) hJNorm hDJ hDDJ
  exact hb.trans_eq (by dsimp only [N2,N3];ring)

end ShrinkingSpheres
