import Proof.LocalFourthFlowVariation
import Proof.NormalJointThirdVariation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The actual normal geodesic phase satisfies the genuine fourth joint
    variational equation on every admitted strict initial disk. -/
theorem NormalCoordinates.hasDerivAt_joint_fourth_variation {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (v : X) (h k l m : X × X)
    (hv : metricPair g y v v < (R y)^2) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => fourthParameterVariation (normalJointPhase expMap) h k l m ((y,v),s))
      (fourthParameterVariationRhs (normalJointPhase expMap) (coordinateGeodesicSpray g) h k l m ((y,v),t)) t := by
  have hRy := hR.continuousAt (hY.mem_nhds hy)
  have hDisk := hN.eventually_joint_strict_disk hY hΩ hg hy hRy v hv
  have hPhase := hN.contDiffAt_jointPhase hy v t
    (smul_mem_disk_of_mem g y v (R y) t hv.le ht)
  have hPos : (normalJointPhase expMap ((y,v),t)).1 ∈ Ω := hN.path_image hy v hv.le ht
  have hSpray := hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ hPos
  have hTTime : (fun p => fderiv ℝ (thirdParameterVariation (normalJointPhase expMap) h k l) (p,t) (0,1)) =ᶠ[𝓝 (y,v)]
      fun p => thirdParameterVariationRhs (normalJointPhase expMap) (coordinateGeodesicSpray g) h k l (p,t) := by
    filter_upwards [hDisk] with p hp
    have hPx := hN.contDiffAt_jointPhase hp.1 p.2 t
      (smul_mem_disk_of_mem g p.1 p.2 (R p.1) t hp.2.le ht)
    have hT := contDiffAt_thirdParameterVariation (normalJointPhase expMap) h k l (p,t) hPx
    have hVar := hN.hasDerivAt_joint_third_variation hY hΩ hg hK hR hp.1 p.2 h k l hp.2 ht
    exact (hasDerivAt_time_slice (thirdParameterVariation (normalJointPhase expMap) h k l) p t
      (hT.differentiableAt (by simp))).unique hVar
  exact hasDerivAt_fourth_parameter_variation (normalJointPhase expMap)
    (coordinateGeodesicSpray g) (y,v) h k l m t hPhase hSpray hTTime

/-- The actual initial phase is affine in its initial position/velocity,
    hence its fourth initial variation vanishes exactly. -/
lemma NormalCoordinates.joint_fourth_variation_zero {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : X} (hy : y ∈ Y) (v : X) (h k l m : X × X)
    (hv : metricPair g y v v < (R y)^2) :
    fourthParameterVariation (normalJointPhase expMap) h k l m ((y,v),0) = 0 := by
  have hDisk := hN.eventually_joint_strict_disk hY hΩ hg hy
    (hR.continuousAt (hY.mem_nhds hy)) v hv
  have hPhase := hN.contDiffAt_jointPhase hy v 0
    (by simpa only [zero_smul] using zero_mem_disk g y (R y))
  have hT := contDiffAt_thirdParameterVariation (normalJointPhase expMap) h k l ((y,v),0) hPhase
  have hEq : (fun p : X × X => thirdParameterVariation (normalJointPhase expMap) h k l (p,0)) =ᶠ[𝓝 (y,v)]
      fun _ => 0 := by
    filter_upwards [hDisk] with p hp
    exact hN.joint_third_variation_zero hY hΩ hg hR hp.1 p.2 h k l hp.2
  rw [fourthParameterVariation,← fderiv_base_slice_of_contDiffAt _ (y,v) m 0 hT,hEq.fderiv_eq]
  simp

end ShrinkingSpheres
