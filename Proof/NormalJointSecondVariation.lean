import Proof.LocalSecondFlowVariation
import Proof.NormalJointVariationBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The genuine normal flow satisfies the second variational equation in both
    center and velocity. Continuity of the admitted radius is needed only at
    the original center, to supply a local ODE germ. -/
theorem NormalCoordinates.hasDerivAt_joint_second_variation {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : X) (h k : X × X)
    (hv : metricPair g y v v < (R y)^2) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => secondParameterVariation (normalJointPhase expMap) h k ((y,v),s))
      (fderiv ℝ (coordinateGeodesicSpray g) (normalJointPhase expMap ((y,v),t))
          (secondParameterVariation (normalJointPhase expMap) h k ((y,v),t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalJointPhase expMap ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) k ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) h ((y,v),t))) t := by
  have hDisk := hN.eventually_joint_disk hY hΩ hg hy hR v hv
  have hPhase := hN.contDiffAt_jointPhase hy v t
    (smul_mem_disk_of_mem g y v (R y) t hv.le ht)
  have hPos : (normalJointPhase expMap ((y,v),t)).1 ∈ Ω := hN.path_image hy v hv.le ht
  have hSpray := hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ hPos
  have hODE : (fun p => fderiv ℝ (normalJointPhase expMap) (p,t) (0,1)) =ᶠ[𝓝 (y,v)]
      (fun p => coordinateGeodesicSpray g (normalJointPhase expMap (p,t))) := by
    filter_upwards [hDisk] with p hp
    have hPx := hN.contDiffAt_jointPhase hp.1 p.2 t
      (smul_mem_disk_of_mem g p.1 p.2 (R p.1) t hp.2 ht)
    exact (hasDerivAt_time_slice (normalJointPhase expMap) p t
      (hPx.differentiableAt (by simp))).unique (hN.hasDerivAt_jointPhase hp.1 p.2 hp.2 ht)
  have hJTime : (fun p => fderiv ℝ (firstParameterVariation (normalJointPhase expMap) h) (p,t) (0,1))
      =ᶠ[𝓝 (y,v)] (fun p => fderiv ℝ (coordinateGeodesicSpray g) (normalJointPhase expMap (p,t))
        (firstParameterVariation (normalJointPhase expMap) h (p,t))) := by
    filter_upwards [hDisk,hODE.eventuallyEq_nhds] with p hp hODEp
    have hPx := hN.contDiffAt_jointPhase hp.1 p.2 t
      (smul_mem_disk_of_mem g p.1 p.2 (R p.1) t hp.2 ht)
    have hJ := contDiffAt_firstParameterVariation (normalJointPhase expMap) h (p,t) hPx
    have hPPos : (normalJointPhase expMap (p,t)).1 ∈ Ω := hN.path_image hp.1 p.2 hp.2 ht
    have hSp := (hg.contDiffAt_coordinateGeodesicSpray hΩ hK
      (normalJointPhase expMap (p,t)) hPPos).differentiableAt (by simp)
    have hVar := hasDerivAt_parameter_variation (normalJointPhase expMap)
      (coordinateGeodesicSpray g) p h t hPx hSp hODEp
    exact (hasDerivAt_time_slice (firstParameterVariation (normalJointPhase expMap) h) p t
      (hJ.differentiableAt (by simp))).unique hVar
  exact hasDerivAt_second_parameter_variation (normalJointPhase expMap)
    (coordinateGeodesicSpray g) (y,v) h k t hPhase hSpray hJTime

/-- Every joint second variation starts at zero, including mixed center and
    velocity directions. No regularity of the radius away from the center is used. -/
lemma NormalCoordinates.joint_second_variation_zero {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : X) (h k : X × X)
    (hv : metricPair g y v v < (R y)^2) :
    secondParameterVariation (normalJointPhase expMap) h k ((y,v),0) = 0 := by
  have hDisk := hN.eventually_joint_disk hY hΩ hg hy hR v hv
  have hPhase := hN.contDiffAt_jointPhase hy v 0
    (by simpa only [zero_smul] using zero_mem_disk g y (R y))
  have hJ := contDiffAt_firstParameterVariation (normalJointPhase expMap) h ((y,v),0) hPhase
  have hEq : (fun p : X × X => normalJointPhase expMap (p,0)) =ᶠ[𝓝 (y,v)] (fun p => p) := by
    filter_upwards [hDisk] with p hp
    exact (hN.jointPhase_eq_phase hp.1 p.2 0
      (by simpa only [zero_smul] using zero_mem_disk g p.1 (R p.1))).trans
      (hN.phase_zero hp.1 p.2 hp.2)
  have hJEq : (fun p : X × X => firstParameterVariation (normalJointPhase expMap) h (p,0))
      =ᶠ[𝓝 (y,v)] (fun _ => h) := by
    filter_upwards [hDisk,hEq.fderiv (𝕜:=ℝ)] with p hp hd
    have hPx := hN.contDiffAt_jointPhase hp.1 p.2 0
      (by simpa only [zero_smul] using zero_mem_disk g p.1 (R p.1))
    rw [firstParameterVariation,← fderiv_base_slice_of_contDiffAt _ p h 0 hPx,hd]
    exact congrArg (fun L : (X × X) →L[ℝ] X × X => L h) (hasFDerivAt_id p).fderiv
  rw [secondParameterVariation,← fderiv_base_slice_of_contDiffAt _ (y,v) k 0 hJ,hJEq.fderiv_eq]
  simp

end ShrinkingSpheres
