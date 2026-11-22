module

public import Proof.CalderonN.LocalThirdFlowVariation
public import Proof.CalderonN.NormalJointSecondVariation

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalJointThirdVariation.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma NormalCoordinates.eventually_joint_strict_disk {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : (X dim)) (hv : metricPair g y v v < (R y)^2) :
    ∀ᶠ p : (X dim) × (X dim) in 𝓝 (y,v),p.1 ∈ Y ∧ metricPair g p.1 p.2 p.2 < (R p.1)^2 := by
  have hG (i j : (I dim)) : ContDiffAt ℝ ∞ (fun p : (X dim) × (X dim) => g p.1 i j) (y,v) := by
    have hgi : ContDiffAt ℝ ∞ (fun x : (X dim) => g x i j) y :=
      (hg.1 i j).contDiffAt (hΩ.mem_nhds (hN.center_mem hy))
    exact hgi.comp (y,v) contDiffAt_fst
  have hV (i : (I dim)) : ContDiffAt ℝ ∞ (fun p : (X dim) × (X dim) => p.2 i) (y,v) :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp (y,v) contDiffAt_snd
  have hPair : ContinuousAt (fun p : (X dim) × (X dim) => metricPair g p.1 p.2 p.2) (y,v) := by
    exact (ContDiffAt.sum (fun i _ => ContDiffAt.sum
      (fun j _ => ((hG i j).mul (hV i)).mul (hV j)))).continuousAt
  have hDiff := hPair.sub ((hR.comp continuousAt_fst).pow 2)
  have hNear : ∀ᶠ p : (X dim) × (X dim) in 𝓝 (y,v),metricPair g p.1 p.2 p.2-(R p.1)^2 < 0 :=
    hDiff.eventually (isOpen_Iio.mem_nhds (sub_neg.mpr hv))
  have hBase : ∀ᶠ p : (X dim) × (X dim) in 𝓝 (y,v),p.1 ∈ Y :=
    continuousAt_fst.eventually (hY.mem_nhds hy)
  filter_upwards [hNear,hBase] with p hp hpy
  exact ⟨hpy,sub_neg.mp hp⟩

/-- The third variation of the actual normal flow, in arbitrary joint center
    and velocity directions. The radius regularity supplies local admissible disks. -/
theorem NormalCoordinates.hasDerivAt_joint_third_variation {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h k l : (X dim) × (X dim))
    (hv : metricPair g y v v < (R y)^2) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => thirdParameterVariation (normalJointPhase expMap) h k l ((y,v),s))
      (fderiv ℝ (coordinateGeodesicSpray g) (normalJointPhase expMap ((y,v),t))
          (thirdParameterVariation (normalJointPhase expMap) h k l ((y,v),t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalJointPhase expMap ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) l ((y,v),t))
          (secondParameterVariation (normalJointPhase expMap) h k ((y,v),t))+
        fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) (normalJointPhase expMap ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) l ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) k ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) h ((y,v),t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalJointPhase expMap ((y,v),t))
          (secondParameterVariation (normalJointPhase expMap) k l ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) h ((y,v),t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalJointPhase expMap ((y,v),t))
          (firstParameterVariation (normalJointPhase expMap) k ((y,v),t))
          (secondParameterVariation (normalJointPhase expMap) h l ((y,v),t))) t := by
  have hRy := hR.continuousAt (hY.mem_nhds hy)
  have hDisk := hN.eventually_joint_strict_disk hY hΩ hg hy hRy v hv
  have hPhase := hN.contDiffAt_jointPhase hy v t
    (smul_mem_disk_of_mem g y v (R y) t hv.le ht)
  have hPos : (normalJointPhase expMap ((y,v),t)).1 ∈ Ω := hN.path_image hy v hv.le ht
  have hSpray := hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ hPos
  have hSTime : (fun p => fderiv ℝ (secondParameterVariation (normalJointPhase expMap) h k) (p,t) (0,1))
      =ᶠ[𝓝 (y,v)] (fun p => fderiv ℝ (coordinateGeodesicSpray g) (normalJointPhase expMap (p,t))
        (secondParameterVariation (normalJointPhase expMap) h k (p,t))+
        fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) (normalJointPhase expMap (p,t))
          (firstParameterVariation (normalJointPhase expMap) k (p,t))
          (firstParameterVariation (normalJointPhase expMap) h (p,t))) := by
    filter_upwards [hDisk] with p hp
    have hPx := hN.contDiffAt_jointPhase hp.1 p.2 t
      (smul_mem_disk_of_mem g p.1 p.2 (R p.1) t hp.2.le ht)
    have hS := contDiffAt_secondParameterVariation (normalJointPhase expMap) h k (p,t) hPx
    have hVar := hN.hasDerivAt_joint_second_variation hY hΩ hg hK hp.1
      (hR.continuousAt (hY.mem_nhds hp.1)) p.2 h k hp.2 ht
    exact (hasDerivAt_time_slice (secondParameterVariation (normalJointPhase expMap) h k) p t
      (hS.differentiableAt (by simp))).unique hVar
  exact hasDerivAt_third_parameter_variation (normalJointPhase expMap)
    (coordinateGeodesicSpray g) (y,v) h k l t hPhase hSpray hSTime

/-- The joint initial phase is affine, so its third initial variation vanishes. -/
lemma NormalCoordinates.joint_third_variation_zero {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (hR : ContinuousOn R Y)
    {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (h k l : (X dim) × (X dim))
    (hv : metricPair g y v v < (R y)^2) :
    thirdParameterVariation (normalJointPhase expMap) h k l ((y,v),0) = 0 := by
  have hDisk := hN.eventually_joint_strict_disk hY hΩ hg hy
    (hR.continuousAt (hY.mem_nhds hy)) v hv
  have hPhase := hN.contDiffAt_jointPhase hy v 0
    (by simpa only [zero_smul] using zero_mem_disk g y (R y))
  have hS := contDiffAt_secondParameterVariation (normalJointPhase expMap) h k ((y,v),0) hPhase
  have hEq : (fun p : (X dim) × (X dim) => secondParameterVariation (normalJointPhase expMap) h k (p,0))
      =ᶠ[𝓝 (y,v)] (fun _ => 0) := by
    filter_upwards [hDisk] with p hp
    exact hN.joint_second_variation_zero hY hΩ hg hp.1
      (hR.continuousAt (hY.mem_nhds hp.1)) p.2 h k hp.2
  rw [thirdParameterVariation,← fderiv_base_slice_of_contDiffAt _ (y,v) l 0 hS,hEq.fderiv_eq]
  simp

end CalderonN
