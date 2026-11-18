import Proof.FrameRadiusParameterJet
import Proof.RelativeRadiusCoefficientModel
import Proof.ParallelFirstCoefficientModel
import Proof.ParallelCoefficientZeroSlice

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

/-- The geometric input before choosing any radius profile or frame curve. -/
def normalFrameInput (q : NormalFrameParameter × X) : X × X :=
  (q.1.1,q.1.2.1 • q.1.2.2 q.2)
def normalFrameMetric (g : MetricField) (E : X × X → X) (q : NormalFrameParameter × X) : Mat :=
  fun i j => jointNormalMetricPair g E (q.1.2.2 (axis i)) (q.1.2.2 (axis j)) (normalFrameInput q)
def normalFrameNormalizedCoefficient (g g₁ : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) : Mat :=
  fun i j => (firstMetricDensityFactor g g₁ q.1.1)⁻¹*matrixFamilyCoefficient (normalFrameMetric g₁ E) q i j
def normalFrameFirstCovector (g g₁ : MetricField) (p : NormalFrameParameter) : X →L[ℝ] ℝ :=
  (firstDensityLogDifferential g g₁ p.1).comp p.2.2

lemma normalFrameMetric_framed (g : MetricField) (E : X × X → X) (e : Frame) (y z : X) (s : ℝ) :
    normalFrameMetric g E ((y,(s,frameVectorLinear e y)),z) = framedNormalMetric g e E y s z := by
  ext i j
  simp only [normalFrameMetric,normalFrameInput,frameVectorLinear_apply,frameVector_axis,
    jointNormalMetricPair,framedNormalMetric,normalPullbackMetricPair,normalVerticalJacobian,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]

lemma normalFrameNormalizedCoefficient_framed (g g₁ : MetricField) (E : X × X → X) (e : Frame)
    (y z : X) (s : ℝ) :
    normalFrameNormalizedCoefficient g g₁ E ((y,(s,frameVectorLinear e y)),z) =
      (firstMetricDensityFactor g g₁ y)⁻¹ • principalCoefficient (framedNormalMetric g₁ e E y s) z := by
  ext i j
  simp only [normalFrameNormalizedCoefficient,matrixFamilyCoefficient,matrixFamilyDensity,
    normalFrameMetric_framed,principalCoefficient,OAI.AnisotropicCalderon.vol,Matrix.smul_apply,smul_eq_mul]

lemma normalFrameNormalizedCoefficient_actual (d : Data) (y a z : X) (t : ℝ) :
    normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap (normalFrameActualCurve d.frame d.radius y a t,z) =
      normalizedFirstNormalCoefficient d (y+t • a) z :=
  normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame (y+t • a) z (d.radius (y+t • a))

lemma normalFrameMetric_parallel (g g₁ : MetricField) (E : X × X → X) (e : Frame) (r : X → ℝ)
    (y a z : X) (t : ℝ) :
    normalFrameMetric g₁ E (normalFrameParallelCurve g e r y a t,z) =
      parallelFirstMetric g g₁ E y a (r y) (frameVectorLinear e y) (t,z) := rfl

lemma normalFrameNormalizedCoefficient_parallel (g g₁ : MetricField) (E : X × X → X) (e : Frame)
    (r : X → ℝ) (y a z : X) (t : ℝ) :
    normalFrameNormalizedCoefficient g g₁ E (normalFrameParallelCurve g e r y a t,z) =
      parallelNormalizedFirstCoefficient g g₁ E y a (r y) (frameVectorLinear e y) (t,z) := rfl

lemma normalFrameNormalizedCoefficient_relative_radius (d : Data) (y z : X) (t : ℝ) :
    normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap (normalFrameRadiusCurve d.frame d.radius y t,z) =
      relativeDilationFamily (normalizedFirstNormalCoefficient d y) (t,z) := by
  rw [relativeDilation_normalized_coefficient]
  unfold normalFrameRadiusCurve firstNormalCoefficientAtRadius
  rw [normalFrameNormalizedCoefficient_framed,mul_comm (1+t) (d.radius y)]

lemma normalFrameFirstCovector_parallel (g g₁ : MetricField) (e : Frame) (r : X → ℝ)
    (y a : X) (t : ℝ) :
    normalFrameFirstCovector g g₁ (normalFrameParallelCurve g e r y a t) =
      parallelFirstCoefficientCovector g g₁ y a (frameVectorLinear e y) t := rfl

lemma contDiff_normalFrameInput : ContDiff ℝ ∞ normalFrameInput :=
  contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.smul (contDiff_fst.snd.snd.clm_apply contDiff_snd))

lemma contDiffAt_normalFrameMetric (g : MetricField) (E : X × X → X) (q : NormalFrameParameter × X)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g E) (normalFrameInput q)) :
    ContDiffAt ℝ ∞ (normalFrameMetric g E) q := by
  have hL : ContDiff ℝ ∞ (fun p : NormalFrameParameter × X => p.1.2.2) := contDiff_fst.snd.snd
  have hTensor := hT.comp q contDiff_normalFrameInput.contDiffAt
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hSlots := (hTensor.clm_apply (hL.clm_apply (contDiff_const (c:=axis i))).contDiffAt).clm_apply
    (hL.clm_apply (contDiff_const (c:=axis j))).contDiffAt
  simpa only [Function.comp_def,normalJointMetricTensor_apply,normalFrameMetric] using hSlots

lemma contDiffAt_normalFrameNormalizedCoefficient (g g₁ : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X)
    (hT : ContDiffAt ℝ ∞ (normalJointMetricTensor g₁ E) (normalFrameInput q))
    (hc : ContDiffAt ℝ ∞ (firstMetricDensityFactor g g₁) q.1.1)
    (hPos : 0 < (normalFrameMetric g₁ E q).det) :
    ContDiffAt ℝ ∞ (normalFrameNormalizedCoefficient g g₁ E) q := by
  have hMetric := contDiffAt_normalFrameMetric g₁ E q hT
  have hC0 : ContDiffAt ℝ ∞ (fun p : NormalFrameParameter × X => firstMetricDensityFactor g g₁ p.1.1) q := ContDiffAt.comp (f := fun p : NormalFrameParameter × X => p.1.1) (g := firstMetricDensityFactor g g₁) q hc contDiffAt_fst.fst
  have hC := hC0.inv (firstMetricDensityFactor_pos g g₁ q.1.1).ne'
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hA := contDiffAt_matrix_density_inverse_entry (normalFrameMetric g₁ E) q
    (fun k l => contDiffAt_pi.mp (contDiffAt_pi.mp hMetric k) l) hPos i j
  exact hC.mul hA

end ShrinkingSpheres
