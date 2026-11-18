import Proof.ParallelFirstMetricCoefficient
import Proof.ParallelFirstCoefficientModel
import Proof.NormalizedFirstCoefficientTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma parallelFirstMetric_zero (g g₁ : MetricField) (E : X × X → X) (y a : X) (r : ℝ) (e : Frame) (z : X) :
    parallelFirstMetric g g₁ E y a r (frameVectorLinear e y) (0,z) = framedNormalMetric g₁ e E y r z := by
  ext i j
  simp only [parallelFirstMetric,parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero,
    frameVectorLinear_apply,frameVector_axis,jointNormalMetricPair,framedNormalMetric,normalPullbackMetricPair,
    normalVerticalJacobian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]

lemma parallelNormalizedFirstCoefficient_zero (d : Data) (y a z : X) :
    parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a (d.radius y) (frameVectorLinear d.frame y) (0,z) =
      normalizedFirstNormalCoefficient d y z := by
  ext i j
  unfold parallelNormalizedFirstCoefficient
  simp only [parallelFrameInput,affineParallelFrame_zero,zero_smul,add_zero,matrixFamilyCoefficient,matrixFamilyDensity,
    parallelFirstMetric_zero,normalizedFirstNormalCoefficient,principalCoefficient,OAI.AnisotropicCalderon.vol,
    Matrix.smul_apply,smul_eq_mul]

lemma parallelFirstCoefficientModel_zero (g g₁ : MetricField) (y a : X) (L : X →L[ℝ] X) (z : X) :
    parallelFirstCoefficientModel g g₁ y a L (0,z) = firstDensityLogDifferential g g₁ y (L z) • (1:Mat) := by
  simp only [parallelFirstCoefficientModel,parallelFirstCoefficientCovector,affineParallelFrame_zero,
    zero_smul,add_zero,ContinuousLinearMap.comp_apply]

lemma Background.parallelFirstCoefficientModel_zero_logCovector {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a z : X) :
    parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y) (0,z) = firstDensityLogCovector d y z • (1:Mat) := by
  rw [parallelFirstCoefficientModel_zero,h.firstDensityLogCovector_eq_differential hK hΩ hy]
  rfl

end ShrinkingSpheres
