import Proof.CommonSupportCoefficientPointGerms
import Proof.ParallelCoefficientZeroSlice
import Proof.Archive.CommonSupportMatrixInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Joint geometric agreement gives the genuine point coefficient germs needed
    by the existing uniform inverse and Taylor estimates. -/
theorem Background.parallel_coefficient_pair_point_germs {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a : X)
    (A A1 : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → A (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → A1 (t,z) = 0)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,A =ᶠ[𝓝 (0,z)]
      parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a (d.radius y) (frameVectorLinear d.frame y))
    (hRep1 : ∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (0,z)]
      parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) :
    (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (commonSupportMatrixFamily 2 A hA S hS hz 0 i j) =ᶠ[𝓝 z]
        (fun w => normalizedFirstNormalCoefficient d y w i j)) ∧
    ∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (commonSupportMatrixFamily 2 A1 hA1 S1 hS1 hz1 0 i j) =ᶠ[𝓝 z]
        (fun w => firstDensityLogCovector d y w*(1:Mat) i j) := by
  constructor
  · exact commonSupport_coefficient_point_germs A
      (parallelNormalizedFirstCoefficient d.γ d.g₁ d.expMap y a (d.radius y) (frameVectorLinear d.frame y))
      hA S hS hz 0 (normalizedFirstNormalCoefficient d y) hRep
      (fun w => parallelNormalizedFirstCoefficient_zero d y a w)
  · exact commonSupport_coefficient_point_germs A1
      (parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) hA1 S1 hS1 hz1 0
      (fun w => firstDensityLogCovector d y w • (1:Mat)) hRep1
      (fun w => h.parallelFirstCoefficientModel_zero_logCovector hΩ hK hy a w)

end ShrinkingSpheres
