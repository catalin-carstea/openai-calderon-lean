import Proof.ParallelScalarFirstHighSections
import Proof.FrameCovariantCurvatureComm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual physical curvature commutator on the H5/2 supported core.
Its proof transports the already checked H2-to-H0 commutator through the
genuine first/second covariant inclusion graphs and the genuine curvature
inclusion square. No additional curvature or frame-jet premise is used. -/
theorem fiveHalfCovariantDerivative_commutator {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) {y : X} (hy : y ∈ Y) (a b : X) :
    halfSectionCovariantDerivativeL d (fiveHalfCovariantDerivative d U b) y a-
      halfSectionCovariantDerivativeL d (fiveHalfCovariantDerivative d U a) y b=
      frameCurvatureSobolevL (3/2:ℝ) d.γ d.frame y a b
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [map_sub,fiveHalfCovariantDerivative_second_inclusion hY d hg hK he U hU hy,
    fiveHalfCovariantDerivative_second_inclusion hY d hg hK he U hU hy]
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  rw [hg.highSectionCovariantDerivative_commutator hY d hK he hFrame
    (fiveHalfToTwoSection U) hU2.contDiffOn hy a b]
  have hCurvature := DFunLike.congr_fun (frameCurvatureSobolevL_inclusion (3/2:ℝ) 1 (by norm_num)
    d.γ d.frame y a b) (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hCurvature
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hCurvature
  simpa only [frameCurvatureRotationL,fiveHalfToTwoSection,sphereSobolevInclusionL_trans_apply] using hCurvature.symm

end ShrinkingSpheres.ParallelEnergy
