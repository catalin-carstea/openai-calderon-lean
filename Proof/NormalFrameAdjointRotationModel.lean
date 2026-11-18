import Proof.NormalFrameRadialAdjointTaylorModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local irreducible] sphereSobolevDegreeL

lemma Background.normalFrameRadialAdjointTaylorFamily_rotation {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (Da : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i j : I) (t : ℝ) :
    normalFrameRadialAdjointTaylorFamily d Da (normalFrameRotationCurve d.frame d.radius y i j t) =
      Da (normalFrameRotationCurve d.frame d.radius y i j t)-sphereSobolevDegreeL-d.radius y •
        (coarseFirstRadialVariationL 1 ((firstDensityLogCovector d y).comp
          (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).adjoint.comp
          (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have hB : radialCorrectionCovectorL (normalFrameFirstCovector d.γ d.g₁
      (normalFrameRotationCurve d.frame d.radius y i j t)) =
      coarseFirstRadialVariationL 1 ((firstDensityLogCovector d y).comp
        (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap) := by
    rw [h.normalFrameFirstCovector_rotation hΩ hK hy,radialCorrectionCovectorL_apply]
  exact congrArg (fun B : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    Da (normalFrameRotationCurve d.frame d.radius y i j t)-sphereSobolevDegreeL-d.radius y •
      B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) hB

end ShrinkingSpheres
