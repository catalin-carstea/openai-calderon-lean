import Proof.FirstErrorScalarCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

lemma first_error_scalar_generator_form
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (p : NormalFrameRelativeParameter) :
    s.firstAdjointErrorFamily C p=
      (∑ k,(taylorGeneratorCoarse (s.response.adjointTaylor p) k).comp
        (closedOneBoundaryScalarMultiplierL (firstErrorScalarCoefficients Q0
          ((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p)
          (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)
          (fun j => normalFrameRelativeCoframeValue d.γ a j p)
          (fun j => (C j).closed p) k)))+
      (((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p)*d.radius y) •
        (((radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
          (sphereSobolevInclusionL 1 0 (by norm_num))).comp
            (closedVectorNormalMultiplier (fun j => (C j).closed p))) := by
  have hF := firstErrorScalarCoefficients_coarse_form Q0 hQ0 (s.response.adjointTaylor p)
    ((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p)
    (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)
    (fun j => normalFrameRelativeCoframeValue d.γ a j p) (fun j => (C j).closed p)
  exact (s.first_error_generator_normal_form C p).trans (congrArg
    (fun Z : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => Z+
      (((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p)*d.radius y) •
        (((radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
          (sphereSobolevInclusionL 1 0 (by norm_num))).comp
            (closedVectorNormalMultiplier (fun j => (C j).closed p)))) hF.symm)
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
