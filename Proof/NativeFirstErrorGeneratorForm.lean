import Proof.FirstErrorGeneratorAlgebra
import Proof.NativeFirstAdjointError
import Proof.NativeFullAdjointTaylorDecomposition
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

/-- Exact first-error form with one shared unbounded Taylor remainder.
The other unbounded generators are the fixed degree and rotations in the
closed tangential operator. No self-commutator estimate is assumed. -/
lemma first_error_generator_normal_form
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) :
    s.firstAdjointErrorFamily C p=
      (s.response.adjointTaylor p).comp
        (((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p) • relativeCoframeNormalSobolevL 1 d.γ a p+
          (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a) • ContinuousLinearMap.id ℝ (SphereSobolev 1)+
          ((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p) •
            closedVectorNormalMultiplier (fun j => (C j).closed p))+
      ((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p) •
        (closedVectorTangentialAdjoint (fun j => (C j).closed p)+
          sphereSobolevDegreeL.comp (closedVectorNormalMultiplier (fun j => (C j).closed p)))+
      (((d.radius y)⁻¹*normalFrameRelativeInverseRadiusFactor p)*d.radius y) •
        (((radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
          (sphereSobolevInclusionL 1 0 (by norm_num))).comp
            (closedVectorNormalMultiplier (fun j => (C j).closed p))) := by
  let r : ℝ := d.radius y
  let invR : ℝ := normalFrameRelativeInverseRadiusFactor p
  let α : ℝ := r⁻¹*invR
  let b : ℝ := fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a
  let P : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := s.response.adjointTaylor p
  let D : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevDegreeL
  let B : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num))
  let A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := s.response.fullAdjoint p
  let Na : SphereSobolev 1 →L[ℝ] SphereSobolev 1 := relativeCoframeNormalSobolevL 1 d.γ a p
  let Nc : SphereSobolev 1 →L[ℝ] SphereSobolev 1 := closedVectorNormalMultiplier (fun j => (C j).closed p)
  let T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := closedVectorTangentialAdjoint (fun j => (C j).closed p)
  have hFull : A=P+D+r • B := s.response.fullAdjoint_taylor_decomposition p
  have hStart : s.firstAdjointErrorFamily C p=α • P.comp Na+b • P+α • (T+A.comp Nc) := by
    have hh : s.firstAdjointErrorFamily C p=
        (r⁻¹ • (invR • P.comp Na)+b • P)+r⁻¹ • (invR • (T+A.comp Nc)) := rfl
    simpa only [smul_smul] using hh
  have hExpand := congrArg (fun Z : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    α • P.comp Na+b • P+α • (T+Z.comp Nc)) hFull
  exact hStart.trans (hExpand.trans (first_error_generator_algebra P D B T Na Nc r α b))
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
