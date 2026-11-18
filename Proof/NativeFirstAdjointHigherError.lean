import Proof.NativeFirstAdjointError
import Proof.NativeCenterGradientHigherFamily
import Proof.NativeHalfTaylorHigherRegularity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
namespace NativeRelativeHorizontalTaylorData

def firstAdjointHigherErrorFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  relativeFirstAdjointErrorOperator (d.radius y) (normalFrameRelativeInverseRadiusFactor p)
    (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a)
    (Vt.adjointHigherTaylor h hK (by norm_num) p) (relativeCoframeNormalSobolevL (3/2:ℝ) d.γ a p)
    (s.centerGradientHigherFamily C Vc h hK p)

lemma firstAdjointHigherErrorFamily_coarse_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hpt : p ∈ Vt.domain) (hpc : p ∈ s.centerDegreeDomain Vc) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (s.firstAdjointHigherErrorFamily C Vt Vc h hK p) =
      (s.firstAdjointErrorFamily C p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply relativeFirstAdjointErrorOperator_compatible
  · exact Vt.adjointHigherTaylor_coarse_compatible h hK (by norm_num) F0 hF0 p hpt
  · apply ContinuousLinearMap.ext
    intro u
    exact relativeCoframeNormalSobolev_inclusion (3/2:ℝ) 1 (by norm_num) d.γ a p u
  · exact s.centerGradientHigherFamily_coarse_compatible C Vc h hK p hpc
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
