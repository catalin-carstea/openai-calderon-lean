import Proof.HalfBoundaryGradientAdjoint
import Proof.NativeFullHalfRegularity
import Proof.NativeCenterDegreeFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
namespace NativeRelativeHorizontalTaylorData

def centerGradientHalfFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (d.radius y)⁻¹ • (normalFrameRelativeInverseRadiusFactor p •
    halfBoundaryGradientAdjoint (fun j => (C j).closed p) (s.response.fullHalfAdjoint p))

lemma centerGradientHalfFamily_coarse_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (s.centerGradientAdjointFamily C p) =
      (s.centerGradientHalfFamily C p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hh := halfBoundaryGradientAdjoint_coarse_compatible (fun j => (C j).closed p)
    (s.response.fullAdjoint p) (s.response.fullHalfAdjoint p) (V.fullHalfAdjoint_coarse_compatible p hp)
  apply ContinuousLinearMap.ext
  intro u
  have hv := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) hh
  simpa only [centerGradientAdjointFamily,centerGradientHalfFamily,ContinuousLinearMap.comp_apply,_root_.smul_apply,map_smul]
    using congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => (d.radius y)⁻¹ • (normalFrameRelativeInverseRadiusFactor p • z)) hv

lemma centerGradientHalfFamily_physical_block
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      (s.centerGradientHalfFamily C p (sphereSobolevSingleL (1/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock (s.centerGradientAdjointFamily C p) m n z :=
  half_physical_blocks_of_coarse_compatible _ _ (s.centerGradientHalfFamily_coarse_compatible C V p hp) m n z

lemma contDiffOn_centerGradientHalfFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) :
    ContDiffOn ℝ ∞ (s.centerGradientHalfFamily C) (s.centerDegreeDomain V) := by
  intro p hp
  have hQ (j : I) : ContDiffAt ℝ ∞ (C j).closed p :=
    (contDiff_commonSupportClosedCoefficientFamily 3 (C j).scalar (C j).smooth (C j).support (C j).compact (C j).supported).contDiffAt
  have hD := V.contDiffOn_fullHalfAdjoint.contDiffAt (V.domainOpen.mem_nhds hp.1)
  have hG := contDiffAt_halfBoundaryGradientAdjoint (fun j => (C j).closed) s.response.fullHalfAdjoint p hQ hD
  have hR : ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor p :=
    (contDiffAt_const.add contDiffAt_snd).inv (ne_of_gt hp.2)
  exact ((hR.smul hG).const_smul (d.radius y)⁻¹).contDiffWithinAt
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
