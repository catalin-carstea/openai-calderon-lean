import Proof.MidpointHalfCompatibility
import Proof.HalfPhysicalAdjoint
import Proof.NativeRelativeTrueAdjointDomain
import Proof.NativeRelativeFullAdjointJets
import Proof.SphereSobolevOperatorExt
import Proof.FlatDegreeCompatibility
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma half_coarse_compatible_of_physical_blocks
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (L (sphereSobolevSingleL (1/2:ℝ) n z)) =
        coarsePhysicalHarmonicBlock R m n z) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply sphereSobolev_clm_ext_on_single 1
  intro n z
  apply sphereSobolev_ext (-(1/2:ℝ))
  intro m
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,sphereSobolevInclusionL_single]
  exact (hL m n z).symm

lemma half_physical_blocks_of_coarse_compatible
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (L (sphereSobolevSingleL (1/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock R m n z := by
  have hh := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (A (sphereSobolevSingleL 1 n z))) hL
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,sphereSobolevInclusionL_single,
    coarsePhysicalHarmonicBlock] using hh.symm

namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

def fullHalfResponse (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported p+fixedLowRadialL

def fullHalfAdjoint (t : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (t.fullHalfResponse p).adjoint

lemma SymmetricAdjointDomain.lowResponse_coarse_compatible {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (t.response p) =
      (commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported p).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p
  have hLH := actual_radial_endpoints_compatible (commonSupportEnergyMemLp q.a q.smooth p)
    (V.coercive p hp) F
    (fun z _ => congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))
    (V.strong p hp) (V.normal p hp)
  exact midpoint_half_compatible_of_common_high (t.response p) _ (actualHighRadialErrorL F)
    (t.highRestriction p (V.sub hp)).symm hLH

lemma SymmetricAdjointDomain.fullHalfResponse_coarse_compatible {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (t.response p+sphereSobolevDegreeL) =
      (t.fullHalfResponse p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hR := V.lowResponse_coarse_compatible p hp
  apply ContinuousLinearMap.ext
  intro u
  have hRv := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) hR
  have hDv := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) fixedLowRadialL_degree_compatible
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (t.response p u+sphereSobolevDegreeL u) = _
  simpa only [map_add,ContinuousLinearMap.comp_apply,_root_.add_apply,fullHalfResponse] using
    congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x+y) hRv hDv.symm

lemma SymmetricAdjointDomain.fullHalfResponse_physical_block {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (t.fullHalfResponse p (sphereSobolevSingleL (1/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock (t.response p+sphereSobolevDegreeL) m n z := by
  have hh := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    sphereSobolevCoefficientL (-(1/2:ℝ)) m (A (sphereSobolevSingleL 1 n z)))
      (V.fullHalfResponse_coarse_compatible p hp)
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevCoefficientL_inclusion,sphereSobolevInclusionL_single,
    coarsePhysicalHarmonicBlock] using hh.symm

lemma SymmetricAdjointDomain.fullHalfAdjoint_coarse_compatible {t : NormalFrameRelativeResponsePacket q}
    (V : t.SymmetricAdjointDomain) (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (t.fullAdjoint p) =
      (t.fullHalfAdjoint p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) :=
  half_coarse_compatible_of_physical_blocks (t.fullAdjoint p) (t.fullHalfAdjoint p)
    (half_operator_adjoint_physical_block (t.response p+sphereSobolevDegreeL) (t.fullAdjoint p)
      (V.fullPair p hp) (t.fullHalfResponse p) (V.fullHalfResponse_physical_block p hp))
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
