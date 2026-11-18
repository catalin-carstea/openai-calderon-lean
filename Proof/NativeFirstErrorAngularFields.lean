import Proof.NativeFirstErrorAngularPacket
import Proof.NativeFirstAdjointErrorRegularity
import Proof.CoordinateCombinationAngularFields
import Proof.RelativeCoframeSmoothDomain
import Proof.NativeTaylorAngularRegularity
import Proof.NativeCenterDegreeFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
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

def firstErrorAngularFields
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) : CoarseAngularFields :=
  (((((s.response.adjointTaylorAngularFields p).mulCoordinateCombination
    (fun j => normalFrameRelativeCoframeValue d.γ a j p)).smul (normalFrameRelativeInverseRadiusFactor p)).smul
      (d.radius y)⁻¹).add ((s.response.adjointTaylorAngularFields p).smul
        (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a))).add (s.centerGradientAngularFields C p)

lemma firstErrorAngularFields_operator
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (p : NormalFrameRelativeParameter) :
    (s.firstErrorAngularFields C p).operator = s.firstAdjointErrorFamily C p := by
  change ((d.radius y)⁻¹ • (normalFrameRelativeInverseRadiusFactor p •
      ((s.response.adjointTaylorAngularFields p).mulCoordinateCombination
        (fun j => normalFrameRelativeCoframeValue d.γ a j p)).operator)+
    (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a) • (s.response.adjointTaylorAngularFields p).operator)+
      (s.centerGradientAngularFields C p).operator = _
  rw [CoarseAngularFields.mulCoordinateCombination_operator,s.centerGradientAngularFields_operator]
  rfl

lemma firstErrorAngularFields_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (s.firstErrorAngularFields C p).degreeData ∈ CoarseDegreeCompatibility.compatibleData := by
  let F := s.firstErrorAngularPacket C V h hK p hp
  have hFields : CoarseAngularFields.ofPacket F = s.firstErrorAngularFields C p := rfl
  rw [← hFields]
  exact F.data_mem

lemma firstErrorAngularFields_smoothAt
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V) :
    CoarseAngularFields.SmoothAt (s.firstErrorAngularFields C) p := by
  have hP := s.response.adjointTaylorAngularFields_smoothAt V hΩ h hK p hp.1
  have hPos := s.coefficients.positive (s.response.sub (V.sub hp.1))
  have hQ (j : I) : ContDiffAt ℝ ∞ (normalFrameRelativeCoframeValue d.γ a j) p :=
    (h.contDiffOn_relativeCoframeValue hΩ hK a j).contDiffAt
      ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hPos)
  have hQM := hP.mulCoordinateCombination hQ
  have hR : ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor p :=
    (contDiffAt_const.add contDiffAt_snd).inv (ne_of_gt hp.2)
  have hb := s.contDiffAt_firstErrorLogCoefficient hY hProfile p (V.sub hp.1) (a:=a)
  exact (((CoarseAngularFields.SmoothAt.scalar hR hQM).const_smul (d.radius y)⁻¹).add
    (CoarseAngularFields.SmoothAt.scalar hb hP)).add (s.centerGradientAngularFields_smoothAt C V hΩ h hK p hp)
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
