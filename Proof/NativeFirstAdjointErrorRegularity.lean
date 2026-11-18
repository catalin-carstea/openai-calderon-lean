import Proof.NativeFirstAdjointHigherError
import Proof.RelativeCoframeSmoothDomain
import Proof.RelativeCoframeSobolevRegularity
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

lemma Elliptic.contDiffOn_relativeCoframeNormalSobolevL (hΩ : IsOpen Ω) {K : ℝ}
    (h : Elliptic Ω K d.γ) (hK : 0 < K) (s : ℝ) (a : X) :
    ContDiffOn ℝ ∞ (relativeCoframeNormalSobolevL s d.γ a) (normalFrameRelativePositiveDomain Ω) := by
  exact h.contDiffOn_relativeCoframeSobolevMultiplier hΩ hK s a

namespace NativeRelativeHorizontalTaylorData

lemma contDiffAt_firstErrorLogCoefficient
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hY : IsOpen Y) {floor c₀ : ℝ} {Cj : Fin 9 → ℝ}
    (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.response.domain) :
    ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter =>
      fderiv ℝ (fun x => Real.log (d.radius x)) q.1.1 a) p := by
  have hCenter := s.coefficients.centers p (s.response.sub hp)
  have hLog : ContDiffOn ℝ ∞ (fderiv ℝ (fun x => Real.log (d.radius x))) Y :=
    (hProfile.1.log (fun x hx => (hProfile.2 x hx).1.ne')).fderiv_of_isOpen (m:=∞) hY (by simp)
  exact (((hLog.contDiffAt (hY.mem_nhds hCenter)).clm_apply contDiffAt_const).comp p contDiffAt_fst.fst)

lemma contDiffOn_firstAdjointHalfErrorFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj) :
    ContDiffOn ℝ ∞ (s.firstAdjointHalfErrorFamily C) (s.centerDegreeDomain V) := by
  intro p hp
  have hA := V.contDiffOn_adjointHalfTaylor.contDiffAt (V.domainOpen.mem_nhds hp.1)
  have hPos := s.coefficients.positive (s.response.sub (V.sub hp.1))
  have hM := (h.contDiffOn_relativeCoframeNormalSobolevL hΩ hK (1/2:ℝ) a).contDiffAt
    ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hPos)
  have hR : ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor p :=
    (contDiffAt_const.add contDiffAt_snd).inv (ne_of_gt hp.2)
  have hb := s.contDiffAt_firstErrorLogCoefficient hY hProfile p (V.sub hp.1) (a:=a)
  have hG := (s.contDiffOn_centerGradientHalfFamily C V).contDiffAt ((s.centerDegreeDomain_open V).mem_nhds hp)
  exact (((hR.smul (hA.clm_comp hM)).const_smul (d.radius y)⁻¹).add (hb.smul hA)).add hG |>.contDiffWithinAt

lemma contDiffAt_firstAdjointHigherErrorFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (p : NormalFrameRelativeParameter) (hpt : p ∈ Vt.domain) (hpc : p ∈ s.centerDegreeDomain Vc) :
    ContDiffAt ℝ ∞ (s.firstAdjointHigherErrorFamily C Vt Vc h hK) p := by
  have hA := (Vt.contDiffOn_adjointHigherTaylor hΩ h hK (by norm_num)).contDiffAt (Vt.domainOpen.mem_nhds hpt)
  have hPos := s.coefficients.positive (s.response.sub (Vt.sub hpt))
  have hM := (h.contDiffOn_relativeCoframeNormalSobolevL hΩ hK (3/2:ℝ) a).contDiffAt
    ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hPos)
  have hR : ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor p :=
    (contDiffAt_const.add contDiffAt_snd).inv (ne_of_gt hpc.2)
  have hb := s.contDiffAt_firstErrorLogCoefficient hY hProfile p (Vt.sub hpt) (a:=a)
  have hG := (s.contDiffOn_centerGradientHigherFamily C Vc hΩ h hK).contDiffAt
    ((s.centerDegreeDomain_open Vc).mem_nhds hpc)
  exact (((hR.smul (hA.clm_comp hM)).const_smul (d.radius y)⁻¹).add (hb.smul hA)).add hG
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
