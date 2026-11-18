import Proof.NativeCenterGradientAngularNaturality
import Proof.RelativeCoframeAngularIdentity
import Proof.CoframeCoordinateCombinationAngular
import Proof.NativeFirstErrorAngularFields
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
namespace NativeRelativeHorizontalTaylorData
lemma hasDerivAt_firstError_angular_curve
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hpV : p ∈ V.domain) (hpC : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0)
    (i j : I) :
    HasDerivAt (fun θ => s.firstAdjointErrorFamily C (normalFrameRelativeAngularCurve d.γ p i j θ))
      ((s.firstErrorAngularFields C p).angular (i,j)) 0 := by
  let c := normalFrameRelativeAngularCurve d.γ p i j
  let P := s.response.adjointTaylorAngularFields p
  have hFix : normalFrameRelativeNormalization d.γ p=p := normalFrameRelativeNormalization_eq_self _ _ he
  have hZero : c 0=p := (normalFrameRelativeAngularCurve_zero d.γ p i j).trans hFix
  have hpN := V.normalizationStable p hpV
  have hPaDiff : DifferentiableAt ℝ s.response.adjointTaylor (normalFrameRelativeNormalization d.γ p) :=
    (s.response.contDiffOn_adjointTaylor.contDiffAt (s.response.domainOpen.mem_nhds (V.sub hpN))).differentiableAt (by simp)
  have hPa := hasDerivAt_relativeAngularFamily d.γ s.response.adjointTaylor p i j hPaDiff
  have hpPos := s.coefficients.positive (s.response.sub (V.sub hpV))
  have hMDiff : DifferentiableAt ℝ (relativeCoframeNormalSobolevL 1 d.γ a)
      (normalFrameRelativeNormalization d.γ p) :=
    ((h.contDiffOn_relativeCoframeSobolevMultiplier hΩ hK 1 a).contDiffAt
      ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds
        (h.normalFrameRelativeNormalization_mem hK p hpPos))).differentiableAt (by simp)
  have hM := (hasDerivAt_relativeAngularFamily d.γ (relativeCoframeNormalSobolevL 1 d.γ a) p i j hMDiff).congr_deriv
    (h.relativeCoframeNormal_angularDerivative hΩ hK 1 a p hpPos i j)
  have hProd := hPa.clm_comp hM
  have hVal :
      (normalFrameRelativeAngularDerivative d.γ s.response.adjointTaylor i j p).comp
          (relativeCoframeNormalSobolevL 1 d.γ a (c 0))+
        (s.response.adjointTaylor (c 0)).comp (relativeCoframeAngularSobolevL 1 d.γ a i j p) =
      (P.mulCoordinateCombination (fun k => normalFrameRelativeCoframeValue d.γ a k p)).angular (i,j) := by
    simp only [hZero]
    exact (P.mulCoframe_angular d.γ a p i j).symm
  have hProd' := hProd.congr_deriv hVal
  have hG := s.hasDerivAt_centerGradient_angular_curve C V h hK p hpV hpC he i j
  exact (((hProd'.const_smul (normalFrameRelativeInverseRadiusFactor p)).const_smul (d.radius y)⁻¹).add
    (hPa.const_smul (fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 a))).add hG

lemma firstErrorAngularFields_angular_eq
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V) (hpC : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l)) = if k=l then 1 else 0)
    (i j : I) :
    (s.firstErrorAngularFields C p).angular (i,j) =
      normalFrameRelativeAngularDerivative d.γ (s.firstAdjointErrorFamily C) i j p := by
  have hFix : normalFrameRelativeNormalization d.γ p=p := normalFrameRelativeNormalization_eq_self _ _ he
  have hSmooth := (s.firstErrorAngularFields_smoothAt C V hY hΩ h hK hProfile p hp).operator
  have hOp : (fun q => (s.firstErrorAngularFields C q).operator)=s.firstAdjointErrorFamily C := by
    funext q
    exact s.firstErrorAngularFields_operator C q
  rw [hOp] at hSmooth
  have hDiff : DifferentiableAt ℝ (s.firstAdjointErrorFamily C) (normalFrameRelativeNormalization d.γ p) := by
    rw [hFix]
    exact hSmooth.differentiableAt (by simp)
  exact (s.hasDerivAt_firstError_angular_curve C V hΩ h hK p hp.1 hpC he i j).unique
    (hasDerivAt_relativeAngularFamily d.γ (s.firstAdjointErrorFamily C) p i j hDiff)
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
