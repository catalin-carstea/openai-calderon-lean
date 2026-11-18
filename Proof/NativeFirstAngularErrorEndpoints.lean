import Proof.NativeCovariantErrorEndpoints
import Proof.NativeFirstErrorAngularNaturality
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

/-- The actual native rotation commutator of the SAME first-adjoint error
    retains both genuine endpoint squares. -/
lemma first_adjoint_error_angular_endpoints
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter)
    (hpT : p ∈ s.centerDegreeDomain Vt) (hpC : p ∈ s.centerDegreeDomain Vc)
    (hpCs : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (i j : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        ((s.firstErrorAngularFields C p).angular (i,j))=
      (fderiv ℝ (s.firstAdjointHalfErrorFamily C) p
        (normalFrameRelativeAngularTangent d.γ p i j)).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc h hK) p
          (normalFrameRelativeAngularTangent d.γ p i j))=
      ((s.firstErrorAngularFields C p).angular (i,j)).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  have hAngular := s.firstErrorAngularFields_angular_eq C Vt hY hΩ h hK hProfile p hpT hpCs he i j
  have hFix := normalFrameRelativeNormalization_eq_self d.γ p he
  rw [normalFrameRelativeAngularDerivative,hFix] at hAngular
  rw [hAngular]
  exact s.first_adjoint_error_derivative_endpoints C Vt Vc hY hΩ h hK hProfile hF0
    p (normalFrameRelativeAngularTangent d.γ p i j) hpT hpC
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
