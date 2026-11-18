import Proof.EndpointCompatibleDerivative
import Proof.NativeFirstAdjointErrorRegularity
import Proof.NativeFirstErrorAngularFields
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

/-- Native parameter derivatives of the SAME first-adjoint error retain both
    genuine endpoint squares. The horizontal derivative is a specialization. -/
lemma first_adjoint_error_derivative_endpoints
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p b : NormalFrameRelativeParameter)
    (hpT : p ∈ s.centerDegreeDomain Vt) (hpC : p ∈ s.centerDegreeDomain Vc) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (fderiv ℝ (s.firstAdjointErrorFamily C) p b)=
      (fderiv ℝ (s.firstAdjointHalfErrorFamily C) p b).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc h hK) p b)=
      (fderiv ℝ (s.firstAdjointErrorFamily C) p b).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  have hFS := (s.firstErrorAngularFields_smoothAt C Vt hY hΩ h hK hProfile p hpT).operator
  have hOp : (fun q => (s.firstErrorAngularFields C q).operator)=s.firstAdjointErrorFamily C := by
    funext q
    exact s.firstErrorAngularFields_operator C q
  rw [hOp] at hFS
  have hF := hFS.differentiableAt (by simp)
  have hL := ((s.contDiffOn_firstAdjointHalfErrorFamily C Vt hY hΩ h hK hProfile).contDiffAt
    ((s.centerDegreeDomain_open Vt).mem_nhds hpT)).differentiableAt (by simp)
  have hH := (s.contDiffAt_firstAdjointHigherErrorFamily C Vt Vc hY hΩ h hK hProfile
    p hpT.1 hpC).differentiableAt (by simp)
  have hLow : ∀ᶠ q in 𝓝 p,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (s.firstAdjointErrorFamily C q)=
        (s.firstAdjointHalfErrorFamily C q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [(s.centerDegreeDomain_open Vt).mem_nhds hpT] with q hq
    exact s.firstAdjointHalfErrorFamily_coarse_compatible C Vt hF0 q hq.1
  have hHigh : ∀ᶠ q in 𝓝 p,
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
          (s.firstAdjointHigherErrorFamily C Vt Vc h hK q)=
        (s.firstAdjointErrorFamily C q).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    filter_upwards [(s.centerDegreeDomain_open Vt).mem_nhds hpT,
      (s.centerDegreeDomain_open Vc).mem_nhds hpC] with q hqt hqc
    exact s.firstAdjointHigherErrorFamily_coarse_compatible C Vt Vc h hK hF0 q hqt.1 hqc
  exact ⟨compatible_endpoint_fderiv _ _ _ _ p b hF hL hLow,
    compatible_endpoint_fderiv _ _ _ _ p b hH hF hHigh⟩
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
