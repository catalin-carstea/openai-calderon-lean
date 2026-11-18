import Proof.NativeActualFirstErrorCovariant
import Proof.NativeFirstAdjointErrorRegularity
import Proof.CovariantHalfCoarseBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

/-- Differentiate the SAME native coarse/half inclusion graph. The actual
horizontal derivative therefore retains the genuine order-one half domain. -/
lemma NativeRelativeHorizontalTaylorData.first_covariant_half_derivative_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (v : NormalFrameRelativeParameter) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (fderiv ℝ (s.firstAdjointErrorFamily C) p v)=
    (fderiv ℝ (s.firstAdjointHalfErrorFamily C) p v).comp
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  extract_lets p
  have hp := s.centerDegreeDomain_pointMem V
  have hOp := (s.firstErrorAngularFields_smoothAt C V hY hΩ h hK hProfile p hp).operator
  have hOpEq : (fun q => (s.firstErrorAngularFields C q).operator)=s.firstAdjointErrorFamily C :=
    funext (fun q => s.firstErrorAngularFields_operator C q)
  rw [hOpEq] at hOp
  have hHalf := (s.contDiffOn_firstAdjointHalfErrorFamily C V hY hΩ h hK hProfile).contDiffAt
    ((s.centerDegreeDomain_open V).mem_nhds hp)
  have hGraph : ∀ᶠ q in 𝓝 p,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (s.firstAdjointErrorFamily C q)=
      (s.firstAdjointHalfErrorFamily C q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [(s.centerDegreeDomain_open V).mem_nhds hp] with q hq
    exact s.firstAdjointHalfErrorFamily_coarse_compatible C V hF0 q hq.1
  exact compatible_endpoint_fderiv _ _ _ _ p v (hOp.differentiableAt (by simp))
    (hHalf.differentiableAt (by simp)) hGraph

/-- A genuine half-domain extension of the native covariant jet gives
an extension of the literal weak derivative used in the physical Green
formula. The input inclusion is explicit; no extra regularity is inferred
from the carrier type. -/
lemma halfOperatorCovariantDerivativeL_eq_strong_extension
    {d : Data} {y b : X}
    (H : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hH : DifferentiableAt ℝ H y) (hLo : DifferentiableAt ℝ Lo y)
    (hLow : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (H x)=
      (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hHigh : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi y)=
      (H y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hGraph : CoarseCovariantRotationGraph d y b H S)
    (hS : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d Lo Hi y b=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [halfOperatorCovariantDerivativeL_eq_coarse H Lo Hi S hH hLo hLow hHigh hGraph]
  apply ContinuousLinearMap.ext
  intro u
  have hh := DFunLike.congr_fun hS (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh

/-- A true strong extension on the higher dense core determines the
coarse-to-half inclusion graph on the full H1 domain. -/
lemma coarse_half_endpoint_of_weak_strong
    (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (h : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
    (denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using DFunLike.congr_fun h u

end ShrinkingSpheres
