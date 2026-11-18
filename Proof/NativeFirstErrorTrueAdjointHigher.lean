import Proof.NativeFirstErrorDegreeFamily
import Proof.NativeFirstAdjointErrorRegularity
import Proof.HalfDegreeAdjointHigherLift
import Proof.SmoothFiniteAdjointJets
import Proof.NativeFirstCovariantHalfLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma halfDegreeAdjointHigherLift_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {R S : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {p : P} {N : ℕ} {BR BS : ℝ}
    (hR : SmoothFiniteJetBound R p N BR) (hS : SmoothFiniteJetBound S p N BS) :
    SmoothFiniteJetBound (fun x => halfDegreeAdjointHigherLift (R x) (S x)) p N (BR+BS) := by
  have hSA := hS.adjoint.const_smul (-1)
  simp only [abs_neg,abs_one,one_mul,neg_one_smul] at hSA
  exact halfDegreeHigherLift_jet_bound hR.adjoint hSA

namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

def firstErrorTrueAdjointHigherFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) :
    NormalFrameRelativeParameter → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  fun p => halfDegreeAdjointHigherLift (s.firstAdjointHalfErrorFamily C p) (s.firstErrorDegreeFamily C V h hK p)

lemma firstErrorTrueAdjointHigherFamily_balanced
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (s.firstErrorTrueAdjointHigherFamily C V h hK p)=
    (s.firstAdjointHalfErrorFamily C p).adjoint.comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply halfDegreeAdjointHigherLift_inclusion
  intro m n z
  have hDegree := s.firstErrorDegreeFamily_physical_block C V h hK p hp m n z
  have hLow := half_physical_blocks_of_coarse_compatible _ _
    (s.firstAdjointHalfErrorFamily_coarse_compatible C V hF0 p hp.1) m n z
  exact hDegree.trans (congrArg (fun w => ((m:ℝ)-(n:ℝ)) • w) hLow.symm)

lemma contDiffOn_firstErrorTrueAdjointHigherFamily
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj) :
    ContDiffOn ℝ ∞ (s.firstErrorTrueAdjointHigherFamily C V h hK) (s.centerDegreeDomain V) :=
  contDiffOn_halfDegreeAdjointHigherLift _ _
    (s.contDiffOn_firstAdjointHalfErrorFamily C V hY hΩ h hK hProfile)
    (s.contDiffOn_firstErrorDegreeFamily C V hY hΩ h hK hProfile)

/-- Differentiate the genuine native true-adjoint higher graph. This
alone makes no assertion of a uniform physical derivative bound. -/
lemma firstErrorTrueAdjointHigherFamily_derivative_compatible
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (V : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p v : NormalFrameRelativeParameter) (hp : p ∈ s.centerDegreeDomain V) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (fderiv ℝ (s.firstErrorTrueAdjointHigherFamily C V h hK) p v)=
    (fderiv ℝ (fun q => (s.firstAdjointHalfErrorFamily C q).adjoint) p v).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hHigh := (s.contDiffOn_firstErrorTrueAdjointHigherFamily C V hY hΩ h hK hProfile).contDiffAt
    ((s.centerDegreeDomain_open V).mem_nhds hp)
  have hLow := (Adj.contDiff.comp_contDiffOn
    (s.contDiffOn_firstAdjointHalfErrorFamily C V hY hΩ h hK hProfile)).contDiffAt
      ((s.centerDegreeDomain_open V).mem_nhds hp)
  have hGraph : ∀ᶠ q in 𝓝 p,
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (s.firstErrorTrueAdjointHigherFamily C V h hK q)=
      (s.firstAdjointHalfErrorFamily C q).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    filter_upwards [(s.centerDegreeDomain_open V).mem_nhds hp] with q hq
    exact s.firstErrorTrueAdjointHigherFamily_balanced C V h hK hF0 q hq
  exact compatible_endpoint_fderiv _ _ _ _ p v (hHigh.differentiableAt (by simp))
    (hLow.differentiableAt (by simp)) hGraph

end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
