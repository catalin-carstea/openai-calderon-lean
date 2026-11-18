import Proof.NativeFirstAngularErrorEndpoints
import Proof.NativeFirstErrorAngularGraph
import Proof.CoarseRotationGraphUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

/-- Shared native graph identification, valid at every normalized parameter
    in the common endpoint domains, retaining the chosen coarse commutator. -/
lemma angular_error_endpoints_of_graph
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hpT : p ∈ s.centerDegreeDomain Vt)
    (hpC : p ∈ s.centerDegreeDomain Vc) (hpCs : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (i j : I) (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hS : ∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (s.firstAdjointErrorFamily C p (sphereSobolevInclusionL 2 1 (by norm_num) u))=
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (S (sphereSobolevInclusionL 2 1 (by norm_num) u)+s.firstAdjointErrorFamily C p (sphereSobolevRotationL 2 i j u))) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      (fderiv ℝ (s.firstAdjointHalfErrorFamily C) p (normalFrameRelativeAngularTangent d.γ p i j)).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc h hK) p (normalFrameRelativeAngularTangent d.γ p i j))=
        S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  have hNative := s.firstErrorAngularFields_rotation_graph C Vt h hK p hpT.1 i j
  have hEq := coarse_rotation_generator_unique (s.firstAdjointErrorFamily C p) S
    ((s.firstErrorAngularFields C p).angular (i,j)) i j hS hNative
  have hCompat := s.first_adjoint_error_angular_endpoints C Vt Vc hY hΩ h hK hProfile hF0
    p hpT hpC hpCs he i j
  constructor
  · exact (congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T) hEq).trans hCompat.1
  · exact hCompat.2.trans (congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
      T.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hEq.symm)
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
