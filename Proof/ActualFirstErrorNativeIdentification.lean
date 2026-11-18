import Proof.ActualFirstAdjointErrorGerm
import Proof.CompatibleEndpointUniqueness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Shared coarse identification, before any physical endpoint is selected. -/
lemma NativeRelativeHorizontalTaylorData.actual_first_error_coarse_native_eq
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Y)
    (hr : d.radius y ≠ 0) (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x))
 :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    actualFirstAdjointErrorFamily d a A G y=s.firstAdjointErrorFamily C p := by
  have hh := (s.actual_first_adjoint_error_germ V hY hΩ hSub h hK hy hr hrSm C R A G hR hA hG).eq_of_nhds
  simpa only [normalFrameRelativeActualParameter_point d y hr] using hh

/-- One native packet identifies the actual physical coarse first error
and ANY already selected compatible low endpoint. Shared by ordinary and
adjoint commutator transport, retaining all physical and native witnesses. -/
lemma NativeRelativeHorizontalTaylorData.actual_first_error_native_identification
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Y)
    (hr : d.radius y ≠ 0) (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x))
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d a A G y)=L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    actualFirstAdjointErrorFamily d a A G y=s.firstAdjointErrorFamily C p ∧
      L=s.firstAdjointHalfErrorFamily C p := by
  have hE := s.actual_first_error_coarse_native_eq V hY hΩ hSub h hK hy hr hrSm C R A G hR hA hG
  refine ⟨hE,?_⟩
  exact half_endpoint_unique_of_coarse _ _ _ (by simpa only [hE] using hL)
    (s.firstAdjointHalfErrorFamily_coarse_compatible C V hF0 _ V.pointMem)
end ShrinkingSpheres
