import Proof.NativeRelativePhysicalRadialIdentification
import Proof.NativeRelativeActualRadialGerms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}

lemma actual_radial_point
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hR : RealizesActualMidpointRadialError d y R) :
    R = s.response.response ((y,frameVectorLinear d.frame y),0) := by
  obtain ⟨hRep,hRep1⟩ := s.coefficients.actual_point_germs hΩ h hK hy le_rfl
  have hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2
      (commonSupportMatrixFamily 2 s.coefficients.a s.coefficients.smooth s.coefficients.support
        s.coefficients.compact s.coefficients.supported ((y,frameVectorLinear d.frame y),0)) z =
      normalizedFirstNormalCoefficient d y z := by
    intro z hz
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  exact actual_midpoint_eq_of_normalized_restriction d y R _ _ hR hField s.point.strong
    (s.response.highRestriction _ s.response.pointMem)

lemma actual_adjoint_point
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    (R A : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (hR : RealizesActualMidpointRadialError d y R)
    (hA : ∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A v⟫_ℝ)
    (hPair : ∀ u v,⟪s.radialL u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,s.radialAdjointL v⟫_ℝ) :
    A=s.radialAdjointL := by
  have hEq : R+sphereSobolevDegreeL = s.radialL := congrArg
    (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T+sphereSobolevDegreeL)
      (s.actual_radial_point hΩ h hK hy R hR)
  apply radial_physical_adjoint_unique (R+sphereSobolevDegreeL) A s.radialAdjointL hA
  rw [hEq]
  exact hPair
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres
