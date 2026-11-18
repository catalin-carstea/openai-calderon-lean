import Proof.ActualFirstAdjointErrorFamily
import Proof.RelativeActualInverseRadius
import Proof.NativeFirstAdjointError
import Proof.ActualCenterGradientGerms
import Proof.NativeRelativeActualTaylorGerms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma NativeRelativeHorizontalTaylorData.actual_first_adjoint_error_germ
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
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) :
    actualFirstAdjointErrorFamily d a A G =ᶠ[𝓝 y]
      (fun x => s.firstAdjointErrorFamily C (normalFrameRelativeActualParameter d (d.radius y) x)) := by
  have hTaylor := s.response.actual_adjoint_taylor_germ V hY hΩ hSub h hK hy (by norm_num) hr hrSm R A hR hA
  have hCenter := s.actual_center_gradient_germ V hY hSub h hy hr hrSm C R A G hR hA hG
  filter_upwards [hY.mem_nhds hy,hTaylor,hCenter] with x hx hTx hGx
  have hPa : radialAdjointTaylorRemainderL (A x) (firstRadialCorrectionL d x) (d.radius x) =
      s.response.adjointTaylor (normalFrameRelativeActualParameter d (d.radius y) x) := hTx
  have hM := h.relativeCoframeNormalSobolev_actual_parameter (hSub hx) 1 (d.radius y) a
  have hFactor := relativeInverseRadiusFactor_actual d hr x
  unfold actualFirstAdjointErrorFamily firstAdjointErrorFamily relativeFirstAdjointErrorOperator
  rw [hPa,hGx,← hM,smul_smul,hFactor]
  rfl
end ShrinkingSpheres
