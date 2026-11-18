import Proof.NativeRelativeActualRadialGerms
import Proof.FirstRadialAngularFieldJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 1800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Background.scaled_first_covector_actual_parameter {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    {x : X} (hx : x ∈ Ω) {r0 : ℝ} (hr : r0 ≠ 0) :
    r0 • normalFrameRelativeFirstCovector d.γ d.g₁ (normalFrameRelativeActualParameter d r0 x) =
      d.radius x • firstDensityLogCovector d x := by
  have he (i j : I) : metricPair d.γ x (frameVectorLinear d.frame x (axis i))
      (frameVectorLinear d.frame x (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 x hx i j
  change r0 • ((1+(d.radius x/r0-1)) • normalFrameFirstCovector d.γ d.g₁
    (normalizedOrthonormalFrameParameter d.γ (x,(0,frameVectorLinear d.frame x)))) = _
  rw [normalizedOrthonormalFrameParameter_eq_self _ _ he]
  change r0 • ((1+(d.radius x/r0-1)) •
    (firstDensityLogDifferential d.γ d.g₁ x).comp (frameVectorLinear d.frame x)) = _
  rw [← h.firstDensityLogCovector_eq_differential hK hΩ hx,smul_smul]
  congr 1
  field_simp
  ring

variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

lemma NormalFrameRelativeResponsePacket.actual_forward_taylor_germ
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (hy : y ∈ Y) (hZ : 2 ≤ Z) (hr : d.radius y ≠ 0) (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (R : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) :
    (fun x => R x-d.radius x • (firstRadialCorrectionL d x).comp (sphereSobolevInclusionL 1 0 (by norm_num))) =ᶠ[𝓝 y]
      (fun x => t.forwardTaylor (normalFrameRelativeActualParameter d (d.radius y) x)) := by
  filter_upwards [hY.mem_nhds hy,t.actual_radial_germ V hY hSub h hy hZ hr hrSm R hR] with x hx hRx
  rw [hRx,NormalFrameRelativeResponsePacket.forwardTaylor]
  congr 1
  have hFirst : coarseFirstRadialVariationL 1
      (normalFrameRelativeFirstCovector d.γ d.g₁ (normalFrameRelativeActualParameter d (d.radius y) x)) =
      radialCorrectionCovectorL
        (normalFrameRelativeFirstCovector d.γ d.g₁ (normalFrameRelativeActualParameter d (d.radius y) x)) := by
    simpa only [inv_one,one_smul] using coarseFirstRadialVariationL_normalized_covector 1
      (normalFrameRelativeFirstCovector d.γ d.g₁ (normalFrameRelativeActualParameter d (d.radius y) x))
  rw [hFirst,firstRadialCorrectionL_eq_covector]
  change d.radius x • firstRadialForwardOperatorMapL (firstDensityLogCovector d x) =
    d.radius y • firstRadialForwardOperatorMapL
      (normalFrameRelativeFirstCovector d.γ d.g₁ (normalFrameRelativeActualParameter d (d.radius y) x))
  rw [← map_smul,← map_smul,h.scaled_first_covector_actual_parameter hΩ hK (hSub hx) hr]

lemma NormalFrameRelativeResponsePacket.actual_adjoint_taylor_germ
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K)
    (hy : y ∈ Y) (hZ : 2 ≤ Z) (hr : d.radius y ≠ 0) (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) :
    (fun x => A x-sphereSobolevDegreeL-d.radius x •
      (firstRadialCorrectionL d x).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) =ᶠ[𝓝 y]
      (fun x => t.adjointTaylor (normalFrameRelativeActualParameter d (d.radius y) x)) := by
  filter_upwards [hY.mem_nhds hy,t.actual_adjoint_germ V hY hSub h hy hZ hr hrSm R A hR hA] with x hx hAx
  change A x-sphereSobolevDegreeL-d.radius x •
    (firstRadialCorrectionL d x).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) =
    t.fullAdjoint (normalFrameRelativeActualParameter d (d.radius y) x)-sphereSobolevDegreeL-
      d.radius y • firstRadialAdjointOperatorMapL
        (normalFrameRelativeFirstCovector d.γ d.g₁ (normalFrameRelativeActualParameter d (d.radius y) x))
  apply congrArg₂ (fun F S : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => F-sphereSobolevDegreeL-S) hAx
  rw [firstRadialCorrectionL_eq_covector]
  change d.radius x • firstRadialAdjointOperatorMapL (firstDensityLogCovector d x) =
    d.radius y • firstRadialAdjointOperatorMapL
      (normalFrameRelativeFirstCovector d.γ d.g₁ (normalFrameRelativeActualParameter d (d.radius y) x))
  rw [← map_smul,← map_smul,h.scaled_first_covector_actual_parameter hΩ hK (hSub hx) hr]
end ShrinkingSpheres
