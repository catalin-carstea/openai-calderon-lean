import Proof.ActualCenterGradientRealization
import Proof.RelativeActualInverseRadius
import Proof.NativeRelativeActualRadialGerms
import Proof.RelativeCenterGradientAdjointFamily
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
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

lemma actual_center_gradient_local_germ {Y : Set X} {d : Data} {y a : X} {CC CH : ℝ}
    (hY : IsOpen Y) (hy : y ∈ Y) (hr : d.radius y ≠ 0)
    (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (heSm : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) :
    G =ᶠ[𝓝 y] (fun x => (d.radius x)⁻¹ • closedBoundaryGradientAdjoint
      (fun j => (C j).closed (normalFrameRelativeActualParameter d (d.radius y) x)) (A x)) := by
  have hParam := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hrSm heSm).contDiffAt (hY.mem_nhds hy)
  have hEach (j : I) : ∀ᶠ x in 𝓝 y,normalFrameRelativeActualParameter d (d.radius y) x ∈ (C j).domain := by
    have h0 : normalFrameRelativeActualParameter d (d.radius y) y ∈ (C j).domain := by
      rw [normalFrameRelativeActualParameter_point d y hr]
      exact (C j).point
    exact hParam.continuousAt.eventually ((C j).isOpen.mem_nhds h0)
  have hAll : ∀ᶠ x in 𝓝 y,∀ j : I,normalFrameRelativeActualParameter d (d.radius y) x ∈ (C j).domain :=
    Filter.eventually_all.mpr hEach
  filter_upwards [hY.mem_nhds hy,hAll] with x hx hp
  let p := normalFrameRelativeActualParameter d (d.radius y) x
  have hValue (j : I) (w : UnitSphere) := (C j).atParameterCoefficient_actual hr x (hp j) w
  have hh := hG x hx (fun j => (C j).atParameterCoefficient p) hValue
  rw [hh]
  apply congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => (d.radius x)⁻¹ • T)
  exact (closedBoundaryGradientAdjoint_on_smooth
    (fun j => commonSupportCoefficientFamily 3 (C j).scalar (C j).smooth (C j).support (C j).compact (C j).supported p)
    (A x)).symm

lemma NativeRelativeHorizontalTaylorData.actual_center_gradient_germ
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (V : s.response.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hy : y ∈ Y)
    (hr : d.radius y ≠ 0) (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) :
    G =ᶠ[𝓝 y] (fun x => s.centerGradientAdjointFamily C (normalFrameRelativeActualParameter d (d.radius y) x)) := by
  have hLocal := actual_center_gradient_local_germ hY hy hr hrSm
    (fun i => (h.2.2.2.2.2.2.1 i).mono hSub) C A G hG
  have hAdj := s.response.actual_adjoint_germ V hY hSub h hy (by norm_num) hr hrSm R A hR hA
  filter_upwards [hLocal,hAdj] with x hx hAx
  rw [hx,hAx]
  have hFactor := relativeInverseRadiusFactor_actual d hr x
  change (d.radius x)⁻¹ • _ = (d.radius y)⁻¹ • ((1+(d.radius x/d.radius y-1))⁻¹ • _)
  rw [smul_smul]
  exact congrArg (fun c : ℝ => c • _) hFactor.symm
end ShrinkingSpheres
