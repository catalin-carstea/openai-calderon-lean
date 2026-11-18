import Proof.NormalFrameRelativeActualParameter
import Proof.NativeRelativeTrueAdjointDomain
import Proof.NativeRelativeFullAdjointJets
import Proof.NormalizedRadialRepresentativeUniqueness
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
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

lemma NormalFrameRelativeCoefficientJetFamily.actual_parameter_field
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C)
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hZ : 2 ≤ Z) (hr : d.radius y ≠ 0)
    (x : X) (hx : x ∈ Ω) (hp : normalFrameRelativeActualParameter d (d.radius y) x ∈ q.domain) :
    ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2
      (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
        (normalFrameRelativeActualParameter d (d.radius y) x)) z = normalizedFirstNormalCoefficient d x z := by
  intro z hz
  rw [coefficientMatrixField_commonSupportMatrixFamily]
  exact ((q.coefficientGerm _ hp z
    (Metric.closedBall_subset_closedBall hZ (unitBall_subset_closedBall_two hz))).eq_of_nhds).trans
      (h.normalFrameRelativeCoefficient_actual_parameter hx hr z)

lemma NormalFrameRelativeResponsePacket.actual_radial_germ
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hy : y ∈ Y) (hZ : 2 ≤ Z)
    (hr : d.radius y ≠ 0) (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (R : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) :
    R =ᶠ[𝓝 y] (fun x => t.response (normalFrameRelativeActualParameter d (d.radius y) x)) := by
  have hParam := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hrSm
    (fun i => (h.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
  have hp0 : normalFrameRelativeActualParameter d (d.radius y) y ∈ V.domain := by
    rw [normalFrameRelativeActualParameter_point d y hr]
    exact V.pointMem
  have hpV : ∀ᶠ x in 𝓝 y,normalFrameRelativeActualParameter d (d.radius y) x ∈ V.domain :=
    hParam.continuousAt.eventually (V.domainOpen.mem_nhds hp0)
  filter_upwards [hY.mem_nhds hy,hpV] with x hx hp
  exact actual_midpoint_eq_of_normalized_restriction d x (R x) _ _ (hR x hx)
    (q.actual_parameter_field h hZ hr x (hSub hx) (t.sub (V.sub hp)))
    (V.strong _ hp) (t.highRestriction _ (V.sub hp))

lemma NormalFrameRelativeResponsePacket.actual_adjoint_germ
    (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hy : y ∈ Y) (hZ : 2 ≤ Z)
    (hr : d.radius y ≠ 0) (hrSm : ContDiffOn ℝ ∞ d.radius Y)
    (R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) :
    A =ᶠ[𝓝 y] (fun x => t.fullAdjoint (normalFrameRelativeActualParameter d (d.radius y) x)) := by
  have hRG := t.actual_radial_germ V hY hSub h hy hZ hr hrSm R hR
  have hParam := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hrSm
    (fun i => (h.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
  have hp0 : normalFrameRelativeActualParameter d (d.radius y) y ∈ V.domain := by
    rw [normalFrameRelativeActualParameter_point d y hr]
    exact V.pointMem
  have hpV : ∀ᶠ x in 𝓝 y,normalFrameRelativeActualParameter d (d.radius y) x ∈ V.domain :=
    hParam.continuousAt.eventually (V.domainOpen.mem_nhds hp0)
  filter_upwards [hY.mem_nhds hy,hRG,hpV] with x hx hRx hp
  apply radial_physical_adjoint_unique (R x+sphereSobolevDegreeL) (A x) _ (hA x hx)
  rw [hRx]
  exact V.fullPair _ hp
end ShrinkingSpheres
