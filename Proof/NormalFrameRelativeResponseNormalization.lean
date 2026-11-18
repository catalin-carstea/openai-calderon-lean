import Proof.NormalFrameRelativeNormalization
import Proof.NormalFrameRelativeResponsePacket
import Proof.RadialAdjointCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Elliptic.normalFrameRelativeFirstCovector_normalization {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) (g₁ : MetricField)
    (p : NormalFrameRelativeParameter) (hp : p ∈ normalFrameRelativePositiveDomain Ω) :
    normalFrameRelativeFirstCovector g g₁ (normalFrameRelativeNormalization g p) =
      normalFrameRelativeFirstCovector g g₁ p := by
  have hN := h.normalFrameRelativeNormalization_idempotent hK p hp
  have hEq := congrArg (fun q : NormalFrameRelativeParameter =>
    normalFrameFirstCovector g g₁ (normalFrameRelativeZeroL q)) hN
  change (1+p.2) • normalFrameFirstCovector g g₁
      (normalFrameRelativeZeroL (normalFrameRelativeNormalization g (normalFrameRelativeNormalization g p))) =
    (1+p.2) • normalFrameFirstCovector g g₁ (normalFrameRelativeZeroL (normalFrameRelativeNormalization g p))
  rw [hEq]

namespace NormalFrameRelativeCoefficientJetFamily
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C)

theorem matrix_normalization {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ q.domain)
    (hpN : normalFrameRelativeNormalization d.γ p ∈ q.domain)
    (z : X) (hz : z ∈ Metric.closedBall (0:X) Z) :
    coefficientMatrixField 2 (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
      (normalFrameRelativeNormalization d.γ p)) z =
    coefficientMatrixField 2 (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p) z := by
  rw [coefficientMatrixField_commonSupportMatrixFamily,coefficientMatrixField_commonSupportMatrixFamily]
  exact ((q.coefficientGerm _ hpN z hz).eq_of_nhds).trans
    ((h.normalFrameRelativeCoefficient_normalization hK d.g₁ d.expMap (d.radius y) p (q.positive hp) z).trans
      (q.coefficientGerm p hp z hz).eq_of_nhds.symm)

end NormalFrameRelativeCoefficientJetFamily

namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}

/-- The SAME actual response is unchanged by parameter normalization.
    This follows from native coefficient equality and dense uniqueness. -/
theorem response_normalization (t : NormalFrameRelativeResponsePacket q)
    (hZ : 2 ≤ Z) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ t.domain)
    (hpN : normalFrameRelativeNormalization d.γ p ∈ t.domain) :
    t.response (normalFrameRelativeNormalization d.γ p) = t.response p := by
  exact midpoint_radial_eq_of_coefficient_restrictions _ _ _ _
    (fun z hz => q.matrix_normalization h hK p (t.sub hp) (t.sub hpN) z
      (Metric.closedBall_subset_closedBall hZ (unitBall_subset_closedBall_two hz)))
    (t.highRestriction _ hpN) (t.highRestriction p hp)

theorem forwardTaylor_normalization (t : NormalFrameRelativeResponsePacket q)
    (hZ : 2 ≤ Z) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ t.domain)
    (hpN : normalFrameRelativeNormalization d.γ p ∈ t.domain) :
    t.forwardTaylor (normalFrameRelativeNormalization d.γ p) = t.forwardTaylor p := by
  unfold forwardTaylor
  rw [t.response_normalization hZ h hK p hp hpN,
    h.normalFrameRelativeFirstCovector_normalization hK d.g₁ p (q.positive (t.sub hp))]

theorem adjointTaylor_normalization (t : NormalFrameRelativeResponsePacket q)
    (hZ : 2 ≤ Z) {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p ∈ t.domain)
    (hpN : normalFrameRelativeNormalization d.γ p ∈ t.domain) :
    t.adjointTaylor (normalFrameRelativeNormalization d.γ p) = t.adjointTaylor p := by
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  have hDa := radialAdjointFromResponseL_congr_sphere (F (normalFrameRelativeNormalization d.γ p)) (F p)
    (t.response p+sphereSobolevDegreeL)
    (fun w => q.matrix_normalization h hK p (t.sub hp) (t.sub hpN) w.val
      (Metric.closedBall_subset_closedBall hZ (Metric.closedBall_subset_closedBall (by norm_num)
        (Metric.sphere_subset_closedBall w.property))))
  unfold adjointTaylor
  rw [t.response_normalization hZ h hK p hp hpN,hDa,
    h.normalFrameRelativeFirstCovector_normalization hK d.g₁ p (q.positive (t.sub hp))]

end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
