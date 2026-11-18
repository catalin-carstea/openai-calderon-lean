import Proof.NormalFrameRelativeNativeCoefficientJets
import Proof.CommonSupportCoefficientPointGerms
import Proof.NormalFrameRadialTaylorModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

theorem Background.normalFrameRelativeCoefficient_actual_zero {Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) {y : X} (hy : y ∈ Ω) (z : X) :
    normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y)
      (((y,frameVectorLinear d.frame y),0),z) = normalizedFirstNormalCoefficient d y z := by
  have he (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 y hy i j
  rw [normalFrameRelativeCoefficient_orthonormal _ _ _ _ _ he]
  simpa only [normalFrameRelativeInput,add_zero,one_mul,normalizedFirstNormalCoefficient] using
    normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame y z (d.radius y)

theorem Background.normalFrameRelativeFirstCovector_actual_zero {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω) :
    normalFrameRelativeFirstCovector d.γ d.g₁ ((y,frameVectorLinear d.frame y),0) =
      firstDensityLogCovector d y := by
  have he (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 y hy i j
  rw [normalFrameRelativeFirstCovector,add_zero,one_smul,
    normalizedOrthonormalFrameParameter_eq_self d.γ (y,(0,frameVectorLinear d.frame y)) he]
  exact (h.firstDensityLogCovector_eq_differential hK hΩ hy).symm

theorem NormalFrameRelativeCoefficientJetFamily.actual_point_germs {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data} {y : X}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) (hy : y ∈ Ω)
    {N : ℕ} {Z C : ℝ} (hZ : 2 ≤ Z)
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C) :
    let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p0
    let F1 := commonSupportMatrixFamily 2 q.a1 q.firstSmooth q.support q.compact q.firstSupported p0
    (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 z]
      (fun w => normalizedFirstNormalCoefficient d y w i j)) ∧
    (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 z]
      (fun w => firstDensityLogCovector d y w*(1:Mat) i j)) := by
  intro p0 F F1
  have hRep (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :=
    q.coefficientGerm p0 q.pointMem z (Metric.closedBall_subset_closedBall hZ hz)
  have hRep1 (z : X) (hz : z ∈ Metric.closedBall (0:X) 2) :=
    q.firstGerm p0 q.pointMem z (Metric.closedBall_subset_closedBall hZ hz)
  refine ⟨?_,?_⟩
  · exact commonSupport_coefficient_point_germs q.a
      (normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y)) q.smooth q.support q.compact q.supported p0
      (normalizedFirstNormalCoefficient d y) hRep (h.normalFrameRelativeCoefficient_actual_zero hy)
  · have hh := commonSupport_coefficient_point_germs q.a1
      (normalFrameRelativeFirstModel d.γ d.g₁) q.firstSmooth q.support q.compact q.firstSupported p0
      (fun w => firstDensityLogCovector d y w • (1:Mat)) hRep1 (fun w => by
        rw [normalFrameRelativeFirstModel_scalar,h.normalFrameRelativeFirstCovector_actual_zero hΩ hK hy])
    simpa only [Matrix.smul_apply,smul_eq_mul] using hh

end ShrinkingSpheres
