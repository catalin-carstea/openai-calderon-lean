import Proof.RelativeCoframeSobolevMultiplier
import Proof.NormalFrameRelativeActualParameter
import Proof.MetricSmooth
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def actualCoframeNormalSobolevL (s : ℝ) (d : Data) (a x : X) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  ∑ j : I,metricPair d.γ x a (d.frame x j) • coordinateMultiplierSobolevL s j

lemma Background.relativeCoframeNormalSobolev_actual_parameter {Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) {x : X} (hx : x ∈ Ω)
    (s r0 : ℝ) (a : X) :
    relativeCoframeNormalSobolevL s d.γ a (normalFrameRelativeActualParameter d r0 x) =
      actualCoframeNormalSobolevL s d a x := by
  have he (i j : I) : metricPair d.γ x (frameVectorLinear d.frame x (axis i))
      (frameVectorLinear d.frame x (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 x hx i j
  unfold relativeCoframeNormalSobolevL actualCoframeNormalSobolevL
  apply Finset.sum_congr rfl
  intro j hj
  have hh := normalFrameRelativeCoframeValue_orthonormal d.γ a j x (frameVectorLinear d.frame x) he
  have hValue : normalFrameRelativeCoframeValue d.γ a j (normalFrameRelativeActualParameter d r0 x) =
      metricPair d.γ x a (d.frame x j) := by
    change normalFrameRelativeCoframeValue d.γ a j ((x,frameVectorLinear d.frame x),0) = _
    simpa only [frameVectorLinear_apply,frameVector_axis] using hh
  rw [hValue]

lemma Background.contDiffOn_actualCoframeNormalSobolevL {Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (s : ℝ) (a : X) :
    ContDiffOn ℝ ∞ (actualCoframeNormalSobolevL s d a) Ω := by
  apply ContDiffOn.sum
  intro j hj
  have hPair : ContDiffOn ℝ ∞ (fun x => metricPair d.γ x a (d.frame x j)) Ω :=
    h.1.contDiffOn_metricPair (fun _ => a) (fun x => d.frame x j) contDiffOn_const
      (h.2.2.2.2.2.2.1 j)
  exact hPair.smul contDiffOn_const

lemma actualCoframeNormalSobolevL_point {Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) {x : X} (hx : x ∈ Ω)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (a : X) :
    actualCoframeNormalSobolevL 1 d a x =
      oneBoundaryCoefficientMulL (vectorNormalJet (fixedCenterCoefficient Q d.γ d.frame x a)) := by
  rw [← h.relativeCoframeNormalSobolev_actual_parameter hx 1 (d.radius x) a]
  change relativeCoframeNormalSobolevL 1 d.γ a ((x,frameVectorLinear d.frame x),d.radius x/d.radius x-1) = _
  change relativeCoframeNormalSobolevL 1 d.γ a ((x,frameVectorLinear d.frame x),0) = _
  exact relativeCoframeNormalSobolev_point h hx Q hQ a
end ShrinkingSpheres
