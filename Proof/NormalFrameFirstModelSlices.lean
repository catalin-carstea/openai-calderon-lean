import Proof.NormalFrameFirstModelFamily
import Proof.NormalFrameRadialTaylorModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SmoothSphereRotation

lemma normalFrame_scaled_first_model_parallel (d : Data) (y a z : X) (t : ℝ) (hr : d.radius y ≠ 0) :
    normalFrameScaledFirstModelCoefficient d.γ d.g₁ (d.radius y)
      (normalFrameParallelCurve d.γ d.frame d.radius y a t,z) =
      parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y) (t,z) := by
  change (d.radius y/d.radius y) •
    (normalFrameFirstCovector d.γ d.g₁ (normalFrameParallelCurve d.γ d.frame d.radius y a t) z • (1:Mat)) = _
  rw [div_self hr,one_smul,normalFrameFirstCovector_parallel]
  rfl

lemma Background.normalFrame_scaled_first_model_radius {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (t : ℝ) (z : X) (hr : d.radius y ≠ 0) :
    normalFrameScaledFirstModelCoefficient d.γ d.g₁ (d.radius y)
      (normalFrameRadiusCurve d.frame d.radius y t,z) =
      relativeDilationFamily (scalarFirstCoefficient (firstDensityLogCovector d y)) (t,z) := by
  have hCov : normalFrameFirstCovector d.γ d.g₁ (normalFrameRadiusCurve d.frame d.radius y t) =
      firstDensityLogCovector d y := h.normalFrameFirstCovector_actual hΩ hK hy
  change (((1+t)*d.radius y)/d.radius y) •
    (normalFrameFirstCovector d.γ d.g₁ (normalFrameRadiusCurve d.frame d.radius y t) z • (1:Mat)) = _
  rw [hCov,mul_div_cancel_right₀ _ hr]
  simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul,smul_smul] using
    (relativeDilation_scalarFirstCoefficient (firstDensityLogCovector d y) (t,z)).symm

lemma Background.normalFrame_scaled_first_model_rotation {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (i j : I) (t : ℝ) (z : X) (hr : d.radius y ≠ 0) :
    normalFrameScaledFirstModelCoefficient d.γ d.g₁ (d.radius y)
      (normalFrameRotationCurve d.frame d.radius y i j t,z) =
      firstDensityLogCovector d y (coordinateRotation i j t z) • (1:Mat) := by
  change (d.radius y/d.radius y) •
    (normalFrameFirstCovector d.γ d.g₁ (normalFrameRotationCurve d.frame d.radius y i j t) z • (1:Mat)) = _
  rw [div_self hr,one_smul,h.normalFrameFirstCovector_rotation hΩ hK hy]
  rfl

end ShrinkingSpheres
