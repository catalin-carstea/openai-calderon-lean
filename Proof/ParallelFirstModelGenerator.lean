import Proof.ParallelFirstModelDerivativeBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.EnergyBridge

/-- Every genuine compact representative of the same parallel first model
    inherits the existing covariant Hessian bound at the native operator level. -/
theorem Background.parallel_first_model_generator_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) (hK : 1 ≤ K) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (a : X)
    (A1 : ℝ × X → Mat) (hA1 : ContDiff ℝ ∞ A1) (S : Set X) (hS : IsCompact S)
    (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0)
    (hRep : ∀ z ∈ Metric.closedBall (0:X) 2,A1 =ᶠ[𝓝 (0,z)]
      parallelFirstCoefficientModel d.γ d.g₁ y a (frameVectorLinear d.frame y)) :
    ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
      (∀ z,HasDerivAt (fun t => A1 (t,z)) (b z) 0) ∧
      (∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ parallelFirstModelDerivativeBudget hm K M*‖a‖) ∧
      ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ parallelFirstModelDerivativeBudget hm K M*‖a‖ := by
  have hBounds := h.parallel_first_model_joint_bounds hΩ hK hm hy a A1 hA1 S hS hz1 hRep
  exact exists_commonSupport_generator_of_joint_bounds A1 hA1 S hz1
    (parallelFirstModelDerivativeBudget hm K M*‖a‖) (by unfold parallelFirstModelDerivativeBudget;positivity)
    hBounds.1 hBounds.2

end ShrinkingSpheres
