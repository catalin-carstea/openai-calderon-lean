module

public import Proof.CalderonN.GaussVelocityAdjoint
public import Proof.CalderonN.ParametricBallVelocityAdjoint

import Proof.CalderonN.FixedBallPoissonCongruence
import Mathlib.Tactic

/-! Remove the constant metric density from the actual conormal datum.
The remaining weight conjugates the radial trace. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2350000
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace
namespace CalderonN

open OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {P : Type}

theorem parametricBallVelocityAdjoint_gauss_radial_response
    (p : P) {g : P × X dim → Mat dim} {V : P × X dim → X dim} {ψ : P × X dim → ℝ}
    {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hBU : closedBall (0 : X dim) 1 ⊆ U) (hSS : standardSphere dim ⊆ S) (hSU : S ⊆ U)
    (hS₀ : (0 : X dim) ∉ S) (hg : SmoothMetric U (fun z => g (p,z)))
    (hV : ContDiffOn ℝ ∞ (fun z => V (p,z)) S) (hψ : ContDiffOn ℝ ∞ (fun z => ψ (p,z)) S)
    (c : ℝ) (hc : c ≠ 0) (W : X dim → ℝ)
    (hW : EqOn (ballConormalVector (fun z => g (p,z))) (fun z => (c*W z) • z)
      (standardSphere dim))
    {b : X dim → ℝ}
    (hb : FixedBallSolution (fun z => g (p,z)) (fun z => ψ (p,z)*⟪z,V (p,z)⟫_ℝ/W z) b)
    {z : X dim} (hz : z ∈ standardSphere dim) :
    parametricBallVelocityAdjoint g V ψ (p,z) =
      W z*fderiv ℝ b z z -
        ∑ i,∑ j,sphereRotationDerivative i j (fun x => ψ (p,x)*(x i*V (p,x) j)) z := by
  have he : EqOn (fun x => velocityBoundaryDatum g V ψ (p,x))
      (fun x => c⁻¹*(ψ (p,x)*⟪x,V (p,x)⟫_ℝ/W x)) (standardSphere dim) := by
    intro x hx
    have hx₁ := mem_sphere_zero_iff_norm.mp hx
    have hx₂ : ⟪x,x⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,hx₁,one_pow]
    change ψ (p,x)*(⟪x,V (p,x)⟫_ℝ/⟪x,ballConormalVector (fun z => g (p,z)) x⟫_ℝ) =
      c⁻¹*(ψ (p,x)*⟪x,V (p,x)⟫_ℝ/W x)
    rw [hW hx,real_inner_smul_right,hx₂,mul_one,div_eq_mul_inv,mul_inv]
    simp only [div_eq_mul_inv]
    ring
  have hEq := fixedBallPoisson_fderiv_eq_of_solution hU hBU hg (hb.const_mul c⁻¹) he
    (sphere_subset_closedBall hz)
  rw [parametricBallVelocityAdjoint_on_sphere g V ψ p hz,
    ballVelocityAdjoint_gauss_formula hS hSS hS₀ ⟨fun i j => (hg.1 i j).mono hSU,
      fun x hx => hg.2 x (hSU hx)⟩ hV hψ (fun x => c*W x) hW _ hz,hEq]
  rw [fderiv_const_mul (hb.1.differentiable (by simp) z),smul_apply,smul_eq_mul,
    show c*W z*(c⁻¹*fderiv ℝ b z z) = W z*fderiv ℝ b z z by
      rw [show c*W z*(c⁻¹*fderiv ℝ b z z) =
        (c*c⁻¹)*(W z*fderiv ℝ b z z) by ring,mul_inv_cancel₀ hc,one_mul]]

end CalderonN
