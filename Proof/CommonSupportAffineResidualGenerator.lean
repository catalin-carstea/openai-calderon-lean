import Proof.CommonSupportDirectionalGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Subtract the same compact first model. The constant flat coefficient
    disappears from parameter derivatives, so no noncompact residual is introduced. -/
theorem commonSupport_affine_residual_generator_bounds
    (A A1 : ℝ × X → Mat) (hA : ContDiff ℝ ∞ A) (hA1 : ContDiff ℝ ∞ A1)
    (S : Set X) (hS : IsCompact S) (hz : ∀ t z,z ∉ S → A (t,z) = 0)
    (hz1 : ∀ t z,z ∉ S → A1 (t,z) = 0) (r q : ℝ) (hq : 0 ≤ q)
    (h0 : ∀ z ∈ (ballOpens:Set X),∀ i j,
      |fderiv ℝ (fun p => A p i j-(1:Mat) i j-r*A1 p i j) (0,z) (1,0)| ≤ q)
    (h1 : ∀ z ∈ (ballOpens:Set X),∀ v : X,∀ i j,
      |fderiv ℝ (fderiv ℝ (fun p => A p i j-(1:Mat) i j-r*A1 p i j)) (0,z) (0,v) (1,0)| ≤ q*‖v‖) :
    ∃ D : ℝ × X → Mat,∃ hD : ContDiff ℝ ∞ D,∃ hzD : ∀ t z,z ∉ S → D (t,z) = 0,
      (∀ p,D p = A p-r • A1 p) ∧ ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
        (∀ z,HasDerivAt (fun t => D (t,z)) (b z) 0) ∧
        (∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ q) ∧ ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ q := by
  let D : ℝ × X → Mat := fun p => A p-r • A1 p
  have hD : ContDiff ℝ ∞ D := hA.sub (hA1.const_smul r)
  have hzD : ∀ t z,z ∉ S → D (t,z) = 0 := by
    intro t z hzS;simp only [D,hz t z hzS,hz1 t z hzS,smul_zero,sub_zero]
  have hDeriv (i j : I) : fderiv ℝ (fun p => A p i j-(1:Mat) i j-r*A1 p i j) =
      fderiv ℝ (fun p => D p i j) := by
    have hFun : (fun p => A p i j-(1:Mat) i j-r*A1 p i j) = fun p => D p i j-(1:Mat) i j := by
      funext p
      change A p i j-(1:Mat) i j-r*A1 p i j = (A p i j-r*A1 p i j)-(1:Mat) i j
      ring
    rw [hFun]
    funext p
    exact fderiv_sub_const _
  refine ⟨D,hD,hzD,(fun _ => rfl),?_⟩
  apply exists_commonSupport_generator_of_joint_bounds D hD S hzD q hq
  · intro z hzB i j;rw [← hDeriv];exact h0 z hzB i j
  · intro z hzB v i j;rw [← hDeriv];exact h1 z hzB v i j

end ShrinkingSpheres
