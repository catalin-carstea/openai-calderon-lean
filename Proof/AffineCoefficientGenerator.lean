import Proof.CommonSupportDirectionalGenerators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

private lemma norm_affine_quadratic_sum_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (u v : E) (r q1 qD : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hq1 : 0 ≤ q1) (hqD : 0 ≤ qD)
    (hu : ‖u‖ ≤ q1) (hv : ‖v‖ ≤ qD*r^2) : ‖r • u+v‖ ≤ (q1+qD)*r := by
  calc
    _ ≤ ‖r • u‖+‖v‖ := norm_add_le _ _
    _ ≤ r*q1+qD*r^2 := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr];gcongr
    _ ≤ r*q1+qD*r := by gcongr;nlinarith only [mul_le_mul_of_nonneg_left hr1 hr]
    _ = _ := by ring

/-- The same first-model and quadratic residual generators give the genuine
    principal generator, with a radius-linear local C1 bound. -/
theorem commonSupport_affine_generator_bounds
    (a a1 aD : ℝ × X → Mat) (S : Set X) (r q1 qD : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hq1 : 0 ≤ q1) (hqD : 0 ≤ qD)
    (hField : ∀ p,aD p = a p-r • a1 p)
    (b1 bD : X → Mat) (hb1 : ContDiff ℝ ∞ b1) (hbD : ContDiff ℝ ∞ bD)
    (hz1 : ∀ z,z ∉ S → b1 z = 0) (hzD : ∀ z,z ∉ S → bD z = 0)
    (hCurve1 : ∀ z,HasDerivAt (fun t => a1 (t,z)) (b1 z) 0)
    (hCurveD : ∀ z,HasDerivAt (fun t => aD (t,z)) (bD z) 0)
    (hV1 : ∀ z ∈ (ballOpens:Set X),‖b1 z‖ ≤ q1)
    (hD1 : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b1 z‖ ≤ q1)
    (hVD : ∀ z ∈ (ballOpens:Set X),‖bD z‖ ≤ qD*r^2)
    (hDD : ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ bD z‖ ≤ qD*r^2) :
    ∃ b : X → Mat,ContDiff ℝ ∞ b ∧ (∀ z,z ∉ S → b z = 0) ∧
      (∀ z,HasDerivAt (fun t => a (t,z)) (b z) 0) ∧
      (∀ z ∈ (ballOpens:Set X),‖b z‖ ≤ (q1+qD)*r) ∧
      ∀ z ∈ (ballOpens:Set X),‖fderiv ℝ b z‖ ≤ (q1+qD)*r := by
  let b := fun z => r • b1 z+bD z
  have hb : ContDiff ℝ ∞ b := (hb1.const_smul r).add hbD
  refine ⟨b,hb,?_,?_,?_,?_⟩
  · intro z hz
    simp only [b,hz1 z hz,hzD z hz,smul_zero,zero_add]
  · intro z
    have hFun : (fun t => a (t,z)) = fun t => r • a1 (t,z)+aD (t,z) := by
      funext t
      rw [hField]
      module
    rw [hFun]
    exact ((hCurve1 z).const_smul r).add (hCurveD z)
  · intro z hz
    exact norm_affine_quadratic_sum_le (b1 z) (bD z) r q1 qD hr hr1 hq1 hqD (hV1 z hz) (hVD z hz)
  · intro z hz
    have hDer : fderiv ℝ b z = r • fderiv ℝ b1 z+fderiv ℝ bD z :=
      ((((hb1.differentiable (by simp) z).hasFDerivAt.const_smul r).add
        (hbD.differentiable (by simp) z).hasFDerivAt)).fderiv
    rw [hDer]
    exact norm_affine_quadratic_sum_le _ _ r q1 qD hr hr1 hq1 hqD (hD1 z hz) (hDD z hz)

end ShrinkingSpheres
