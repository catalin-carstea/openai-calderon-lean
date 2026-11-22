module

public import Proof.CalderonN.LinearizedRadialRow
public import Proof.CalderonN.ActualAngularRadialWeights

import Mathlib.Tactic

/-! A smooth extension of the derivative of the radial eigenvalue.
Its quadratic part has controlled value and gradient on the closed ball. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_linearized_radial_weights
    (ell : X dim →L[ℝ] ℝ) {G : X dim → Mat dim} (hG : ContDiff ℝ ∞ G)
    (hRow : ∀ z ∈ standardSphere dim, IsRadialRow z (G z))
    (r P Q : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hEll : ‖ell‖ ≤ 2*P)
    (hRem : ∀ z ∈ closedBall (0 : X dim) 1,
      let R := G-r • (fun w => ell w • (1 : Mat dim))
      ‖R z‖ ≤ Q*r^2 ∧ ‖fderiv ℝ R z‖ ≤ Q*r^2) :
    ∃ V E : SmoothData dim,
      (∀ b : SmoothData dim,
        EqOn (smoothBallConormal G b.1) (fun z => V.1 z*fderiv ℝ b.1 z z) (standardSphere dim)) ∧
      (∀ z, V.1 z = r*ell z+E.1 z) ∧
      ∀ z ∈ closedBall (0 : X dim) 1,
        |V.1 z| ≤ (2*P+3*(dim : ℝ)^2*Q)*r ∧
        ‖fderiv ℝ V.1 z‖ ≤ (2*P+3*(dim : ℝ)^2*Q)*r ∧
        |E.1 z| ≤ 3*(dim : ℝ)^2*Q*r^2 ∧
        ‖fderiv ℝ E.1 z‖ ≤ 3*(dim : ℝ)^2*Q*r^2 := by
  let L (z : X dim) := r • (ell z • (1 : Mat dim))
  let R := G-L
  have hL : ContDiff ℝ ∞ L := (ell.contDiff.smul contDiff_const).const_smul r
  have hR : ContDiff ℝ ∞ R := hG.sub hL
  let E : SmoothData dim := ⟨scalarQuadraticCoefficient R,contDiff_scalarQuadraticCoefficient hR⟩
  let V : SmoothData dim := ⟨fun z => r*ell z+E.1 z,(contDiff_const.mul ell.contDiff).add E.2⟩
  refine ⟨V,E,?_,fun _ => rfl,?_⟩
  · intro b z hz
    rw [smoothBallConormal_eq_of_radialRow G z b.1 (hRow z hz)]
    congr 1
    change scalarQuadraticCoefficient G z = r*ell z+scalarQuadraticCoefficient R z
    rw [show R = G-L from rfl,scalarQuadraticCoefficient_sub,Pi.sub_apply,
      scalarQuadraticCoefficient_smul_linear_at_sphere ell r hz]
    ring
  intro z hz
  let M := 3*(dim : ℝ)^2*Q
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hzN := mem_closedBall_zero_iff.mp hz
  have hb := hRem z hz
  have hE₀ : |E.1 z| ≤ M*r^2 := by
    refine (abs_scalarQuadraticCoefficient_le (A:=R) hzN (Q*r^2) (by positivity) hb.1).trans ?_
    dsimp only [M]
    nlinarith only [show 0 ≤ (dim : ℝ)^2*Q*r^2 by positivity]
  have hE₁ : ‖fderiv ℝ E.1 z‖ ≤ M*r^2 :=
    (norm_fderiv_scalarQuadraticCoefficient_le hR hzN (Q*r^2) (by positivity) hb.1 hb.2).trans_eq
      (by dsimp [M]; ring)
  have hN : r*(2*P)+M*r^2 ≤ (2*P+M)*r := by
    have hh := mul_le_mul_of_nonneg_left hr₁ (mul_nonneg hM hr.le)
    nlinarith only [hh]
  have hℓ : |ell z| ≤ 2*P := (ell.le_opNorm z).trans
    ((mul_le_mul hEll hzN (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
  refine ⟨((abs_add_le _ _).trans (add_le_add ?_ hE₀)).trans hN,?_,hE₀,hE₁⟩
  · rw [abs_mul,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hℓ hr.le
  · have hD : fderiv ℝ (fun x => r*ell x) z = r • ell := by
      change fderiv ℝ (r • ⇑ell) z = _
      have h := fderiv_const_smul (ell.differentiable z) r
      change fderiv ℝ (r • ⇑ell) z = _ at h
      rw [h,ContinuousLinearMap.fderiv]
    change ‖fderiv ℝ (fun x => r*ell x + E.1 x) z‖ ≤ _
    have hAdd := fderiv_fun_add ((differentiableAt_const r).mul (ell.differentiable z))
      (E.2.differentiable (by simp) z)
    change fderiv ℝ (fun x => r*ell x+E.1 x) z = fderiv ℝ (fun x => r*ell x) z+_ at hAdd
    rw [hAdd,hD]
    exact ((norm_add_le _ _).trans (add_le_add (by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hEll hr.le) hE₁)).trans hN

end CalderonN
