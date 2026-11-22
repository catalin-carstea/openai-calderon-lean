module

public import Proof.CalderonN.MultiplierDefectTaylorEquation

import Mathlib.Tactic

/-! Gauss' scalar weight leaves a quadratic boundary commutator
when the first conormal Taylor terms have been subtracted. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem radial_smoothMultiplierDefect (m u v : SmoothData dim) (z : X dim) :
    fderiv ℝ (smoothMultiplierDefect m u v).1 z z =
      fderiv ℝ v.1 z z-m.1 z*fderiv ℝ u.1 z z-u.1 z*fderiv ℝ m.1 z z := by
  change fderiv ℝ (v.1-(fun x => m.1 x*u.1 x)) z z = _
  rw [fderiv_sub (v.2.differentiable (by simp) z) ((m.2.mul u.2).differentiable (by simp) z),
    fderiv_fun_mul (m.2.differentiable (by simp) z) (u.2.differentiable (by simp) z),
    sub_apply,add_apply,smul_apply,smul_apply,smul_eq_mul,smul_eq_mul]
  ring

theorem conormalTaylor_multiplier_boundary
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (W : SmoothData dim)
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim))
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim} (m : SmoothData dim)
    (U : ConormalTaylorSolutions A ell f)
    (V : ConormalTaylorSolutions A ell ⟨fun z => m.1 z*f.1 z,m.2.mul f.2⟩) (r : ℝ) :
    let w := smoothMultiplierDefect m U.actual V.actual
    let w₀ := smoothMultiplierDefect m U.flat V.flat
    let w₁ := smoothMultiplierDefect m U.first V.first
    let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
    EqOn (fun z => (V.remainder hA r).1 z-m.1 z*(U.remainder hA r).1 z)
      (fun z => W.1 z*fderiv ℝ e.1 z z+
        (W.1 z-1-r*ell z)*fderiv ℝ w₀.1 z z+
        r*(W.1 z-1)*fderiv ℝ w₁.1 z z+
        (W.1 z-1-r*ell z)*(f.1 z*fderiv ℝ m.1 z z)) (standardSphere dim) := by
  dsimp only
  let w := smoothMultiplierDefect m U.actual V.actual
  let w₀ := smoothMultiplierDefect m U.flat V.flat
  let w₁ := smoothMultiplierDefect m U.first V.first
  let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
  intro z hz
  have hE : fderiv ℝ e.1 z z = fderiv ℝ w.1 z z-fderiv ℝ w₀.1 z z-r*fderiv ℝ w₁.1 z z := by
    change fderiv ℝ (w.1-w₀.1-r • w₁.1) z z = _
    have hD : DifferentiableAt ℝ (w.1-w₀.1) z := (w.2.sub w₀.2).differentiable (by simp) z
    have hW₁ : DifferentiableAt ℝ (r • w₁.1) z := (w₁.2.const_smul r).differentiable (by simp) z
    rw [fderiv_sub hD hW₁,
      fderiv_sub (w.2.differentiable (by simp) z) (w₀.2.differentiable (by simp) z),
      fderiv_const_smul (w₁.2.differentiable (by simp) z),sub_apply,sub_apply,smul_apply,smul_eq_mul]
  have h1 : fderiv ℝ w.1 z z =
      fderiv ℝ V.actual.1 z z-m.1 z*fderiv ℝ U.actual.1 z z-f.1 z*fderiv ℝ m.1 z z := by
    dsimp only [w]
    rw [radial_smoothMultiplierDefect,show U.actual.1 z = f.1 z from U.actualTrace hz]
  have h2 : fderiv ℝ w₀.1 z z =
      fderiv ℝ V.flat.1 z z-m.1 z*fderiv ℝ U.flat.1 z z-f.1 z*fderiv ℝ m.1 z z := by
    dsimp only [w₀]
    rw [radial_smoothMultiplierDefect,show U.flat.1 z = f.1 z from U.flatTrace hz]
  have h3 : fderiv ℝ w₁.1 z z = fderiv ℝ V.first.1 z z-m.1 z*fderiv ℝ U.first.1 z z := by
    dsimp only [w₁]
    rw [radial_smoothMultiplierDefect,show U.first.1 z = 0 from U.firstTrace hz,zero_mul,sub_zero]
  change (smoothBallConormal A V.actual.1 z-fderiv ℝ V.flat.1 z z-
    r*(ell z*fderiv ℝ V.flat.1 z z+fderiv ℝ V.first.1 z z)) -
    m.1 z*(smoothBallConormal A U.actual.1 z-fderiv ℝ U.flat.1 z z-
      r*(ell z*fderiv ℝ U.flat.1 z z+fderiv ℝ U.first.1 z z)) =
    W.1 z*fderiv ℝ e.1 z z+(W.1 z-1-r*ell z)*fderiv ℝ w₀.1 z z+
      r*(W.1 z-1)*fderiv ℝ w₁.1 z z+(W.1 z-1-r*ell z)*(f.1 z*fderiv ℝ m.1 z z)
  have hU : smoothBallConormal A U.actual.1 z = W.1 z*fderiv ℝ U.actual.1 z z := hW U.actual hz
  have hV : smoothBallConormal A V.actual.1 z = W.1 z*fderiv ℝ V.actual.1 z z := hW V.actual hz
  rw [hU,hV,hE,h1,h2,h3]
  ring

end CalderonN
