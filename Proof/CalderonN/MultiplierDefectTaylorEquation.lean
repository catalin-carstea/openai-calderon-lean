module

public import Proof.CalderonN.MultiplierDefectEquation

import Mathlib.Tactic

/-! Each forcing term in the second-order Taylor remainder comes from
the corresponding coefficient or solution Taylor term. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem multiplierForcing_sub_solution (A : X dim → Mat dim) (m u v : SmoothData dim) (z : X dim) :
    greenSourceCutoffError A m.1 (u.1-v.1) z =
      greenSourceCutoffError A m.1 u.1 z-greenSourceCutoffError A m.1 v.1 z := by
  have h (j : I dim) :
      coordDeriv j (u.1-v.1) z = coordDeriv j u.1 z-coordDeriv j v.1 z := by
    unfold coordDeriv
    rw [fderiv_sub (u.2.differentiable (by simp) z) (v.2.differentiable (by simp) z),sub_apply]
  unfold greenSourceCutoffError
  simp_rw [h,mul_sub,Finset.sum_sub_distrib]
  change (u.1 z-v.1 z)*_ - _ = _
  ring

theorem multiplierForcing_scale_solution (A : X dim → Mat dim) (m u : SmoothData dim) (r : ℝ) (z : X dim) :
    greenSourceCutoffError A m.1 (r • u.1) z = r*greenSourceCutoffError A m.1 u.1 z := by
  have h (j : I dim) : coordDeriv j (r • u.1) z = r*coordDeriv j u.1 z := by
    unfold coordDeriv
    rw [fderiv_const_smul (u.2.differentiable (by simp) z),smul_apply,smul_eq_mul]
  unfold greenSourceCutoffError
  simp_rw [h]
  have hS : (∑ i,∑ j, A z i j*coordDeriv i m.1 z*(r*coordDeriv j u.1 z)) =
      r*(∑ i,∑ j, A z i j*coordDeriv i m.1 z*coordDeriv j u.1 z) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hS]
  change r*u.1 z*negativeBallDivergence A m.1 z- _ = _
  ring

theorem multiplierForcing_sub_coefficients {A B : X dim → Mat dim}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (m u : SmoothData dim) (z : X dim) :
    greenSourceCutoffError (A-B) m.1 u.1 z =
      greenSourceCutoffError A m.1 u.1 z-greenSourceCutoffError B m.1 u.1 z := by
  unfold greenSourceCutoffError
  rw [negativeBallDivergence_sub_coefficient hA hB m]
  simp only [Pi.sub_apply,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  ring

theorem multiplierForcing_scale_coefficient (A : X dim → Mat dim) (m u : SmoothData dim) (r : ℝ) (z : X dim) :
    greenSourceCutoffError (r • A) m.1 u.1 z = r*greenSourceCutoffError A m.1 u.1 z := by
  unfold greenSourceCutoffError
  rw [negativeBallDivergence_const_smul_coefficient]
  simp only [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
  ring

theorem multiplier_defect_taylor_equation {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, ∀ i j,A z i j = A z j i)
    {ell : X dim →L[ℝ] ℝ} {f : SmoothData dim}
    (m : SmoothData dim)
    (U : ConormalTaylorSolutions A ell f)
    (V : ConormalTaylorSolutions A ell ⟨fun z => m.1 z*f.1 z,m.2.mul f.2⟩) (r : ℝ) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let A₁ : X dim → Mat dim := fun z => ell z • 1
    let D := A-A₀
    let R := D-r • A₁
    let w := smoothMultiplierDefect m U.actual V.actual
    let w₀ := smoothMultiplierDefect m U.flat V.flat
    let w₁ := smoothMultiplierDefect m U.first V.first
    let e : SmoothData dim := ⟨w.1-w₀.1-r • w₁.1,(w.2.sub w₀.2).sub (w₁.2.const_smul r)⟩
    let E : SmoothData dim := ⟨U.actual.1-U.flat.1-r • U.first.1,
      (U.actual.2.sub U.flat.2).sub (U.first.2.const_smul r)⟩
    EqOn e.1 0 (standardSphere dim) ∧
    EqOn (negativeBallDivergence A e.1)
      (fun z => -greenSourceCutoffError A m.1 E.1 z-greenSourceCutoffError R m.1 U.flat.1 z-
        r*greenSourceCutoffError D m.1 U.first.1 z-negativeBallDivergence R w₀.1 z-
        r*negativeBallDivergence D w₁.1 z) (ball (0 : X dim) 1) := by
  dsimp only
  let A₀ : X dim → Mat dim := fun _ => 1
  let A₁ : X dim → Mat dim := fun z => ell z • 1
  let w := smoothMultiplierDefect m U.actual V.actual
  let w₀ := smoothMultiplierDefect m U.flat V.flat
  let w₁ := smoothMultiplierDefect m U.first V.first
  let E₀ : SmoothData dim := ⟨U.actual.1-U.flat.1,U.actual.2.sub U.flat.2⟩
  let E₁ : SmoothData dim := ⟨r • U.first.1,U.first.2.const_smul r⟩
  let d₀ : SmoothData dim := ⟨w.1-w₀.1,w.2.sub w₀.2⟩
  let d₁ : SmoothData dim := ⟨r • w₁.1,w₁.2.const_smul r⟩
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hA₁ : ContDiff ℝ ∞ A₁ := ell.contDiff.smul contDiff_const
  have hD : ContDiff ℝ ∞ (A-A₀) := hA.sub hA₀
  have hA₁' : ContDiff ℝ ∞ (r • A₁) := hA₁.const_smul r
  obtain ⟨hwT,hw₀T,hw₁T,hw,hw₀,hw₁⟩ := conormalTaylorSolutions_multiplierDefects hA hSym m U V
  refine ⟨?_,?_⟩
  · intro z hz
    change w.1 z-w₀.1 z-r*w₁.1 z = 0
    rw [show w.1 z = 0 from hwT hz,show w₀.1 z = 0 from hw₀T hz,
      show w₁.1 z = 0 from hw₁T hz,sub_zero,mul_zero,sub_zero]
  · intro z hz
    change negativeBallDivergence A (d₀.1-d₁.1) z =
      -greenSourceCutoffError A m.1 (E₀.1-E₁.1) z -
      greenSourceCutoffError (A-A₀-r • A₁) m.1 U.flat.1 z -
      r*greenSourceCutoffError (A-A₀) m.1 U.first.1 z -
      negativeBallDivergence (A-A₀-r • A₁) w₀.1 z-r*negativeBallDivergence (A-A₀) w₁.1 z
    have hwz : negativeBallDivergence A w.1 z = -greenSourceCutoffError A m.1 U.actual.1 z := hw hz
    have hw₀z : negativeBallDivergence A₀ w₀.1 z = -greenSourceCutoffError A₀ m.1 U.flat.1 z := hw₀ hz
    have hw₁z : negativeBallDivergence A₀ w₁.1 z = -negativeBallDivergence A₁ w₀.1 z -
      greenSourceCutoffError A₁ m.1 U.flat.1 z-greenSourceCutoffError A₀ m.1 U.first.1 z := hw₁ hz
    rw [negativeBallDivergence_sub_solution hA d₀ d₁,multiplierForcing_sub_solution A m E₀ E₁]
    dsimp only [d₀,d₁,E₀,E₁]
    rw [negativeBallDivergence_sub_solution hA w w₀,negativeBallDivergence_const_smul_solution hA w₁,
      multiplierForcing_sub_solution A m U.actual U.flat,multiplierForcing_scale_solution A m U.first,
      multiplierForcing_sub_coefficients hD hA₁',
      multiplierForcing_sub_coefficients hA hA₀,multiplierForcing_sub_coefficients hA hA₀,
      multiplierForcing_scale_coefficient,
      negativeBallDivergence_sub_coefficient hD hA₁',
      negativeBallDivergence_sub_coefficient hA hA₀,negativeBallDivergence_sub_coefficient hA hA₀,
      negativeBallDivergence_const_smul_coefficient,hwz,hw₀z,hw₁z]
    ring

end CalderonN
