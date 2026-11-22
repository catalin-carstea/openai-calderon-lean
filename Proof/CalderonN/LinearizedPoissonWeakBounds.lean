module

public import Proof.CalderonN.RotatedMultiplierBulkBounds

import Mathlib.Tactic

/-! The differentiated harmonic lift has a weak Taylor estimate even
though differentiating the boundary input would lose an angular derivative. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 7800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_linearized_poisson_weak_taylor
    {A B L : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hL : ContDiff ℝ ∞ L)
    (u u₀ p p₁ : SmoothData dim) (r C G : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hC : 0 ≤ C) (hG : 0 ≤ G) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let D := A-A₀
    let R := B-r • L
    let du := smoothSubtractData u u₀
    let e := smoothSubtractData p ⟨r • p₁.1,p₁.2.const_smul r⟩
    let N := ‖smoothSobolev u₀‖
    let W := C*G
    let H := 1+W*(2+2*W)
    SmoothCoefficientC1Bound D (G*r) → SmoothCoefficientC1Bound B (G*r) →
    SmoothCoefficientC1Bound R (G*r^2) → SmoothCoefficientC1Bound L G →
    SmoothDirichletDivergenceBudget A₀ (fun v => ‖smoothSobolev v‖) C →
    SmoothDirichletDivergenceBudget A (fun v => ‖smoothSobolev v‖) C →
    EqOn u.1 u₀.1 (standardSphere dim) →
    EqOn p.1 0 (standardSphere dim) → EqOn p₁.1 0 (standardSphere dim) →
    EqOn (negativeBallDivergence A u.1) 0 (ball (0:X dim) 1) →
    EqOn (negativeBallDivergence A₀ u₀.1) 0 (ball (0:X dim) 1) →
    EqOn (negativeBallDivergence A p.1) (-negativeBallDivergence B u.1) (ball (0:X dim) 1) →
    EqOn (negativeBallDivergence A₀ p₁.1) (-negativeBallDivergence L u₀.1) (ball (0:X dim) 1) →
    ‖smoothSobolev u‖ ≤ H*N ∧ ‖smoothSobolev du‖ ≤ H*r*N ∧
    ‖smoothSobolev p₁‖ ≤ H*N ∧ ‖smoothSobolev e‖ ≤ H*r^2*N := by
  dsimp only
  intro hD hBR hR hLr hI₀ hI huT hpT hp₁T hu hu₀ hp hp₁
  let A₀ : X dim → Mat dim := fun _ => 1
  let D := A-A₀
  let R := B-r • L
  let du := smoothSubtractData u u₀
  let q : SmoothData dim := ⟨r • p₁.1,p₁.2.const_smul r⟩
  let e := smoothSubtractData p q
  let N := ‖smoothSobolev u₀‖
  let W := C*G
  let H := 1+W*(2+2*W)
  have hW : 0 ≤ W := mul_nonneg hC hG
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hDA : ContDiff ℝ ∞ D := hA.sub hA₀
  have hRA : ContDiff ℝ ∞ R := hB.sub (hL.const_smul r)
  have hLr' : ContDiff ℝ ∞ (r • L) := hL.const_smul r
  have duT : EqOn du.1 0 (standardSphere dim) := fun z hz => sub_eq_zero.mpr (huT hz)
  have eT : EqOn e.1 0 (standardSphere dim) := fun z hz => by
    change p.1 z-r*p₁.1 z = 0
    rw [show p.1 z = 0 from hpT hz,show p₁.1 z = 0 from hp₁T hz,mul_zero,sub_zero]
  have hOne {A' : X dim → Mat dim}
      (hInv : SmoothDirichletDivergenceBudget A' (fun v => ‖smoothSobolev v‖) C)
      {F : X dim → Mat dim} (hF : ContDiff ℝ ∞ F) (Q : ℝ) (hQ : 0 ≤ Q)
      (hFQ : SmoothCoefficientC1Bound F Q)
      (v w : SmoothData dim) (hv : EqOn v.1 0 (standardSphere dim))
      (hEq : EqOn (negativeBallDivergence A' v.1)
        (-negativeBallDivergence F w.1) (ball (0:X dim) 1)) :
      ‖smoothSobolev v‖ ≤ C*Q*‖smoothSobolev w‖ :=
    (hInv 1 (fun _ => F) (fun _ => hF) (fun _ => w) (fun _ => Q) (fun _ => hQ)
      (fun _ => hFQ) v hv (fun z hz => by simpa using hEq hz)).trans_eq
        (by rw [Fin.sum_univ_one,mul_assoc])
  have hdu := hOne hI hDA (G*r) (by positivity) hD du u₀ duT
    (negativeBallDivergence_harmonic_lift_difference hA u u₀ hu hu₀)
  have hN₁ : ‖smoothSobolev du‖ ≤ W*r*N := hdu.trans_eq (by dsimp [W,N]; ring)
  have hp₁N : ‖smoothSobolev p₁‖ ≤ W*N := hOne hI₀ hL G hG hLr p₁ u₀ hp₁T hp₁
  have hScaled : SmoothCoefficientC1Bound (r • D) (G*r^2) := by
    intro z hz
    have hD' : fderiv ℝ (r • D) z = r • fderiv ℝ D z :=
      fderiv_const_smul (hDA.differentiable (by simp) z) r
    have h := hD z hz
    change ‖r • D z‖ ≤ _ ∧ ‖fderiv ℝ (r • D) z‖ ≤ _
    rw [hD']
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact ⟨(mul_le_mul_of_nonneg_left h.1 hr).trans_eq (by ring),
      (mul_le_mul_of_nonneg_left h.2 hr).trans_eq (by ring)⟩
  have heQ : EqOn (negativeBallDivergence A e.1)
      (fun z => -(∑ i : Fin 3,negativeBallDivergence (![B,R,r • D] i) (![du,u₀,p₁] i).1 z))
      (ball (0:X dim) 1) := by
    intro z hz
    have hp₀ : negativeBallDivergence A₀ p₁.1 z = -negativeBallDivergence L u₀.1 z := hp₁ hz
    change negativeBallDivergence A (p.1-r • p₁.1) z = _
    rw [negativeBallDivergence_sub_solution hA p q,hp hz,Pi.neg_apply]
    change -negativeBallDivergence B u.1 z-negativeBallDivergence A (r • p₁.1) z = _
    simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    change _ = -(negativeBallDivergence B (u.1-u₀.1) z+
      (negativeBallDivergence (B-r • L) u₀.1 z+negativeBallDivergence (r • (A-A₀)) p₁.1 z))
    rw [negativeBallDivergence_const_smul_solution hA p₁,
      negativeBallDivergence_sub_solution hB u u₀,negativeBallDivergence_sub_coefficient hB hLr',
      negativeBallDivergence_const_smul_coefficient,negativeBallDivergence_const_smul_coefficient,
      negativeBallDivergence_sub_coefficient hA hA₀,hp₀]
    ring
  have heN' := hI 3 ![B,R,r • D] (by intro i; fin_cases i <;> first | exact hB | exact hRA | exact hDA.const_smul r) ![du,u₀,p₁] ![G*r,G*r^2,G*r^2]
    (by intro i; fin_cases i <;> first | exact mul_nonneg hG hr | exact mul_nonneg hG (sq_nonneg r))
    (by intro i; fin_cases i <;> first | exact hBR | exact hR | exact hScaled) e eT heQ
  have heN : ‖smoothSobolev e‖ ≤ W*(2*W+1)*r^2*N := by
    simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero] at heN'
    refine heN'.trans ?_
    calc
      _ ≤ C*(G*r*(W*r*N)+(G*r^2*N+G*r^2*(W*N))) := by gcongr
      _ = _ := by dsimp [W]; ring
  have hHU : 1+W ≤ H := by dsimp only [H]; nlinarith only [hW,sq_nonneg W]
  have hHW : W ≤ H := by linarith only [hHU]
  have hHE : W*(2*W+1) ≤ H := by dsimp only [H]; nlinarith only [hW]
  refine ⟨?_,hN₁.trans (by gcongr),hp₁N.trans (by gcongr),heN.trans (by gcongr)⟩
  have hUn := (smoothBallSobolev_norm_le_add_sub 1 u u₀).trans
    (add_le_add le_rfl hN₁)
  apply (show ‖smoothSobolev u‖ ≤ N+W*r*N from hUn).trans
  calc
    _ ≤ N+W*1*N := by gcongr
    _ = (1+W)*N := by ring
    _ ≤ _ := by gcongr

end CalderonN
