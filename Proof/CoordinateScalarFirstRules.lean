import Proof.CoordinateSecondJetCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma coordDeriv_add_at (f g : X → ℝ) {y : X} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (i : I) :
    coordDeriv i (fun x => f x+g x) y = coordDeriv i f y+coordDeriv i g y := by
  unfold coordDeriv
  rw [fderiv_fun_add hf hg]
  rfl

lemma coordDeriv_mul_at (f g : X → ℝ) {y : X} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (i : I) :
    coordDeriv i (fun x => f x*g x) y = coordDeriv i f y*g y+f y*coordDeriv i g y := by
  unfold coordDeriv
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul]
  ring

lemma coordDeriv_fintype_sum_at {ι : Type*} [Fintype ι] (f : ι → X → ℝ) {y : X}
    (hf : ∀ j,DifferentiableAt ℝ (f j) y) (i : I) :
    coordDeriv i (fun x => ∑ j,f j x) y = ∑ j,coordDeriv i (f j) y := by
  unfold coordDeriv
  rw [fderiv_fun_sum (fun j hj => hf j)]
  simp only [_root_.sum_apply]

lemma abs_coordDeriv_mul_le (f g : X → ℝ) {y : X} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) (i : I) {B DB C DC : ℝ}
    (hB : 0 ≤ B) (hDB : 0 ≤ DB)
    (hfv : |f y| ≤ B) (hfd : |coordDeriv i f y| ≤ DB)
    (hgv : |g y| ≤ C) (hgd : |coordDeriv i g y| ≤ DC) :
    |coordDeriv i (fun x => f x*g x) y| ≤ DB*C+B*DC := by
  rw [coordDeriv_mul_at f g hf hg i]
  exact (abs_add_le _ _).trans (add_le_add
    (by rw [abs_mul];exact mul_le_mul hfd hgv (abs_nonneg _) hDB)
    (by rw [abs_mul];exact mul_le_mul hfv hgd (abs_nonneg _) hB))

lemma abs_coordDeriv_fintype_sum_le {ι : Type*} [Fintype ι] (f : ι → X → ℝ) {y : X}
    (hf : ∀ j,DifferentiableAt ℝ (f j) y) (i : I) (C : ℝ)
    (hBound : ∀ j,|coordDeriv i (f j) y| ≤ C) :
    |coordDeriv i (fun x => ∑ j,f j x) y| ≤ (Fintype.card ι:ℝ)*C := by
  rw [coordDeriv_fintype_sum_at f hf i]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (fun j hj => hBound j)).trans_eq (by simp))
end ShrinkingSpheres
