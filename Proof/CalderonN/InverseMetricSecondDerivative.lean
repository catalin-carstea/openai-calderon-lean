module

import Proof.CalderonN.InverseMetricDerivative
import Proof.CalderonN.BackgroundBudgets
public import Proof.CalderonN.ChristoffelDerivative

import Mathlib.Tactic

/-! Adapted from `InverseMetricSecondDerivative` in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The second inverse-metric coordinate jet uses only ellipticity and the first two
    actual background jets. This supplies the arbitrary-geometry coefficient budget. -/
theorem Elliptic.inverse_second_coordinate_bound {Y : Set (X dim)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField dim)}
    (h : Elliptic Y K g) (hK : 0 < K) {y : (X dim)} (hy : y ∈ Y)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂) (i j k l : (I dim)) :
    |coordDeriv l (coordDeriv k (fun x => (g x)⁻¹ i j)) y| ≤ (dim:ℝ)^2*((2*(dim:ℝ)^2)*K^3*M₁^2+K^2*M₂) := by
  let F (a b : (I dim)) (x : (X dim)) : ℝ := (g x)⁻¹ i a*coordDeriv k (fun x => g x a b) x*(g x)⁻¹ b j
  have hi (a b : (I dim)) := ((h.contDiffOn_inverse_entry hK a b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hg (a b : (I dim)) := h.differentiableAt_fderiv_entry hY hy a b
  have hd (a b : (I dim)) : DifferentiableAt ℝ (coordDeriv k (fun x => g x a b)) y :=
    ((((h.1 a b).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hF (a b : (I dim)) : DifferentiableAt ℝ (F a b) y := ((hi i a).fun_mul (hd a b)).fun_mul (hi b j)
  have hEq : coordDeriv k (fun x => (g x)⁻¹ i j) =ᶠ[𝓝 y] (fun x => -(∑ a,∑ b,F a b x)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact fderiv_inverse_metric_entries hY h hK hx (axis k) i j
  have hsum : HasFDerivAt (fun x => ∑ a,∑ b,F a b x) (∑ a,∑ b,fderiv ℝ (F a b) y) y :=
    HasFDerivAt.fun_sum (fun a _ => HasFDerivAt.fun_sum (fun b _ => (hF a b).hasFDerivAt))
  have heq : coordDeriv l (coordDeriv k (fun x => (g x)⁻¹ i j)) y = -(∑ a,∑ b,coordDeriv l (F a b) y) := by
    change (fderiv ℝ (coordDeriv k (fun x => (g x)⁻¹ i j)) y) (axis l) = _
    have hneg : HasFDerivAt (fun x => -(∑ a,∑ b,F a b x)) (-(∑ a,∑ b,fderiv ℝ (F a b) y)) y := hsum.neg
    rw [hEq.fderiv_eq,hneg.fderiv]
    simp only [neg_apply,sum_apply,coordDeriv]
  have hInv (a b : (I dim)) : |coordDeriv l (fun x => (g x)⁻¹ a b) y| ≤ (dim:ℝ)^2*K^2*M₁ := by
    simpa only [norm_axis,mul_one,coordDeriv] using h.inverse_derivative_entry_bound hY hK hy M₁ hM₁ hD (axis l) a b
  have hFirst (a b : (I dim)) : |coordDeriv k (fun x => g x a b) y| ≤ M₁ := (coordDeriv_abs_le _ y k).trans (hD a b)
  have hSecond (a b : (I dim)) : |coordDeriv l (coordDeriv k (fun x => g x a b)) y| ≤ M₂ := by
    simpa only [norm_axis,mul_one,coordDeriv] using fderiv_coordDeriv_abs_le (fun x => g x a b) y k (hg a b) M₂ (hD₂ a b) (axis l)
  have ht (a b : (I dim)) : |coordDeriv l (F a b) y| ≤ (2*(dim:ℝ)^2)*K^3*M₁^2+K^2*M₂ := by
    have hprod := (((hi i a).hasFDerivAt.fun_mul (hd a b).hasFDerivAt).fun_mul (hi b j).hasFDerivAt).fderiv
    have he : coordDeriv l (F a b) y =
        (coordDeriv l (fun x => (g x)⁻¹ i a) y*coordDeriv k (fun x => g x a b) y+
          (g y)⁻¹ i a*coordDeriv l (coordDeriv k (fun x => g x a b)) y)*(g y)⁻¹ b j+
          ((g y)⁻¹ i a*coordDeriv k (fun x => g x a b) y)*coordDeriv l (fun x => (g x)⁻¹ b j) y := by
      change (fderiv ℝ (fun x => (g x)⁻¹ i a*coordDeriv k (fun x => g x a b) x*(g x)⁻¹ b j) y) (axis l) = _
      rw [hprod]
      simp only [add_apply,smul_apply,smul_eq_mul,coordDeriv]
      ring
    rw [he,add_mul]
    have h1 : |coordDeriv l (fun x => (g x)⁻¹ i a) y*coordDeriv k (fun x => g x a b) y*(g y)⁻¹ b j| ≤ ((dim:ℝ)^2*K^2*M₁)*M₁*K := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hInv i a) (hFirst a b) (abs_nonneg _) (by positivity))
        (h.inverse_entry_bound hK hy b j) (abs_nonneg _) (by positivity)
    have h2 : |(g y)⁻¹ i a*coordDeriv l (coordDeriv k (fun x => g x a b)) y*(g y)⁻¹ b j| ≤ K*M₂*K := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (h.inverse_entry_bound hK hy i a) (hSecond a b) (abs_nonneg _) hK.le)
        (h.inverse_entry_bound hK hy b j) (abs_nonneg _) (by positivity)
    have h3 : |((g y)⁻¹ i a*coordDeriv k (fun x => g x a b) y)*coordDeriv l (fun x => (g x)⁻¹ b j) y| ≤ K*M₁*((dim:ℝ)^2*K^2*M₁) := by
      rw [abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (h.inverse_entry_bound hK hy i a) (hFirst a b) (abs_nonneg _) hK.le)
        (hInv b j) (abs_nonneg _) (by positivity)
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by nlinarith only [h1,h2,h3])
  rw [heq,abs_neg]
  calc
    _ ≤ ∑ a,∑ b,|coordDeriv l (F a b) y| := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _a : (I dim),∑ _b : (I dim),((2*(dim:ℝ)^2)*K^3*M₁^2+K^2*M₂) := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ht a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end CalderonN
