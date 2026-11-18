import Proof.ScalarInverseSecondJet
import Proof.MetricCoefficientSecondDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
open scoped ContDiff
namespace ShrinkingSpheres

/-- A relative coordinate budget for a positive scalar remains relative for its
inverse. The coordinate-to-operator constants are only dimension constants. -/
theorem scalar_inverse_relative_coordinate_jets (f : X → ℝ) (y : X)
    (hf : ContDiffAt ℝ ∞ f y) (hpos : 0 < f y) (D1 D2 : ℝ)
    (hD10 : 0 ≤ D1) (hD20 : 0 ≤ D2)
    (hD1 : ∀ i,|coordDeriv i f y| ≤ D1*f y)
    (hD2 : ∀ i j,|coordDeriv i (coordDeriv j f) y| ≤ D2*f y) :
    (∀ i,|coordDeriv i (fun x => (f x)⁻¹) y| ≤ (3*D1)*(f y)⁻¹) ∧
    (∀ i j,|coordDeriv i (coordDeriv j (fun x => (f x)⁻¹)) y| ≤
      (9*D2+18*D1^2)*(f y)⁻¹) := by
  have hN1 : ‖fderiv ℝ f y‖ ≤ 3*D1*f y := by
    convert norm_linear_le_of_axis_bound (fderiv ℝ f y) (D1*f y) (by positivity)
      (fun a => by simpa only [Real.norm_eq_abs,coordDeriv] using hD1 a) using 1 <;> ring
  have hN2 : ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ 9*D2*f y := by
    have hd := ((hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp))
    convert norm_bilinear_le_of_axis_bound (fderiv ℝ (fderiv ℝ f) y) (D2*f y) (by positivity)
      (fun a b => by rw [← coordinate_second_derivative f y hd a b,Real.norm_eq_abs];exact hD2 a b) using 1 <;> ring
  have hI1 := norm_fderiv_scalar_inverse_le f y (hf.differentiableAt (by simp)) hpos (3*D1*f y) hN1
  have hI2 := norm_second_fderiv_scalar_inverse_le f y hf hpos (3*D1*f y) (9*D2*f y)
    (by positivity) (by positivity) hN1 hN2
  constructor
  · intro i
    exact ((coordDeriv_abs_le _ y i).trans hI1).trans_eq (by field_simp [hpos.ne'] <;> ring)
  · intro i j
    have hInv : ContDiffAt ℝ ∞ (fun x => (f x)⁻¹) y := hf.inv hpos.ne'
    have hi := (hInv.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
    rw [coordinate_second_derivative _ y hi i j]
    have ht := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ (fun x => (f x)⁻¹)) y) (axis i) (axis j)
    rw [norm_axis,norm_axis,mul_one,mul_one,Real.norm_eq_abs] at ht
    exact (ht.trans hI2).trans_eq (by field_simp [hpos.ne'] <;> ring)

end ShrinkingSpheres
