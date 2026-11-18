import Proof.InverseMetricBounds

noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The inverse derivative is obtained by differentiating the actual matrix inverse
    identity on the coordinate domain, then multiplying by the same inverse. -/
theorem fderiv_inverse_metric_entries {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a : X) (i j : I) :
    fderiv ℝ (fun x => (g x)⁻¹ i j) y a =
      -(∑ k, ∑ l, (g y)⁻¹ i k * fderiv ℝ (fun x => g x k l) y a * (g y)⁻¹ l j) := by
  let D : Mat := fun k l => fderiv ℝ (fun x => g x k l) y a
  let H : Mat := fun k l => fderiv ℝ (fun x => (g x)⁻¹ k l) y a
  have hG (k l : I) := (((h.1 k l).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hH (k l : I) := (((h.contDiffOn_inverse_entry hK k l).contDiffAt
    (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hmat : H * g y + (g y)⁻¹ * D = 0 := by
    ext k l
    have hconst : (fun x => ∑ t, (g x)⁻¹ k t * g x t l) =ᶠ[nhds y]
        (fun _ => if k = l then (1 : ℝ) else 0) := by
      filter_upwards [hΩ.mem_nhds hy] with x hx
      simpa only [Matrix.mul_apply, Matrix.one_apply] using
        congrArg (fun M : Mat => M k l)
          (Matrix.nonsing_inv_mul (g x) (isUnit_iff_ne_zero.mpr (h.posDef hK hx).det_pos.ne'))
    have hzero := congrArg (fun T : X →L[ℝ] ℝ => T a) hconst.fderiv_eq
    have hsum := HasFDerivAt.sum (u:=Finset.univ) (fun t _ => (hH k t).mul (hG t l))
    have hfun : (fun x => ∑ t, (g x)⁻¹ k t * g x t l) =
        ∑ t, (fun x => (g x)⁻¹ k t) * (fun x => g x t l) := by
      funext x
      rfl
    rw [hfun, hsum.fderiv] at hzero
    simp only [_root_.sum_apply, ContinuousLinearMap.add_apply, _root_.smul_apply,
      smul_eq_mul, fderiv_const_apply, zero_apply] at hzero
    change (∑ t, fderiv ℝ (fun x => (g x)⁻¹ k t) y a * g y t l) +
      (∑ t, (g y)⁻¹ k t * fderiv ℝ (fun x => g x t l) y a) = 0
    simpa only [Finset.sum_add_distrib, mul_comm, add_comm] using hzero
  have hmul := congrArg (fun M : Mat => M * (g y)⁻¹) hmat
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv (g y)
    (isUnit_iff_ne_zero.mpr (h.posDef hK hy).det_pos.ne'), Matrix.mul_one, Matrix.zero_mul] at hmul
  have hij := congrArg (fun M : Mat => M i j) hmul
  simp only [Matrix.add_apply, Matrix.zero_apply] at hij
  change H i j = _
  have heq : H i j = -(((g y)⁻¹ * D * (g y)⁻¹) i j) := by linarith only [hij]
  rw [heq]
  congr 1
  change (∑ l, (∑ k, (g y)⁻¹ i k * fderiv ℝ (fun x => g x k l) y a) * (g y)⁻¹ l j) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A coordinate derivative of the inverse uses only ellipticity and the first derivative
    budget. The estimate is valid in every ambient direction. -/
theorem Elliptic.inverse_derivative_entry_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M₁ : ℝ) (hM : 0 ≤ M₁) (hD : ∀ i j, ‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (a : X) (i j : I) :
    |fderiv ℝ (fun x => (g x)⁻¹ i j) y a| ≤ 9*K^2*M₁*‖a‖ := by
  rw [fderiv_inverse_metric_entries hΩ h hK hy, abs_neg]
  have hh (k l : I) : |(g y)⁻¹ i k * fderiv ℝ (fun x => g x k l) y a * (g y)⁻¹ l j| ≤
      K*(M₁*‖a‖)*K := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (h.inverse_entry_bound hK hy i k)
      (((fderiv ℝ (fun x => g x k l) y).le_opNorm a).trans
        (mul_le_mul_of_nonneg_right (hD k l) (norm_nonneg a))) (abs_nonneg _) hK.le)
      (h.inverse_entry_bound hK hy l j) (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ k, ∑ l, |(g y)⁻¹ i k * fderiv ℝ (fun x => g x k l) y a * (g y)⁻¹ l j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _k : I, ∑ _l : I, K*(M₁*‖a‖)*K := Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hh k l))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end ShrinkingSpheres
