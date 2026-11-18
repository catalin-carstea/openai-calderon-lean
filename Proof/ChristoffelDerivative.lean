import Proof.BackgroundBudgets

noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma fderiv_coordDeriv_apply (f : X → ℝ) (y : X) (i : I)
    (hD : DifferentiableAt ℝ (fderiv ℝ f) y) (a : X) :
    fderiv ℝ (coordDeriv i f) y a = fderiv ℝ (fderiv ℝ f) y a (axis i) := by
  have hh := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (axis i) y)
  change HasFDerivAt (coordDeriv i f) _ y at hh
  rw [hh.fderiv]
  simp

lemma fderiv_coordDeriv_abs_le (f : X → ℝ) (y : X) (i : I)
    (hD : DifferentiableAt ℝ (fderiv ℝ f) y) (M₂ : ℝ)
    (hM : ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M₂) (a : X) :
    |fderiv ℝ (coordDeriv i f) y a| ≤ M₂*‖a‖ := by
  rw [fderiv_coordDeriv_apply f y i hD a]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) y a‖ := by
      simpa only [norm_axis, mul_one, Real.norm_eq_abs] using
        (fderiv ℝ (fderiv ℝ f) y a).le_opNorm (axis i)
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖*‖a‖ := (fderiv ℝ (fderiv ℝ f) y).le_opNorm a
    _ ≤ M₂*‖a‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg a)

lemma Elliptic.differentiableAt_fderiv_entry {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) {y : X} (hy : y ∈ Ω) (i j : I) :
    DifferentiableAt ℝ (fderiv ℝ (fun x => g x i j)) y :=
  ((((h.1 i j).fderiv_of_isOpen (m:=∞) hΩ (by simp)).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))

lemma Elliptic.differentiableAt_coordDeriv_entry {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) {y : X} (hy : y ∈ Ω) (a i j : I) :
    DifferentiableAt ℝ (coordDeriv a (fun x => g x i j)) y :=
  ((h.differentiableAt_fderiv_entry hΩ hy i j).clm_apply (differentiableAt_const (axis a)))

/-- Differentiating the coordinate Christoffel formula in an arbitrary ambient direction. -/
theorem fderiv_christoffel_entries {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (a : X) (k i j : I) :
    fderiv ℝ (fun x => christoffel g x k i j) y a =
      (∑ l, (fderiv ℝ (fun x => (g x)⁻¹ k l) y a *
        (coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y) +
        (g y)⁻¹ k l * (fderiv ℝ (coordDeriv i (fun x => g x l j)) y a +
          fderiv ℝ (coordDeriv j (fun x => g x i l)) y a - fderiv ℝ (coordDeriv l (fun x => g x i j)) y a))) / 2 := by
  have hH (l : I) := (((h.contDiffOn_inverse_entry hK k l).contDiffAt
    (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hD (a b c : I) := (h.differentiableAt_coordDeriv_entry hΩ hy a b c).hasFDerivAt
  have hsum := (HasFDerivAt.sum (u:=Finset.univ) (fun l _ =>
    (hH l).mul (((hD i l j).add (hD j i l)).sub (hD l i j)))).mul (hasFDerivAt_const ((2 : ℝ)⁻¹) y)
  have hfun : (fun x => christoffel g x k i j) =
      (∑ l, ((fun x => (g x)⁻¹ k l) *
        ((coordDeriv i (fun x => g x l j) + coordDeriv j (fun x => g x i l)) -
          coordDeriv l (fun x => g x i j)))) * (fun _ => (2 : ℝ)⁻¹) := by
    funext x
    rfl
  rw [hfun, hsum.fderiv]
  simp only [_root_.sum_apply, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    Pi.mul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, smul_zero, zero_add, zero_apply, div_eq_mul_inv]
  rw [mul_comm ((2 : ℝ)⁻¹)]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- A dimension-only derivative bound for the actual Christoffel symbols. -/
theorem Elliptic.christoffel_derivative_entry_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ i j, ‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j, ‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂) (a : X) (k i j : I) :
    |fderiv ℝ (fun x => christoffel g x k i j) y a| ≤ (81*K^2*M₁^2+9*K*M₂)*‖a‖ := by
  have hcoord (a b c : I) : |coordDeriv a (fun x => g x b c) y| ≤ M₁ :=
    (coordDeriv_abs_le _ y a).trans (hD b c)
  have hcoordD (i b c : I) : |fderiv ℝ (coordDeriv i (fun x => g x b c)) y a| ≤ M₂*‖a‖ :=
    fderiv_coordDeriv_abs_le _ y i (h.differentiableAt_fderiv_entry hΩ hy b c) M₂ (hD₂ b c) a
  have habs3 (u v w B : ℝ) (hu : |u| ≤ B) (hv : |v| ≤ B) (hw : |w| ≤ B) : |u+v-w| ≤ 3*B := by
    have hh := (abs_sub (u+v) w).trans (add_le_add (abs_add_le u v) le_rfl)
    linarith
  have hterm (l : I) :
      |fderiv ℝ (fun x => (g x)⁻¹ k l) y a *
        (coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y) +
        (g y)⁻¹ k l * (fderiv ℝ (coordDeriv i (fun x => g x l j)) y a +
          fderiv ℝ (coordDeriv j (fun x => g x i l)) y a - fderiv ℝ (coordDeriv l (fun x => g x i j)) y a)| ≤
      (27*K^2*M₁^2+3*K*M₂)*‖a‖ := by
    have hS := habs3 _ _ _ M₁ (hcoord i l j) (hcoord j i l) (hcoord l i j)
    have hSD := habs3 _ _ _ (M₂*‖a‖) (hcoordD i l j) (hcoordD j i l) (hcoordD l i j)
    calc
      _ ≤ |fderiv ℝ (fun x => (g x)⁻¹ k l) y a *
          (coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y)| +
          |(g y)⁻¹ k l * (fderiv ℝ (coordDeriv i (fun x => g x l j)) y a +
            fderiv ℝ (coordDeriv j (fun x => g x i l)) y a - fderiv ℝ (coordDeriv l (fun x => g x i j)) y a)| := abs_add_le _ _
      _ ≤ (9*K^2*M₁*‖a‖)*(3*M₁)+K*(3*(M₂*‖a‖)) := by
        rw [abs_mul,abs_mul]
        exact add_le_add
          (mul_le_mul (h.inverse_derivative_entry_bound hΩ hK hy M₁ hM₁ hD a k l) hS (abs_nonneg _) (by positivity))
          (mul_le_mul (h.inverse_entry_bound hK hy k l) hSD (abs_nonneg _) hK.le)
      _ = _ := by ring
  have htotal := (Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun l =>
      fderiv ℝ (fun x => (g x)⁻¹ k l) y a *
        (coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y) +
        (g y)⁻¹ k l * (fderiv ℝ (coordDeriv i (fun x => g x l j)) y a +
          fderiv ℝ (coordDeriv j (fun x => g x i l)) y a - fderiv ℝ (coordDeriv l (fun x => g x i j)) y a))).trans
    (Finset.sum_le_sum (fun l _ => hterm l))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  rw [fderiv_christoffel_entries hΩ h hK hy, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpos : 0 ≤ (81*K^2*M₁^2+9*K*M₂)*‖a‖ := by positivity
  nlinarith only [htotal,hpos]

end ShrinkingSpheres
