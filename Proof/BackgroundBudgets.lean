import Proof.InverseMetricDerivative

noncomputable section
set_option autoImplicit false
open Set
namespace ShrinkingSpheres

lemma Background.reference_jet_bound {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (j : Fin (m+1)) {y : X} (hy : y ∈ Ω) (i l : I) :
    ‖iteratedFDeriv ℝ j.val (fun x => g x i l) y‖ ≤ M j :=
  h.2.2.2.2.1 g (by simp) j i l y hy

lemma Background.reference_entry_bound {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    {y : X} (hy : y ∈ Ω) (i l : I) : |g y i l| ≤ M 0 := by
  have hh := h.reference_jet_bound 0 hy i l
  change ‖iteratedFDeriv ℝ 0 (fun x => g x i l) y‖ ≤ M 0 at hh
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hh

lemma Background.reference_fderiv_bound {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e) (hm : 1 ≤ m)
    {y : X} (hy : y ∈ Ω) (i l : I) :
    ‖fderiv ℝ (fun x => g x i l) y‖ ≤ M ⟨1,by omega⟩ := by
  simpa only [norm_iteratedFDeriv_one] using h.reference_jet_bound ⟨1,by omega⟩ hy i l

lemma Background.reference_second_fderiv_bound {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e) (hm : 2 ≤ m)
    {y : X} (hy : y ∈ Ω) (i l : I) :
    ‖fderiv ℝ (fderiv ℝ (fun x => g x i l)) y‖ ≤ M ⟨2,by omega⟩ := by
  have hh := h.reference_jet_bound ⟨2,by omega⟩ hy i l
  rwa [← norm_iteratedFDeriv_fderiv (n:=1), norm_iteratedFDeriv_one] at hh

lemma coordDeriv_abs_le (f : X → ℝ) (y : X) (i : I) :
    |coordDeriv i f y| ≤ ‖fderiv ℝ f y‖ := by
  simpa only [coordDeriv, norm_axis, mul_one, Real.norm_eq_abs] using (fderiv ℝ f y).le_opNorm (axis i)

/-- A dimension-only coordinate bound for the actual Christoffel symbols. -/
theorem Elliptic.christoffel_entry_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M₁ : ℝ) (hM : 0 ≤ M₁) (hD : ∀ i j, ‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁) (k i j : I) :
    |christoffel g y k i j| ≤ 9*K*M₁ := by
  have hcoord (a b c : I) : |coordDeriv a (fun x => g x b c) y| ≤ M₁ :=
    (coordDeriv_abs_le _ y a).trans (hD b c)
  have hsum (l : I) : |coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y -
      coordDeriv l (fun x => g x i j) y| ≤ 3*M₁ := by
    calc
      _ ≤ |coordDeriv i (fun x => g x l j) y + coordDeriv j (fun x => g x i l) y| +
          |coordDeriv l (fun x => g x i j) y| := abs_sub _ _
      _ ≤ (|coordDeriv i (fun x => g x l j) y| + |coordDeriv j (fun x => g x i l) y|) +
          |coordDeriv l (fun x => g x i j) y| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 3*M₁ := by linarith only [hcoord i l j, hcoord j i l, hcoord l i j]
  have hterm (l : I) : |(g y)⁻¹ k l * (coordDeriv i (fun x => g x l j) y +
      coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y)| ≤ K*(3*M₁) := by
    rw [abs_mul]
    exact mul_le_mul (h.inverse_entry_bound hK hy k l) (hsum l) (abs_nonneg _) hK.le
  have htotal : |∑ l, (g y)⁻¹ k l * (coordDeriv i (fun x => g x l j) y +
      coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y)| ≤ 9*K*M₁ := by
    calc
      _ ≤ ∑ l, |(g y)⁻¹ k l * (coordDeriv i (fun x => g x l j) y +
          coordDeriv j (fun x => g x i l) y - coordDeriv l (fun x => g x i j) y)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : I, K*(3*M₁) := Finset.sum_le_sum (fun l _ => hterm l)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [christoffel, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpos : 0 ≤ 9*K*M₁ := by positivity
  linarith

end ShrinkingSpheres
