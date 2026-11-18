import Proof.CoordinateSecondJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma principal_second_le_inverse_add {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K) {r : X → ℝ} {ε : ℝ} (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M₁)
    (hD₂ : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M₂) (i j k l : I) :
    |coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y| ≤ 162*K^3*M₁^2+9*K^2*M₂+ε*r y := by
  have heq : coordDeriv l (coordDeriv k (fun x => (principal g g₂ x-(g x)⁻¹) i j)) y =
      coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y-
        coordDeriv l (coordDeriv k (fun x => (g x)⁻¹ i j)) y := by
    simpa only [Matrix.sub_apply] using coordinate_second_sub hY
      (contDiffOn_principal_entry h h₂ hK i j) (h.contDiffOn_inverse_entry hK i j) hy l k
  have hsmall := hs.coordinate_second_component_bound hY h h₂ hK hy l k i j
  rw [heq] at hsmall
  have hinv := h.inverse_second_coordinate_bound hY hK hy M₁ M₂ hM₁ hM₂ hD hD₂ i j k l
  have he : coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y =
      coordDeriv l (coordDeriv k (fun x => (g x)⁻¹ i j)) y+
      (coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y-
        coordDeriv l (coordDeriv k (fun x => (g x)⁻¹ i j)) y) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hinv hsmall)

/-- The actual second coordinate coefficient of rQ has the manuscript's O(epsilon)
    weight, uniformly over every admitted radius and second-metric perturbation. -/
theorem principal_radius_second_weight {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M₁)
    (hD₂ : ∀ a b,‖fderiv ℝ (fderiv ℝ (fun x => g x a b)) y‖ ≤ M₂) (i j k l : I) :
    |coordDeriv l (coordDeriv k (fun x => r x*principal g g₂ x i j)) y| ≤
      ((K^2+9*K^2*|Cj 2|+27*K^2*M₁)*(K+1)+2*K*(9*K^2*M₁+1)+
        (162*K^3*M₁^2+9*K^2*M₂+1))*ε := by
  have hr := (hp.2 y hy).1
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hb : 1 ≤ beta g r y := hf.trans (hp.2 y hy).2.1
  have hβ : 0 < beta g r y := zero_lt_one.trans_le hb
  obtain ⟨hrr,hrb,hrε⟩ := radius_bounds (r y) (beta g r y) (beta g r y) ε hr.le hb le_rfl (hs y hy).2
  have her : ε*r y ≤ 1 := (mul_le_mul_of_nonneg_right hε1 hr.le).trans (by simpa using hrε.trans hε1)
  have hQ : |principal g g₂ y i j| ≤ K+1 := (principal_entry_le_inverse_add h hKpos hs hy i j).trans (by linarith)
  have hDQ (a : I) : |coordDeriv a (fun x => principal g g₂ x i j) y| ≤ 9*K^2*M₁+1 :=
    (principal_derivative_le_inverse_add hY h h₂ hKpos hs hy M₁ hM₁ hD i j a).trans (by linarith)
  have hD₂Q : |coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y| ≤ 162*K^3*M₁^2+9*K^2*M₂+1 :=
    (principal_second_le_inverse_add hY h h₂ hKpos hs hy M₁ M₂ hM₁ hM₂ hD hD₂ i j k l).trans (by linarith)
  have hD₂r := hp.coordinate_radius_second_bound hY h hK e hframe hf (show 0 ≤ 9*K*M₁ by positivity) hy
    (fun a b c => h.christoffel_entry_bound hKpos hy M₁ hM₁ hD a b c) l k
  have hD₂r' : |coordDeriv l (coordDeriv k r) y| ≤ (K^2+9*K^2*|Cj 2|+27*K^2*M₁)*ε := by
    have ht := mul_le_mul_of_nonneg_left (hs y hy).2 (show 0 ≤ K^2+9*K^2*|Cj 2|+27*K^2*M₁ by positivity)
    nlinarith only [hD₂r,ht]
  have hDr (a : I) : |coordDeriv a r y| ≤ K*ε := by
    have hR := hp.coordinate_radius_first_bound hY h hK e hframe hy a
    have ht := mul_le_mul_of_nonneg_left hrb (zero_le_one.trans hK)
    have hbε : ε/beta g r y ≤ ε := (div_le_iff₀ hβ).mpr (by nlinarith)
    have ht2 := mul_le_mul_of_nonneg_left hbε (zero_le_one.trans hK)
    nlinarith only [hR,ht,ht2]
  rw [coordinate_second_mul hY hp.1 (contDiffOn_principal_entry h h₂ hKpos i j) hy l k]
  have h1 := mul_le_mul hD₂r' hQ (abs_nonneg _) (show 0 ≤ (K^2+9*K^2*|Cj 2|+27*K^2*M₁)*ε by positivity)
  have h2 := mul_le_mul (hDr k) (hDQ l) (abs_nonneg _) (show 0 ≤ K*ε by positivity)
  have h3 := mul_le_mul (hDr l) (hDQ k) (abs_nonneg _) (show 0 ≤ K*ε by positivity)
  have h4 := mul_le_mul hrε hD₂Q (abs_nonneg _) hε
  have ha : |coordDeriv l (coordDeriv k r) y*principal g g₂ y i j+
      coordDeriv k r y*coordDeriv l (fun x => principal g g₂ x i j) y+
      coordDeriv l r y*coordDeriv k (fun x => principal g g₂ x i j) y+
      r y*coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y| ≤
      |coordDeriv l (coordDeriv k r) y*principal g g₂ y i j|+
      |coordDeriv k r y*coordDeriv l (fun x => principal g g₂ x i j) y|+
      |coordDeriv l r y*coordDeriv k (fun x => principal g g₂ x i j) y|+
      |r y*coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y| := by
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl) |>.trans
      (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl)
  simp only [← abs_mul] at h1 h2 h3
  have h4' : |r y*coordDeriv l (coordDeriv k (fun x => principal g g₂ x i j)) y| ≤ ε*(162*K^3*M₁^2+9*K^2*M₂+1) := by
    rw [abs_mul,abs_of_pos hr]
    exact h4
  nlinarith only [ha,h1,h2,h3,h4']

end ShrinkingSpheres
