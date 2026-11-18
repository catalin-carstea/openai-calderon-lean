import Proof.ProfileRadiusSecondJet
import Proof.PhysicalTraceRegularity
import Proof.Smallness
import Proof.BackgroundBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma Small.coordinate_component_bound {Y : Set X} {g g₂ : MetricField} {r : X → ℝ} {ε : ℝ}
    (hs : Small Y g g₂ r ε) {y : X} (hy : y ∈ Y) (i a b : I) :
    |coordDeriv i (fun x => (principal g g₂ x-(g x)⁻¹) a b) y| ≤ ε*r y := by
  fin_cases i
  · change |coordDeriv (0 : I) (fun x => (principal g g₂ x-(g x)⁻¹) a b) y| ≤ ε*r y
    exact hs.partial_bound hy 1 0 0 (by decide) a b
  · change |coordDeriv (1 : I) (fun x => (principal g g₂ x-(g x)⁻¹) a b) y| ≤ ε*r y
    exact hs.partial_bound hy 0 1 0 (by decide) a b
  · change |coordDeriv (2 : I) (fun x => (principal g g₂ x-(g x)⁻¹) a b) y| ≤ ε*r y
    exact hs.partial_bound hy 0 0 1 (by decide) a b


lemma principal_entry_le_inverse_add {Y : Set X} {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {r : X → ℝ} {ε : ℝ} (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (i j : I) : |principal g g₂ y i j| ≤ K+ε*r y := by
  have heq : principal g g₂ y i j = (g y)⁻¹ i j+(principal g g₂ y-(g y)⁻¹) i j := by simp only [Matrix.sub_apply]; ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (h.inverse_entry_bound hK hy i j) (hs.component_bound hy i j))

lemma principal_derivative_le_inverse_add {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K) {r : X → ℝ} {ε : ℝ} (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M₁ : ℝ) (hM : 0 ≤ M₁)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M₁) (i j k : I) :
    |coordDeriv k (fun x => principal g g₂ x i j) y| ≤ 9*K^2*M₁+ε*r y := by
  have hq := ((contDiffOn_principal_entry h h₂ hK i j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hi := ((h.contDiffOn_inverse_entry hK i j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have heq : coordDeriv k (fun x => (principal g g₂ x-(g x)⁻¹) i j) y =
      coordDeriv k (fun x => principal g g₂ x i j) y-coordDeriv k (fun x => (g x)⁻¹ i j) y := by
    simp only [Matrix.sub_apply,coordDeriv]
    rw [fderiv_fun_sub hq hi]
    rfl
  have hinv := h.inverse_derivative_entry_bound hY hK hy M₁ hM hD (axis k) i j
  rw [norm_axis,mul_one] at hinv
  change |coordDeriv k (fun x => (g x)⁻¹ i j) y| ≤ 9*K^2*M₁ at hinv
  have hsmall := hs.coordinate_component_bound hy k i j
  rw [heq] at hsmall
  have he : coordDeriv k (fun x => principal g g₂ x i j) y =
      coordDeriv k (fun x => (g x)⁻¹ i j) y+
      (coordDeriv k (fun x => principal g g₂ x i j) y-coordDeriv k (fun x => (g x)⁻¹ i j) y) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hinv hsmall)

/-- Zeroth and first coordinate coefficient weights for the actual scalar principal part
    rQ. Constants use only ellipticity, one background derivative and the admitted profile. -/
theorem principal_radius_zero_first_weights {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 1 ≤ K) (e : Frame)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hf : 1 ≤ floor)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : Small Y g g₂ r ε)
    {y : X} (hy : y ∈ Y) (M₁ : ℝ) (hM : 0 ≤ M₁)
    (hD : ∀ a b,‖fderiv ℝ (fun x => g x a b) y‖ ≤ M₁) (i j k : I) :
    |r y*principal g g₂ y i j| ≤ (K+1)*ε/(beta g r y)^2 ∧
    |coordDeriv k (fun x => r x*principal g g₂ x i j) y| ≤
      (K*(K+1)+9*K^2*M₁+1)*ε/beta g r y := by
  have hr := (hp.2 y hy).1
  have hb : 1 ≤ beta g r y := hf.trans (hp.2 y hy).2.1
  have hβ : 0 < beta g r y := zero_lt_one.trans_le hb
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hr1 : r y ≤ 1 := (radius_bounds (r y) (beta g r y) floor ε hr.le hf (hp.2 y hy).2.1 (hs y hy).2).2.2.trans hε1
  have her : ε*r y ≤ 1 := (mul_le_mul_of_nonneg_right hε1 hr.le).trans (by simpa using hr1)
  have hQ : |principal g g₂ y i j| ≤ K+1 := (principal_entry_le_inverse_add h hKpos hs hy i j).trans (by linarith)
  have hDQ : |coordDeriv k (fun x => principal g g₂ x i j) y| ≤ 9*K^2*M₁+1 :=
    (principal_derivative_le_inverse_add hY h h₂ hKpos hs hy M₁ hM hD i j k).trans (by linarith)
  have hDr := hp.coordinate_radius_first_bound hY h hK e hframe hy k
  have hsmall := (hs y hy).2
  constructor
  · rw [abs_mul,abs_of_pos hr]
    apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
    have ht := mul_le_mul_of_nonneg_right hQ (mul_nonneg hr.le (sq_nonneg (beta g r y)))
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ K+1 by positivity)
    nlinarith only [ht,hh]
  · have hdr := (hp.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hdq := ((contDiffOn_principal_entry h h₂ hKpos i j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have heq : coordDeriv k (fun x => r x*principal g g₂ x i j) y =
        coordDeriv k r y*principal g g₂ y i j+r y*coordDeriv k (fun x => principal g g₂ x i j) y := by
      unfold coordDeriv
      rw [(hdr.hasFDerivAt.fun_mul hdq.hasFDerivAt).fderiv]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      ring
    rw [heq]
    have hp1 : |coordDeriv k r y*principal g g₂ y i j| ≤ (K*r y*beta g r y)*(K+1) := by
      rw [abs_mul]
      exact mul_le_mul hDr hQ (abs_nonneg _) (by positivity)
    have hp2 : |r y*coordDeriv k (fun x => principal g g₂ x i j) y| ≤ r y*(9*K^2*M₁+1) := by
      rw [abs_mul,abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hDQ hr.le
    have hbound := (abs_add_le _ _).trans (add_le_add hp1 hp2)
    have hbterm := mul_le_mul_of_nonneg_left hb (show 0 ≤ r y*(9*K^2*M₁+1) by positivity)
    apply (le_div_iff₀ hβ).mpr
    have ht := mul_le_mul_of_nonneg_right hbound hβ.le
    have hsC := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ K*(K+1)+9*K^2*M₁+1 by positivity)
    have hbterm2 := mul_le_mul_of_nonneg_right hbterm hβ.le
    nlinarith only [ht,hbterm2,hsC]

end ShrinkingSpheres
