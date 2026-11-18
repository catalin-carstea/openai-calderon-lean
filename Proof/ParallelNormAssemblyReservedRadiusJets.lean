import Proof.ScalarRelativeInverseJets
import Proof.AdmissibleRadiusSmallJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- Radius normalization uses relative first/second inverse-radius jets
from the original profile. Constants precede every profile and frame. -/
theorem uniform_radius_inverse_two_jet_weights {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      (∀ i : I,|coordDeriv i (fun x => (d.radius x)⁻¹) y| ≤
        C*beta d.γ d.radius y/(d.radius y)) ∧
      (∀ i j : I,|coordDeriv i (coordDeriv j (fun x => (d.radius x)⁻¹)) y| ≤
        C*(beta d.γ d.radius y)^2/(d.radius y)) := by
  let G := 9*K*|M ⟨1,by omega⟩|
  let R2 := K^2+9*K^2*|Cj 2|+3*G*K
  let C := 3*K+(9*R2+18*K^2)
  have hK0 := zero_le_one.trans hK
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hR2 : 0 ≤ R2 := by dsimp only [R2];positivity
  have hC1 : 3*K ≤ C := by dsimp only [C];linarith only [hR2,sq_nonneg K]
  have hC2 : 9*R2+18*K^2 ≤ C := by dsimp only [C];linarith only [hK0]
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor hf ε d hd y hy
  let β := beta d.γ d.radius y
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (x : X) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hΓ (a b c : I) : |christoffel d.γ y a b c| ≤ G :=
    hg.christoffel_entry_bound (zero_lt_one.trans_le hK) hy |M ⟨1,by omega⟩| (abs_nonneg _)
      (fun i j => (hd.1.reference_fderiv_bound hm (hSub hy) i j).trans (le_abs_self _)) a b c
  have hR1 (i : I) : |coordDeriv i d.radius y| ≤ (K*β)*d.radius y := by
    exact (hd.2.2.2.2.1.coordinate_radius_first_bound hY hg hK d.frame he hy i).trans_eq (by ring)
  have hR2N (i j : I) : |coordDeriv i (coordDeriv j d.radius) y| ≤ (R2*β^2)*d.radius y := by
    exact (hd.2.2.2.2.1.coordinate_radius_second_bound hY hg hK d.frame he hf hG hy hΓ i j).trans_eq (by ring)
  obtain ⟨h1,h2⟩ := scalar_inverse_relative_coordinate_jets d.radius y
    (hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)) hr (K*β) (R2*β^2)
    (mul_nonneg hK0 hβ) (mul_nonneg hR2 (sq_nonneg _)) hR1 hR2N
  constructor
  · intro i
    calc
      _ ≤ (3*(K*β))*(d.radius y)⁻¹ := h1 i
      _ = (3*K)*β/d.radius y := by ring
      _ ≤ C*β/d.radius y := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hβ) hr.le
  · intro i j
    calc
      _ ≤ (9*(R2*β^2)+18*(K*β)^2)*(d.radius y)⁻¹ := h2 i j
      _ = (9*R2+18*K^2)*β^2/d.radius y := by ring
      _ ≤ C*β^2/d.radius y := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (sq_nonneg β)) hr.le

/-- Normalizing an r-scaled angular family preserves the required fixed,
beta and beta-squared jet scales, on the SAME four product-rule values. -/
lemma radius_normalized_two_jet_norms {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F Si Sj T : E) (w wi wj wij C0 C1 C2 CI r β : ℝ)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hCI : 0 ≤ CI)
    (hr : 0 < r) (hβ : 0 ≤ β)
    (hw : |w| ≤ r⁻¹) (hwi : |wi| ≤ CI*β/r) (hwj : |wj| ≤ CI*β/r)
    (hwij : |wij| ≤ CI*β^2/r)
    (hF : ‖F‖ ≤ C0*r) (hSi : ‖Si‖ ≤ C1*r*β) (hSj : ‖Sj‖ ≤ C1*r*β)
    (hT : ‖T‖ ≤ C2*r*β^2) :
    ‖w • F‖ ≤ C0 ∧
    ‖w • Si+wi • F‖ ≤ (C1+CI*C0)*β ∧
    ‖(w • T+wj • Si)+(wi • Sj+wij • F)‖ ≤ (C2+2*CI*C1+CI*C0)*β^2 := by
  have h0 : ‖w • F‖ ≤ r⁻¹*(C0*r) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hF (norm_nonneg _) (inv_nonneg.mpr hr.le)
  have h1 : ‖w • Si‖ ≤ r⁻¹*(C1*r*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hSi (norm_nonneg _) (inv_nonneg.mpr hr.le)
  have h2 : ‖wi • F‖ ≤ (CI*β/r)*(C0*r) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwi hF (norm_nonneg _) (by positivity)
  have h20 : ‖w • T‖ ≤ r⁻¹*(C2*r*β^2) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hw hT (norm_nonneg _) (inv_nonneg.mpr hr.le)
  have h21 : ‖wj • Si‖ ≤ (CI*β/r)*(C1*r*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwj hSi (norm_nonneg _) (by positivity)
  have h22 : ‖wi • Sj‖ ≤ (CI*β/r)*(C1*r*β) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwi hSj (norm_nonneg _) (by positivity)
  have h23 : ‖wij • F‖ ≤ (CI*β^2/r)*(C0*r) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hwij hF (norm_nonneg _) (by positivity)
  refine ⟨h0.trans_eq (by field_simp <;> ring),?_,?_⟩
  · exact ((norm_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by field_simp <;> ring)
  · exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))).trans
      ((add_le_add (add_le_add h20 h21) (add_le_add h22 h23)).trans_eq (by field_simp <;> ring))

end ShrinkingSpheres.ParallelEnergy
