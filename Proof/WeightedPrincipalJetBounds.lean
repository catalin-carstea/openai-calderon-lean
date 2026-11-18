import Proof.DensityCoefficientJets
import Proof.PrincipalSecondCoefficientWeight

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Scalar coefficient calculus for a positive density and an arbitrary beta-weighted
    principal entry. It is local on the actual smooth coordinate domain. -/
theorem weighted_principal_entry_two_jets {Y : Set X} (hY : IsOpen Y) {μ a : X → ℝ}
    (hμ : ContDiffOn ℝ ∞ μ Y) (ha : ContDiffOn ℝ ∞ a Y) {y : X} (hy : y ∈ Y)
    {β ε A₀ A₁ A₂ D₁ D₂ : ℝ} (hβ : 1 ≤ β) (hε : 0 ≤ ε) (hμpos : 0 < μ y)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hμ₁ : ∀ k,|coordDeriv k μ y| ≤ D₁*μ y)
    (hμ₂ : ∀ k l,|coordDeriv l (coordDeriv k μ) y| ≤ D₂*μ y)
    (ha₀ : |a y| ≤ A₀*ε/β^2) (ha₁ : ∀ k,|coordDeriv k a y| ≤ A₁*ε/β)
    (ha₂ : ∀ k l,|coordDeriv l (coordDeriv k a) y| ≤ A₂*ε) (k l : I) :
    |coordDeriv k (fun x => μ x*a x) y| ≤ μ y*(D₁*A₀+A₁)*ε/β ∧
    |coordDeriv l (coordDeriv k (fun x => μ x*a x)) y| ≤ μ y*(D₂*A₀+2*D₁*A₁+A₂)*ε := by
  have hb : 0 < β := zero_lt_one.trans_le hβ
  have hbb : β ≤ β^2 := by nlinarith
  have ha₀β : |a y| ≤ A₀*ε/β := by
    apply (le_div_iff₀ hb).mpr
    have ht := (le_div_iff₀ (sq_pos_of_pos hb)).mp ha₀
    exact (mul_le_mul_of_nonneg_left hbb (abs_nonneg _)).trans ht
  have hβ1 : A₀*ε/β ≤ A₀*ε := (div_le_iff₀ hb).mpr (by nlinarith [mul_nonneg hA₀ hε])
  have ha₀ε := ha₀β.trans hβ1
  have ha₁ε (i : I) : |coordDeriv i a y| ≤ A₁*ε := (ha₁ i).trans ((div_le_iff₀ hb).mpr (by nlinarith [mul_nonneg hA₁ hε]))
  constructor
  · have hdμ := (hμ.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hda := (ha.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have heq : coordDeriv k (fun x => μ x*a x) y = coordDeriv k μ y*a y+μ y*coordDeriv k a y := by
      unfold coordDeriv
      rw [(hdμ.hasFDerivAt.fun_mul hda.hasFDerivAt).fderiv]
      simp only [add_apply,smul_apply,smul_eq_mul]
      ring
    rw [heq]
    have h1 := mul_le_mul (hμ₁ k) ha₀β (abs_nonneg _) (mul_nonneg hD₁ hμpos.le)
    have h2 := mul_le_mul_of_nonneg_left (ha₁ k) hμpos.le
    have h2' : |μ y*coordDeriv k a y| ≤ μ y*(A₁*ε/β) := by rw [abs_mul,abs_of_pos hμpos]; exact h2
    have h1' : |coordDeriv k μ y*a y| ≤ D₁*μ y*(A₀*ε/β) := by rw [abs_mul]; exact h1
    have ht := (abs_add_le _ _).trans (add_le_add h1' h2')
    convert ht using 1 <;> ring
  · rw [coordinate_second_mul hY hμ ha hy l k]
    have h1 := mul_le_mul (hμ₂ k l) ha₀ε (abs_nonneg _) (mul_nonneg hD₂ hμpos.le)
    have h2 := mul_le_mul (hμ₁ k) (ha₁ε l) (abs_nonneg _) (mul_nonneg hD₁ hμpos.le)
    have h3 := mul_le_mul (hμ₁ l) (ha₁ε k) (abs_nonneg _) (mul_nonneg hD₁ hμpos.le)
    have h4 := mul_le_mul_of_nonneg_left (ha₂ k l) hμpos.le
    have h4' : |μ y*coordDeriv l (coordDeriv k a) y| ≤ μ y*(A₂*ε) := by rw [abs_mul,abs_of_pos hμpos]; exact h4
    simp only [← abs_mul] at h1 h2 h3
    have hadd (x z u v : ℝ) : |x+z+u+v| ≤ |x|+|z|+|u|+|v| :=
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
        (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl)
    have ht := hadd (coordDeriv l (coordDeriv k μ) y*a y) (coordDeriv k μ y*coordDeriv l a y)
      (coordDeriv l μ y*coordDeriv k a y) (μ y*coordDeriv l (coordDeriv k a) y)
    nlinarith only [h1,h2,h3,h4',ht]

end ShrinkingSpheres
