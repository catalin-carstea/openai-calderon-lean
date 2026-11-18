import Proof.InverseMetricThirdDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The third Christoffel jet needs only four background metric jets.
    The generous dimension constants avoid any dependence on a chosen frame. -/
theorem Elliptic.christoffel_third_fderiv_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M₁ M₂ M₃ M₄ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (hD : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂)
    (hD₃ : ∀ i j,‖iteratedFDeriv ℝ 3 (fun x => g x i j) y‖ ≤ M₃)
    (hD₄ : ∀ i j,‖iteratedFDeriv ℝ 4 (fun x => g x i j) y‖ ≤ M₄) (k i j : I) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => christoffel g x k i j))) y‖ ≤
      9*(K*M₄+3*(9*K^2*M₁)*M₃+3*(9*(162*K^3*M₁^2+9*K^2*M₂))*M₂+(9*(K^2*M₃+4*K*(9*K^2*M₁)*M₂+(2*K*(9*(162*K^3*M₁^2+9*K^2*M₂))+2*(9*K^2*M₁)^2)*M₁))*M₁) := by
  let P := K*M₄+3*(9*K^2*M₁)*M₃+3*(9*(162*K^3*M₁^2+9*K^2*M₂))*M₂+(9*(K^2*M₃+4*K*(9*K^2*M₁)*M₂+(2*K*(9*(162*K^3*M₁^2+9*K^2*M₂))+2*(9*K^2*M₁)^2)*M₁))*M₁
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hInv (a b : I) := h.contDiffOn_inverse_entry hK a b
  have hCoord (a b c : I) := contDiffOn_coordDeriv hΩ (h.1 b c) a
  have hInvD (a b : I) : ‖fderiv ℝ (fun x => (g x)⁻¹ a b) y‖ ≤ 9*K^2*M₁ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simpa only [Real.norm_eq_abs] using h.inverse_derivative_entry_bound hΩ hK hy M₁ hM₁ hD v a b
  have hCoord0 (a b c : I) : |coordDeriv a (fun x => g x b c) y| ≤ M₁ :=
    (coordDeriv_abs_le _ y a).trans (hD b c)
  have hNorm (f : X → ℝ) : ‖iteratedFDeriv ℝ 3 f y‖ = ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y‖ :=
    norm_iteratedFDeriv_three_eq_nested f y
  have hNorm₂ (f : X → ℝ) : ‖iteratedFDeriv ℝ 2 f y‖ = ‖fderiv ℝ (fderiv ℝ f) y‖ :=
    norm_iteratedFDeriv_two_eq_nested f y
  have hCoord1 (a b c : I) : ‖fderiv ℝ (coordDeriv a (fun x => g x b c)) y‖ ≤ M₂ := by
    have hb := norm_iteratedFDeriv_coordDeriv_le hΩ (h.1 b c) hy a 1
    rw [norm_iteratedFDeriv_one] at hb
    exact hb.trans (by simpa only [hNorm₂] using hD₂ b c)
  have hCoord2 (a b c : I) : ‖fderiv ℝ (fderiv ℝ (coordDeriv a (fun x => g x b c))) y‖ ≤ M₃ := by
    rw [← hNorm₂]
    exact (norm_iteratedFDeriv_coordDeriv_le hΩ (h.1 b c) hy a 2).trans (hD₃ b c)
  have hCoord3 (a b c : I) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (coordDeriv a (fun x => g x b c)))) y‖ ≤ M₄ := by
    rw [← hNorm]
    exact (norm_iteratedFDeriv_coordDeriv_le hΩ (h.1 b c) hy a 3).trans (hD₄ b c)
  have hTerm (l a b c : I) : ‖iteratedFDeriv ℝ 3
      (fun x => (g x)⁻¹ k l*coordDeriv a (fun z => g z b c) x) y‖ ≤ P := by
    rw [hNorm]
    exact (norm_third_fderiv_mul_at hΩ (hInv k l) (hCoord a b c) hy).trans (by
      dsimp only [P]
      gcongr
      · exact h.inverse_entry_bound hK hy k l
      · exact hCoord3 a b c
      · exact hInvD k l
      · exact hCoord2 a b c
      · exact h.inverse_second_fderiv_bound hΩ hK hy M₁ M₂ hM₁ hM₂ hD hD₂ k l
      · exact hCoord1 a b c
      · exact h.inverse_third_fderiv_bound hΩ hK hy M₁ M₂ M₃ hM₁ hM₂ hM₃ hD hD₂
          (fun i j => by rw [← hNorm]; exact hD₃ i j) k l
      · exact hCoord0 a b c)
  let F (l : I) (x : X) := (g x)⁻¹ k l*coordDeriv i (fun z => g z l j) x+
    (g x)⁻¹ k l*coordDeriv j (fun z => g z i l) x-
    (g x)⁻¹ k l*coordDeriv l (fun z => g z i j) x
  have hF (l : I) : ContDiffOn ℝ ∞ (F l) Ω :=
    (((hInv k l).mul (hCoord i l j)).add ((hInv k l).mul (hCoord j i l))).sub
      ((hInv k l).mul (hCoord l i j))
  have hFBound (l : I) : ‖iteratedFDeriv ℝ 3 (F l) y‖ ≤ 3*P := by
    exact (norm_iteratedFDeriv_add_sub_at
      (((hInv k l).mul (hCoord i l j)).contDiffAt (hΩ.mem_nhds hy))
      (((hInv k l).mul (hCoord j i l)).contDiffAt (hΩ.mem_nhds hy))
      (((hInv k l).mul (hCoord l i j)).contDiffAt (hΩ.mem_nhds hy)) 3).trans
      (by linarith only [hTerm l i l j,hTerm l j i l,hTerm l l i j])
  have hFun : (fun x => christoffel g x k i j) =
      (fun x => (1/2:ℝ) • ∑ l,F l x) := by
    funext x
    simp only [christoffel,F,smul_eq_mul,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [← hNorm,hFun,iteratedFDeriv_const_smul_apply'
    (((ContDiffOn.sum (fun l _ => hF l)).contDiffAt (hΩ.mem_nhds hy)).of_le (by simp)),norm_smul]
  rw [iteratedFDeriv_fun_sum_apply (fun l _ => ((hF l).contDiffAt (hΩ.mem_nhds hy)).of_le (by simp))]
  have hb := (norm_sum_le (Finset.univ : Finset I) (fun l => iteratedFDeriv ℝ 3 (F l) y)).trans
    (Finset.sum_le_sum (fun l _ => hFBound l))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  have hh : |(1/2:ℝ)| ≤ 1 := by norm_num
  change |(1/2:ℝ)| * _ ≤ 9*P
  calc
    _ ≤ 1*(3*(3*P)) := mul_le_mul hh hb (norm_nonneg _) zero_le_one
    _ = _ := by ring

end ShrinkingSpheres
