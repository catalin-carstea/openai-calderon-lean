import Proof.ThirdDerivativeProductBounds
import Proof.ConnectionSecondBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma fderiv_inverse_metric_operator {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) (i j : I) :
    fderiv ℝ (fun x => (g x)⁻¹ i j) y =
      -(∑ p,∑ q,((g y)⁻¹ i p*(g y)⁻¹ q j) • fderiv ℝ (fun x => g x p q) y) := by
  ext v
  rw [fderiv_inverse_metric_entries hΩ h hK hy]
  simp only [_root_.neg_apply,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Third inverse-metric jets follow by differentiating the operator-valued
    inverse identity twice. This estimate uses only three metric jets. -/
theorem Elliptic.inverse_third_fderiv_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M₁ M₂ M₃ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hD : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M₁)
    (hD₂ : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M₂)
    (hD₃ : ∀ i j,‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => g x i j))) y‖ ≤ M₃)
    (i j : I) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => (g x)⁻¹ i j))) y‖ ≤
      9*(K^2*M₃+4*K*(9*K^2*M₁)*M₂+
        (2*K*(9*(162*K^3*M₁^2+9*K^2*M₂))+2*(9*K^2*M₁)^2)*M₁) := by
  let A := 9*K^2*M₁
  let B := 9*(162*K^3*M₁^2+9*K^2*M₂)
  let P := K^2*M₃+4*K*A*M₂+(2*K*B+2*A^2)*M₁
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hInv (a b : I) := h.contDiffOn_inverse_entry hK a b
  have hInvD (a b : I) : ‖fderiv ℝ (fun x => (g x)⁻¹ a b) y‖ ≤ A := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro v
    simpa only [Real.norm_eq_abs] using h.inverse_derivative_entry_bound hΩ hK hy M₁ hM₁ hD v a b
  have hInvD₂ (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun x => (g x)⁻¹ a b)) y‖ ≤ B :=
    h.inverse_second_fderiv_bound hΩ hK hy M₁ M₂ hM₁ hM₂ hD hD₂ a b
  let C (p q : I) (x : X) := (g x)⁻¹ i p*(g x)⁻¹ q j
  let G (p q : I) (x : X) := fderiv ℝ (fun z => g z p q) x
  have hC (p q : I) : ContDiffOn ℝ ∞ (C p q) Ω := (hInv i p).mul (hInv q j)
  have hG (p q : I) : ContDiffOn ℝ ∞ (G p q) Ω :=
    (h.1 p q).fderiv_of_isOpen (m:=∞) hΩ (by simp)
  have hC0 (p q : I) : |C p q y| ≤ K^2 := by
    dsimp [C]
    rw [abs_mul,pow_two]
    exact mul_le_mul (h.inverse_entry_bound hK hy i p) (h.inverse_entry_bound hK hy q j)
      (abs_nonneg _) hK.le
  have hC1 (p q : I) : ‖fderiv ℝ (C p q) y‖ ≤ 2*K*A := by
    have hd1 := ((hInv i p).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
    have hd2 := ((hInv q j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
    change ‖fderiv ℝ ((fun x => (g x)⁻¹ i p)*(fun x => (g x)⁻¹ q j)) y‖ ≤ _
    rw [fderiv_mul hd1 hd2]
    calc
      _ ≤ |(g y)⁻¹ i p| * ‖fderiv ℝ (fun x => (g x)⁻¹ q j) y‖+
          |(g y)⁻¹ q j| * ‖fderiv ℝ (fun x => (g x)⁻¹ i p) y‖ := by
        exact (norm_add_le _ _).trans (add_le_add (by rw [norm_smul,Real.norm_eq_abs])
          (by rw [norm_smul,Real.norm_eq_abs]))
      _ ≤ K*A+K*A := by gcongr <;> first | exact h.inverse_entry_bound hK hy _ _ | exact hInvD _ _
      _ = _ := by ring
  have hC2 (p q : I) : ‖fderiv ℝ (fderiv ℝ (C p q)) y‖ ≤ 2*K*B+2*A^2 := by
    exact (norm_second_fderiv_mul_at hΩ (hInv i p) (hInv q j) hy).trans (by
      calc
        _ ≤ K*B+2*A*A+B*K := by
          gcongr <;> first | exact h.inverse_entry_bound hK hy _ _ | exact hInvD _ _ | exact hInvD₂ _ _
        _ = _ := by ring)
  have hTerm (p q : I) : ‖iteratedFDeriv ℝ 2 (fun x => C p q x • G p q x) y‖ ≤ P := by
    rw [norm_iteratedFDeriv_two_eq_nested]
    exact (norm_second_fderiv_smul_at hΩ (hC p q) (hG p q) hy).trans (by
      calc
        _ ≤ K^2*M₃+2*(2*K*A)*M₂+(2*K*B+2*A^2)*M₁ := by
          gcongr
          · exact hC0 p q
          · exact hD₃ p q
          · exact hC1 p q
          · exact hD₂ p q
          · exact hC2 p q
          · exact hD p q
        _ = P := by dsimp [P]; ring)
  have hEq : (fun x => fderiv ℝ (fun z => (g z)⁻¹ i j) x) =ᶠ[𝓝 y]
      (fun x => -(∑ p,∑ q,C p q x • G p q x)) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact fderiv_inverse_metric_operator hΩ h hK hx i j
  rw [← norm_iteratedFDeriv_two_eq_nested]
  rw [(hEq.iteratedFDeriv ℝ 2).eq_of_nhds]
  change ‖iteratedFDeriv ℝ 2 (-(fun x => ∑ p,∑ q,C p q x • G p q x)) y‖ ≤ 9*P
  rw [iteratedFDeriv_neg_apply,norm_neg]
  have hRow (p : I) : ContDiffAt ℝ ∞ (fun x => ∑ q,C p q x • G p q x) y :=
    (ContDiffOn.sum (fun q _ => (hC p q).smul (hG p q))).contDiffAt (hΩ.mem_nhds hy)
  calc
    _ ≤ ∑ p : I,‖iteratedFDeriv ℝ 2 (fun x => ∑ q,C p q x • G p q x) y‖ :=
      norm_iteratedFDeriv_finite_sum_le _ _ y 2 (fun p _ => hRow p)
    _ ≤ ∑ p : I,∑ q : I,‖iteratedFDeriv ℝ 2 (fun x => C p q x • G p q x) y‖ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_iteratedFDeriv_finite_sum_le _ _ y 2
        (fun q _ => ((hC p q).smul (hG p q)).contDiffAt (hΩ.mem_nhds hy))
    _ ≤ ∑ _p : I,∑ _q : I,P := Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hTerm p q))
    _ = 9*P := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end ShrinkingSpheres
