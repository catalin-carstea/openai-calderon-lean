import Proof.InverseMetricFourthDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def fourthChristoffelBudget (K M1 M2 M3 M4 M5 : ℝ) : ℝ :=
  let A := 9*K^2*M1
  let B := 9*(162*K^3*M1^2+9*K^2*M2)
  let C := 9*(K^2*M3+4*K*A*M2+(2*K*B+2*A^2)*M1)
  let D := fourthInverseMetricBudget K M1 M2 M3 M4
  9*(K*M5+4*A*M4+6*B*M3+4*C*M2+D*M1)

/-- The fourth actual Christoffel jet uses only five metric jets. -/
theorem Elliptic.christoffel_fourth_fderiv_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M1 M2 M3 M4 M5 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4) (hM5 : 0 ≤ M5)
    (hD1 : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M1)
    (hD2 : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M2)
    (hD3 : ∀ i j,‖iteratedFDeriv ℝ 3 (fun x => g x i j) y‖ ≤ M3)
    (hD4 : ∀ i j,‖iteratedFDeriv ℝ 4 (fun x => g x i j) y‖ ≤ M4)
    (hD5 : ∀ i j,‖iteratedFDeriv ℝ 5 (fun x => g x i j) y‖ ≤ M5) (k i j : I) :
    ‖iteratedFDeriv ℝ 4 (fun x => christoffel g x k i j) y‖ ≤ fourthChristoffelBudget K M1 M2 M3 M4 M5 := by
  let A := 9*K^2*M1
  let B := 9*(162*K^3*M1^2+9*K^2*M2)
  let C := 9*(K^2*M3+4*K*A*M2+(2*K*B+2*A^2)*M1)
  let D := fourthInverseMetricBudget K M1 M2 M3 M4
  let Q := K*M5+4*A*M4+6*B*M3+4*C*M2+D*M1
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hD : 0 ≤ D := by dsimp [D,fourthInverseMetricBudget];positivity
  have hQ : 0 ≤ Q := by dsimp [Q];positivity
  have hInv (a b : I) := h.contDiffOn_inverse_entry hK a b
  have hCoord (a b c : I) := contDiffOn_coordDeriv hΩ (h.1 b c) a
  have hInv1 (a b : I) : ‖fderiv ℝ (fun x => (g x)⁻¹ a b) y‖ ≤ A := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro v
    simpa only [Real.norm_eq_abs] using h.inverse_derivative_entry_bound hΩ hK hy M1 hM1 hD1 v a b
  have hInv2 (a b : I) : ‖iteratedFDeriv ℝ 2 (fun x => (g x)⁻¹ a b) y‖ ≤ B := by
    rw [norm_iteratedFDeriv_two_eq_nested]
    exact h.inverse_second_fderiv_bound hΩ hK hy M1 M2 hM1 hM2 hD1 hD2 a b
  have hInv3 (a b : I) : ‖iteratedFDeriv ℝ 3 (fun x => (g x)⁻¹ a b) y‖ ≤ C := by
    rw [norm_iteratedFDeriv_three_eq_nested]
    exact h.inverse_third_fderiv_bound hΩ hK hy M1 M2 M3 hM1 hM2 hM3 hD1 hD2
      (fun u v => by rw [← norm_iteratedFDeriv_three_eq_nested];exact hD3 u v) a b
  have hInv4 (a b : I) : ‖iteratedFDeriv ℝ 4 (fun x => (g x)⁻¹ a b) y‖ ≤ D :=
    h.inverse_fourth_fderiv_bound hΩ hK hy M1 M2 M3 M4 hM1 hM2 hM3 hM4 hD1 hD2 hD3 hD4 a b
  have hCoord0 (a b c : I) : |coordDeriv a (fun x => g x b c) y| ≤ M1 :=
    (coordDeriv_abs_le _ y a).trans (hD1 b c)
  have hCoord1 (a b c : I) : ‖fderiv ℝ (coordDeriv a (fun x => g x b c)) y‖ ≤ M2 := by
    have hb := norm_iteratedFDeriv_coordDeriv_le hΩ (h.1 b c) hy a 1
    rw [norm_iteratedFDeriv_one] at hb
    exact hb.trans (by rw [norm_iteratedFDeriv_two_eq_nested];exact hD2 b c)
  have hCoord2 (a b c : I) : ‖iteratedFDeriv ℝ 2 (coordDeriv a (fun x => g x b c)) y‖ ≤ M3 :=
    (norm_iteratedFDeriv_coordDeriv_le hΩ (h.1 b c) hy a 2).trans (hD3 b c)
  have hCoord3 (a b c : I) : ‖iteratedFDeriv ℝ 3 (coordDeriv a (fun x => g x b c)) y‖ ≤ M4 :=
    (norm_iteratedFDeriv_coordDeriv_le hΩ (h.1 b c) hy a 3).trans (hD4 b c)
  have hCoord4 (a b c : I) : ‖iteratedFDeriv ℝ 4 (coordDeriv a (fun x => g x b c)) y‖ ≤ M5 :=
    (norm_iteratedFDeriv_coordDeriv_le hΩ (h.1 b c) hy a 4).trans (hD5 b c)
  have hTerm (l a b c : I) : ‖iteratedFDeriv ℝ 4
      (fun x => (g x)⁻¹ k l*coordDeriv a (fun z => g z b c) x) y‖ ≤ Q := by
    exact (norm_fourth_iteratedFDeriv_mul_at hΩ (hInv k l) (hCoord a b c) hy).trans (by
      calc
        _ ≤ K*M5+4*A*M4+6*B*M3+4*C*M2+D*M1 := by
          gcongr
          · exact h.inverse_entry_bound hK hy k l
          · exact hCoord4 a b c
          · exact hInv1 k l
          · exact hCoord3 a b c
          · exact hInv2 k l
          · exact hCoord2 a b c
          · exact hInv3 k l
          · exact hCoord1 a b c
          · exact hInv4 k l
          · exact hCoord0 a b c
        _ = Q := rfl)
  let F (l : I) (x : X) := (g x)⁻¹ k l*coordDeriv i (fun z => g z l j) x+
    (g x)⁻¹ k l*coordDeriv j (fun z => g z i l) x-(g x)⁻¹ k l*coordDeriv l (fun z => g z i j) x
  have hF (l : I) : ContDiffOn ℝ ∞ (F l) Ω :=
    (((hInv k l).mul (hCoord i l j)).add ((hInv k l).mul (hCoord j i l))).sub ((hInv k l).mul (hCoord l i j))
  have hFBound (l : I) : ‖iteratedFDeriv ℝ 4 (F l) y‖ ≤ 3*Q := by
    exact (norm_iteratedFDeriv_add_sub_at
      (((hInv k l).mul (hCoord i l j)).contDiffAt (hΩ.mem_nhds hy))
      (((hInv k l).mul (hCoord j i l)).contDiffAt (hΩ.mem_nhds hy))
      (((hInv k l).mul (hCoord l i j)).contDiffAt (hΩ.mem_nhds hy)) 4).trans
      (by linarith only [hTerm l i l j,hTerm l j i l,hTerm l l i j])
  have hFun : (fun x => christoffel g x k i j) = fun x => (1/2:ℝ) • ∑ l,F l x := by
    funext x
    simp only [christoffel,F,smul_eq_mul,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hFun,iteratedFDeriv_const_smul_apply'
    (((ContDiffOn.sum (fun l _ => hF l)).contDiffAt (hΩ.mem_nhds hy)).of_le (by simp)),norm_smul]
  have hb := norm_iteratedFDeriv_finite_sum_le Finset.univ F y 4
    (fun l _ => (hF l).contDiffAt (hΩ.mem_nhds hy))
  have hSum := hb.trans (Finset.sum_le_sum (fun l _ => hFBound l))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hSum
  change |(1/2:ℝ)| * _ ≤ 9*Q
  exact (mul_le_mul (by norm_num : |(1/2:ℝ)| ≤ 1) hSum (norm_nonneg _) zero_le_one).trans_eq (by ring)

end ShrinkingSpheres
