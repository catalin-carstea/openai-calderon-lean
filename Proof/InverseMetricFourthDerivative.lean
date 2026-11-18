import Proof.FourthDerivativeProductBounds
import Proof.InverseMetricThirdDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def fourthInverseMetricBudget (K M1 M2 M3 M4 : ℝ) : ℝ :=
  let A := 9*K^2*M1
  let B := 9*(162*K^3*M1^2+9*K^2*M2)
  let C := 9*(K^2*M3+4*K*A*M2+(2*K*B+2*A^2)*M1)
  9*(K^2*M4+3*(2*K*A)*M3+3*(2*K*B+2*A^2)*M2+(2*K*C+6*A*B)*M1)

/-- Fourth inverse-metric jets use only the four supplied metric jets.
    The proof differentiates the existing inverse operator identity three times. -/
theorem Elliptic.inverse_fourth_fderiv_bound {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω)
    (M1 M2 M3 M4 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hM4 : 0 ≤ M4)
    (hD1 : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M1)
    (hD2 : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M2)
    (hD3 : ∀ i j,‖iteratedFDeriv ℝ 3 (fun x => g x i j) y‖ ≤ M3)
    (hD4 : ∀ i j,‖iteratedFDeriv ℝ 4 (fun x => g x i j) y‖ ≤ M4) (i j : I) :
    ‖iteratedFDeriv ℝ 4 (fun x => (g x)⁻¹ i j) y‖ ≤ fourthInverseMetricBudget K M1 M2 M3 M4 := by
  let A := 9*K^2*M1
  let B := 9*(162*K^3*M1^2+9*K^2*M2)
  let C := 9*(K^2*M3+4*K*A*M2+(2*K*B+2*A^2)*M1)
  let Q := K^2*M4+3*(2*K*A)*M3+3*(2*K*B+2*A^2)*M2+(2*K*C+6*A*B)*M1
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hQ : 0 ≤ Q := by dsimp [Q];positivity
  have hInv (a b : I) := h.contDiffOn_inverse_entry hK a b
  have hInv1 (a b : I) : ‖fderiv ℝ (fun x => (g x)⁻¹ a b) y‖ ≤ A := by
    apply ContinuousLinearMap.opNorm_le_bound _ hA
    intro v
    simpa only [Real.norm_eq_abs] using h.inverse_derivative_entry_bound hΩ hK hy M1 hM1 hD1 v a b
  have hInv2 (a b : I) : ‖fderiv ℝ (fderiv ℝ (fun x => (g x)⁻¹ a b)) y‖ ≤ B :=
    h.inverse_second_fderiv_bound hΩ hK hy M1 M2 hM1 hM2 hD1 hD2 a b
  have hInv3 (a b : I) : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun x => (g x)⁻¹ a b))) y‖ ≤ C :=
    h.inverse_third_fderiv_bound hΩ hK hy M1 M2 M3 hM1 hM2 hM3 hD1 hD2
      (fun u v => by rw [← norm_iteratedFDeriv_three_eq_nested];exact hD3 u v) a b
  let W (p q : I) (x : X) := (g x)⁻¹ i p*(g x)⁻¹ q j
  let G (p q : I) (x : X) := fderiv ℝ (fun z => g z p q) x
  have hW (p q : I) : ContDiffOn ℝ ∞ (W p q) Ω := (hInv i p).mul (hInv q j)
  have hG (p q : I) : ContDiffOn ℝ ∞ (G p q) Ω := (h.1 p q).fderiv_of_isOpen (m:=∞) hΩ (by simp)
  have hW0 (p q : I) : |W p q y| ≤ K^2 := by
    dsimp [W]
    rw [abs_mul,pow_two]
    exact mul_le_mul (h.inverse_entry_bound hK hy i p) (h.inverse_entry_bound hK hy q j) (abs_nonneg _) hK.le
  have hW1 (p q : I) : ‖fderiv ℝ (W p q) y‖ ≤ 2*K*A := by
    have hdf := ((hInv i p).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
    have hdg := ((hInv q j).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
    change ‖fderiv ℝ ((fun x => (g x)⁻¹ i p)*(fun x => (g x)⁻¹ q j)) y‖ ≤ _
    rw [fderiv_mul hdf hdg]
    calc
      _ ≤ |(g y)⁻¹ i p| *‖fderiv ℝ (fun x => (g x)⁻¹ q j) y‖+
          |(g y)⁻¹ q j| *‖fderiv ℝ (fun x => (g x)⁻¹ i p) y‖ := by
        exact (norm_add_le _ _).trans (add_le_add (by rw [norm_smul,Real.norm_eq_abs]) (by rw [norm_smul,Real.norm_eq_abs]))
      _ ≤ K*A+K*A := by gcongr <;> first | exact h.inverse_entry_bound hK hy _ _ | exact hInv1 _ _
      _ = _ := by ring
  have hW2 (p q : I) : ‖iteratedFDeriv ℝ 2 (W p q) y‖ ≤ 2*K*B+2*A^2 := by
    rw [norm_iteratedFDeriv_two_eq_nested]
    exact (norm_second_fderiv_mul_at hΩ (hInv i p) (hInv q j) hy).trans (by
      calc
        _ ≤ K*B+2*A*A+B*K := by
          gcongr <;> first | exact h.inverse_entry_bound hK hy _ _ | exact hInv1 _ _ | exact hInv2 _ _
        _ = _ := by ring)
  have hW3 (p q : I) : ‖iteratedFDeriv ℝ 3 (W p q) y‖ ≤ 2*K*C+6*A*B := by
    rw [norm_iteratedFDeriv_three_eq_nested]
    exact (norm_third_fderiv_mul_at hΩ (hInv i p) (hInv q j) hy).trans (by
      calc
        _ ≤ K*C+3*A*B+3*B*A+C*K := by
          gcongr
          · exact h.inverse_entry_bound hK hy i p
          · exact hInv3 q j
          · exact hInv1 i p
          · exact hInv2 q j
          · exact hInv2 i p
          · exact hInv1 q j
          · exact hInv3 i p
          · exact h.inverse_entry_bound hK hy q j
        _ = _ := by ring)
  have hG2 (p q : I) : ‖iteratedFDeriv ℝ 2 (G p q) y‖ ≤ M3 := by
    change ‖iteratedFDeriv ℝ 2 (fderiv ℝ (fun z => g z p q)) y‖ ≤ _
    rw [norm_iteratedFDeriv_fderiv]
    exact hD3 p q
  have hG3 (p q : I) : ‖iteratedFDeriv ℝ 3 (G p q) y‖ ≤ M4 := by
    change ‖iteratedFDeriv ℝ 3 (fderiv ℝ (fun z => g z p q)) y‖ ≤ _
    rw [norm_iteratedFDeriv_fderiv]
    exact hD4 p q
  have hTerm (p q : I) : ‖iteratedFDeriv ℝ 3 (fun x => W p q x • G p q x) y‖ ≤ Q := by
    exact (norm_third_iteratedFDeriv_smul_at hΩ (hW p q) (hG p q) hy).trans (by
      calc
        _ ≤ K^2*M4+3*(2*K*A)*M3+3*(2*K*B+2*A^2)*M2+(2*K*C+6*A*B)*M1 := by
          gcongr
          · exact hW0 p q
          · exact hG3 p q
          · exact hW1 p q
          · exact hG2 p q
          · exact hW2 p q
          · exact hD2 p q
          · exact hW3 p q
          · exact hD1 p q
        _ = Q := rfl)
  have hEq : (fun x => fderiv ℝ (fun z => (g z)⁻¹ i j) x) =ᶠ[𝓝 y]
      fun x => -(∑ p,∑ q,W p q x • G p q x) := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact fderiv_inverse_metric_operator hΩ h hK hx i j
  rw [← norm_iteratedFDeriv_fderiv (n:=3),(hEq.iteratedFDeriv ℝ 3).eq_of_nhds]
  change ‖iteratedFDeriv ℝ 3 (-(fun x => ∑ p,∑ q,W p q x • G p q x)) y‖ ≤ 9*Q
  rw [iteratedFDeriv_neg_apply,norm_neg]
  have hRow (p : I) : ContDiffAt ℝ ∞ (fun x => ∑ q,W p q x • G p q x) y :=
    (ContDiffOn.sum (fun q _ => (hW p q).smul (hG p q))).contDiffAt (hΩ.mem_nhds hy)
  calc
    _ ≤ ∑ p : I,‖iteratedFDeriv ℝ 3 (fun x => ∑ q,W p q x • G p q x) y‖ :=
      norm_iteratedFDeriv_finite_sum_le _ _ y 3 (fun p _ => hRow p)
    _ ≤ ∑ p : I,∑ q : I,‖iteratedFDeriv ℝ 3 (fun x => W p q x • G p q x) y‖ := by
      apply Finset.sum_le_sum
      intro p _
      exact norm_iteratedFDeriv_finite_sum_le _ _ y 3
        (fun q _ => ((hW p q).smul (hG p q)).contDiffAt (hΩ.mem_nhds hy))
    _ ≤ ∑ _p : I,∑ _q : I,Q := Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ => hTerm p q))
    _ = 9*Q := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end ShrinkingSpheres
