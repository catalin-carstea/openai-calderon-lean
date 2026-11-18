import Proof.DensityCoefficientJets
import Proof.ConnectionSecondBounds
import Proof.MetricDensityBounds
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma norm_linear_le_of_axis_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : X →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C) (hL : ∀ i,‖L (axis i)‖ ≤ C) : ‖L‖ ≤ 3*C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hEq : L v = ∑ i,v i • L (axis i) := by
    conv_lhs => rw [← axis_expansion v]
    simp only [map_sum,map_smul]
  rw [hEq]
  calc
    _ ≤ ∑ i,‖v i • L (axis i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I,‖v‖*C := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i)
        (hL i) (norm_nonneg _) (norm_nonneg v)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

/-- A second angular metric jet gives the actual second divergence-coefficient
    jet, with a quadratic dependence on the first metric jet. -/
theorem Elliptic.principalCoefficient_second_fderiv_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (h : Elliptic Ω K g) (hK : 0 < K)
    {y : X} (hy : y ∈ Ω) (M1 M2 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hD1 : ∀ i j,‖fderiv ℝ (fun x => g x i j) y‖ ≤ M1)
    (hD2 : ∀ i j,‖fderiv ℝ (fderiv ℝ (fun x => g x i j)) y‖ ≤ M2) (i j : I) :
    ‖fderiv ℝ (fderiv ℝ (fun x => principalCoefficient g x i j)) y‖ ≤
      metricDensityBudget K*(K*(9*(972*K^2*M1^2+27*K*M2))+
        2*(81*K*M1)*(9*K^2*M1)+9*(162*K^3*M1^2+9*K^2*M2)) := by
  have hμ := h.contDiffOn_density hK
  have hInv := h.contDiffOn_inverse_entry hK i j
  have hμPos : 0 ≤ metricDensity g y := Real.sqrt_nonneg _
  have hμBound := h.density_upper_bound hK hy
  have hμ1 : ‖fderiv ℝ (metricDensity g) y‖ ≤ (81*K*M1)*metricDensity g y := by
    have hb := norm_linear_le_of_axis_bound (fderiv ℝ (metricDensity g) y)
      ((27*K*M1)*metricDensity g y) (by positivity)
      (fun a => by simpa only [Real.norm_eq_abs,coordDeriv] using (h.relative_density_coordinate_jets hΩ hK hy M1 M2 hM1 hM2 hD1 hD2 a a).1)
    exact hb.trans_eq (by ring)
  have hμ2 : ‖fderiv ℝ (fderiv ℝ (metricDensity g)) y‖ ≤
      (9*(972*K^2*M1^2+27*K*M2))*metricDensity g y := by
    have hb : ‖fderiv ℝ (fderiv ℝ (metricDensity g)) y‖ ≤
        9*((972*K^2*M1^2+27*K*M2)*metricDensity g y) := by
      apply norm_bilinear_le_of_axis_bound _ _ (by positivity)
      intro a b
      have hd := ((hμ.fderiv_of_isOpen (m:=∞) hΩ (by simp)).contDiffAt
        (hΩ.mem_nhds hy)).differentiableAt (by simp)
      rw [← coordinate_second_derivative (metricDensity g) y hd a b,Real.norm_eq_abs]
      exact (h.relative_density_coordinate_jets hΩ hK hy M1 M2 hM1 hM2 hD1 hD2 b a).2
    exact hb.trans_eq (by ring)
  have hInv1 : ‖fderiv ℝ (fun x => (g x)⁻¹ i j) y‖ ≤ 9*K^2*M1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simpa only [Real.norm_eq_abs] using h.inverse_derivative_entry_bound hΩ hK hy M1 hM1 hD1 v i j
  have hInv2 := h.inverse_second_fderiv_bound hΩ hK hy M1 M2 hM1 hM2 hD1 hD2 i j
  have hb := norm_second_fderiv_mul_at hΩ hμ hInv hy
  change ‖fderiv ℝ (fderiv ℝ (fun x => principalCoefficient g x i j)) y‖ ≤ _ at hb
  exact hb.trans (by
    calc
      _ ≤ (metricDensity g y)*(9*(162*K^3*M1^2+9*K^2*M2))+
          2*((81*K*M1)*metricDensity g y)*(9*K^2*M1)+
          ((9*(972*K^2*M1^2+27*K*M2))*metricDensity g y)*K := by
        rw [abs_of_nonneg hμPos]
        gcongr <;> first | exact hμ1 | exact hμ2 | exact hInv1 | exact hInv2 |
          exact h.inverse_entry_bound hK hy i j
      _ = (metricDensity g y)*(K*(9*(972*K^2*M1^2+27*K*M2))+
          2*(81*K*M1)*(9*K^2*M1)+9*(162*K^3*M1^2+9*K^2*M2)) := by ring
      _ ≤ _ := by gcongr)

end ShrinkingSpheres
