import Proof.FirstErrorScalarCoefficients
import Proof.WeightedTaylorCoefficientNorms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def firstErrorScalarFixedBudget (Q0 : SmoothCoefficientJets 2) : ℝ :=
  1+‖closedUnitCoefficient Q0‖+
    (∑ j : I,‖smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j)‖)+
    ∑ j : I,‖closedCoordinateCoefficientProductL Q0 j‖

lemma firstErrorScalarFixedBudget_bounds (Q0 : SmoothCoefficientJets 2) :
    1 ≤ firstErrorScalarFixedBudget Q0 ∧ ‖closedUnitCoefficient Q0‖ ≤ firstErrorScalarFixedBudget Q0 ∧
    (∀ j : I,‖smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j)‖ ≤ firstErrorScalarFixedBudget Q0) ∧
    ∀ j : I,‖closedCoordinateCoefficientProductL Q0 j‖ ≤ firstErrorScalarFixedBudget Q0 := by
  have hN := norm_nonneg (closedUnitCoefficient Q0)
  have hS : 0 ≤ ∑ j : I,‖smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j)‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j)))
  have hT : 0 ≤ ∑ j : I,‖closedCoordinateCoefficientProductL Q0 j‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg (closedCoordinateCoefficientProductL Q0 j))
  unfold firstErrorScalarFixedBudget
  refine ⟨by linarith,by linarith,?_,?_⟩
  · intro j
    have hh := Finset.single_le_sum (fun k _ => norm_nonneg (smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k))) (Finset.mem_univ j)
    linarith
  · intro j
    have hh := Finset.single_le_sum (fun k _ => norm_nonneg (closedCoordinateCoefficientProductL Q0 k)) (Finset.mem_univ j)
    linarith

/-- The actual scaling of the scalar coefficients gives one radius factor
in their weighted sum. No differentiability of a moving frame is used. -/
lemma firstErrorScalarCoefficients_weighted_bound (Q0 : SmoothCoefficientJets 2)
    (r A BV BB BQ : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 ≤ A)
    (hBV : 0 ≤ BV) (hBB : 0 ≤ BB) (hBQ : 0 ≤ BQ)
    (b : ℝ) (v : I → ℝ) (Q : I → ClosedCoefficientJets 3)
    (hb : |b| ≤ BB*A*r⁻¹) (hv : ∀ j,|v j| ≤ BV*A) (hQ : ∀ j,‖Q j‖ ≤ BQ*A*r^2) :
    (∑ a,taylorGeneratorWeight r a*‖firstErrorScalarCoefficients Q0 r⁻¹ b v Q a‖) ≤
      (firstErrorScalarFixedBudget Q0*(3*BV+BB+15*BQ))*A*r := by
  obtain ⟨hJ,hUnit,hCoord,hProd⟩ := firstErrorScalarFixedBudget_bounds Q0
  let J := firstErrorScalarFixedBudget Q0
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hNormal : ‖∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j)‖ ≤ 3*J*BQ*A*r^2 := by
    calc
      _ ≤ ∑ j : I,‖closedCoordinateCoefficientProductL Q0 j (Q j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : I,J*(BQ*A*r^2) := Finset.sum_le_sum (fun j _ =>
        ((closedCoordinateCoefficientProductL Q0 j).le_opNorm (Q j)).trans
          (mul_le_mul (hProd j) (hQ j) (norm_nonneg _) hJ0))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  have hVector : ‖∑ j : I,v j • smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j)‖ ≤ 3*J*BV*A := by
    calc
      _ ≤ ∑ j : I,‖v j • smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : I,(BV*A)*J := Finset.sum_le_sum (fun j _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hv j) (hCoord j) (norm_nonneg _) (mul_nonneg hBV hA))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  have hT : ‖firstErrorScalarCoefficients Q0 r⁻¹ b v Q .taylor‖ ≤
      r⁻¹*(3*J*BV*A)+(BB*A*r⁻¹)*J+r⁻¹*(3*J*BQ*A*r^2) := by
    have h1 := norm_add_le (r⁻¹ • (∑ j : I,v j • smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j)))
      (b • closedUnitCoefficient Q0)
    have h2 := norm_add_le (r⁻¹ • (∑ j : I,v j • smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j))+
      b • closedUnitCoefficient Q0) (r⁻¹ • (∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j)))
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hi] at h1 h2
    have hb' := mul_le_mul hb hUnit (norm_nonneg _) (by positivity : 0 ≤ BB*A*r⁻¹)
    have hv' := mul_le_mul_of_nonneg_left hVector hi
    have hn' := mul_le_mul_of_nonneg_left hNormal hi
    change ‖r⁻¹ • (∑ j : I,v j • smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 j))+
      b • closedUnitCoefficient Q0+r⁻¹ • (∑ j : I,closedCoordinateCoefficientProductL Q0 j (Q j))‖ ≤ _
    linarith only [h1,h2,hb',hv',hn']
  have hD : ‖firstErrorScalarCoefficients Q0 r⁻¹ b v Q .degree‖ ≤ r⁻¹*(3*J*BQ*A*r^2) := by
    simp only [firstErrorScalarCoefficients,norm_smul,Real.norm_eq_abs,abs_of_nonneg hi]
    exact mul_le_mul_of_nonneg_left hNormal hi
  have hR (i j : I) : ‖firstErrorScalarCoefficients Q0 r⁻¹ b v Q (.rotation i j)‖ ≤ r⁻¹*(J*(BQ*A*r^2)) := by
    simp only [firstErrorScalarCoefficients,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hi]
    exact mul_le_mul_of_nonneg_left
      (((closedCoordinateCoefficientProductL Q0 i).le_opNorm (Q j)).trans
        (mul_le_mul (hProd i) (hQ j) (norm_nonneg _) hJ0)) hi
  exact weighted_taylor_coefficient_norm_sum _ r A BV BB BQ J hr hr1 hA hBV hBB hBQ hJ0 hT hD hR
end ShrinkingSpheres
