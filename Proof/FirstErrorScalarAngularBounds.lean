import Proof.FirstErrorScalarAngularCoefficients
import Proof.WeightedTaylorCoefficientNorms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_coordinateScalarAngularTemplate_le (Q0 : SmoothCoefficientJets 2) (k i j : I) :
    ‖coordinateScalarAngularTemplate Q0 k i j‖ ≤ 2*firstErrorScalarFixedBudget Q0 := by
  let J := firstErrorScalarFixedBudget Q0
  have hJ : 0 ≤ J := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hIf (P : Prop) [Decidable P] (l : I) :
      ‖(if P then smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 l) else 0)‖ ≤ J := by
    split_ifs
    · exact (firstErrorScalarFixedBudget_bounds Q0).2.2.1 l
    · simpa only [norm_zero] using hJ
  exact (norm_sub_le _ _).trans ((add_le_add (hIf (k=j) i) (hIf (k=i) j)).trans_eq (by ring))

/-- The scalar first-error angular witnesses have the same one-radius
    weighted gain; only the existing coefficient and angular budgets enter. -/
lemma firstErrorScalarAngularCoefficients_weighted_bound (Q0 : SmoothCoefficientJets 2)
    (r A BV BQ BR : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 ≤ A)
    (hBV : 0 ≤ BV) (hBQ : 0 ≤ BQ) (hBR : 0 ≤ BR)
    (v : I → ℝ) (Q R : I → ClosedCoefficientJets 3) (i j : I)
    (hv : ∀ k,|v k| ≤ BV*A) (hQ : ∀ k,‖Q k‖ ≤ BQ*A*r^2)
    (hR : ∀ k,‖R k‖ ≤ BR*A*r^2) :
    (∑ a,taylorGeneratorWeight r a*‖firstErrorScalarAngularCoefficients Q0 r⁻¹ v Q R i j a‖) ≤
      (firstErrorScalarFixedBudget Q0*(6*BV+15*(BR+2*BQ)))*A*r := by
  let J := firstErrorScalarFixedBudget Q0
  let B := BR+2*BQ
  have hJ : 0 ≤ J := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hProduct (k l : I) : ‖closedCoordinateAngularCoefficient Q0 k i j (Q l) (R l)‖ ≤ J*(B*A*r^2) := by
    have hQQ := (SmoothFiniteJetBound.constant (Q l) (0:ℝ) 0).weaken (hQ l)
    have hRR := (SmoothFiniteJetBound.constant (R l) (0:ℝ) 0).weaken (hR l)
    have hh := closedCoordinateAngularCoefficient_jets Q0 k i j (fun _ : ℝ => Q l) (fun _ : ℝ => R l)
      0 0 (BQ*A*r^2) (BR*A*r^2) hQQ hRR
    have hn := hh.bound 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at hn
    exact hn.trans_eq (by dsimp only [J,B];ring)
  have hVector : ‖∑ k : I,v k • coordinateScalarAngularTemplate Q0 k i j‖ ≤ 6*J*BV*A := by
    calc
      _ ≤ ∑ k : I,‖v k • coordinateScalarAngularTemplate Q0 k i j‖ := norm_sum_le _ _
      _ ≤ ∑ k : I,(BV*A)*(2*J) := Finset.sum_le_sum (fun k _ => by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hv k) (norm_coordinateScalarAngularTemplate_le Q0 k i j)
          (norm_nonneg _) (mul_nonneg hBV hA))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  have hNormal : ‖∑ k : I,closedCoordinateAngularCoefficient Q0 k i j (Q k) (R k)‖ ≤ 3*J*B*A*r^2 := by
    calc
      _ ≤ ∑ k : I,‖closedCoordinateAngularCoefficient Q0 k i j (Q k) (R k)‖ := norm_sum_le _ _
      _ ≤ ∑ k : I,J*(B*A*r^2) := Finset.sum_le_sum (fun k _ => hProduct k k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  have hT : ‖firstErrorScalarAngularCoefficients Q0 r⁻¹ v Q R i j .taylor‖ ≤
      r⁻¹*(3*J*(2*BV)*A)+(0*A*r⁻¹)*J+r⁻¹*(3*J*B*A*r^2) := by
    have hh := norm_add_le
      (r⁻¹ • (∑ k : I,v k • coordinateScalarAngularTemplate Q0 k i j))
      (r⁻¹ • (∑ k : I,closedCoordinateAngularCoefficient Q0 k i j (Q k) (R k)))
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hi] at hh
    exact (hh.trans (add_le_add (mul_le_mul_of_nonneg_left hVector hi)
      (mul_le_mul_of_nonneg_left hNormal hi))).trans_eq (by ring)
  have hD : ‖firstErrorScalarAngularCoefficients Q0 r⁻¹ v Q R i j .degree‖ ≤ r⁻¹*(3*J*B*A*r^2) := by
    change ‖r⁻¹ • (∑ k : I,closedCoordinateAngularCoefficient Q0 k i j (Q k) (R k))‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hi]
    exact mul_le_mul_of_nonneg_left hNormal hi
  have hRot (k l : I) : ‖firstErrorScalarAngularCoefficients Q0 r⁻¹ v Q R i j (.rotation k l)‖ ≤
      r⁻¹*(J*(B*A*r^2)) := by
    change ‖(-r⁻¹) • closedCoordinateAngularCoefficient Q0 k i j (Q l) (R l)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hi]
    exact mul_le_mul_of_nonneg_left (hProduct k l) hi
  have hh := weighted_taylor_coefficient_norm_sum
    (firstErrorScalarAngularCoefficients Q0 r⁻¹ v Q R i j) r A (2*BV) 0 B J hr hr1 hA
    (by positivity) le_rfl hB hJ hT hD hRot
  exact hh.trans_eq (by dsimp only [J,B];ring)
end ShrinkingSpheres
