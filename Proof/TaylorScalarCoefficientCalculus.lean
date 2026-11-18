import Proof.FlatRaisingRightScalarForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma taylorGeneratorWeight_nonneg (r : ℝ) (a : TaylorGeneratorIndex) :
    0 ≤ taylorGeneratorWeight r a := by
  cases a <;> simp only [taylorGeneratorWeight] <;> positivity

lemma taylor_scalar_weighted_sum_add_le (r : ℝ) (Q R : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    (∑ a,taylorGeneratorWeight r a*‖Q a+R a‖) ≤
      (∑ a,taylorGeneratorWeight r a*‖Q a‖)+(∑ a,taylorGeneratorWeight r a*‖R a‖) := by
  calc
    _ ≤ ∑ a,taylorGeneratorWeight r a*(‖Q a‖+‖R a‖) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (norm_add_le _ _) (taylorGeneratorWeight_nonneg r a))
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib]

lemma taylor_scalar_weighted_sum_smul (r c : ℝ) (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    (∑ a,taylorGeneratorWeight r a*‖c • Q a‖)=|c| *(∑ a,taylorGeneratorWeight r a*‖Q a‖) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_smul,Real.norm_eq_abs]
  ring

lemma taylor_scalar_weighted_sum_finite_le {κ : Type*} [Fintype κ]
    (r : ℝ) (Q : κ → TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    (∑ a,taylorGeneratorWeight r a*‖∑ k,Q k a‖) ≤
      ∑ k,∑ a,taylorGeneratorWeight r a*‖Q k a‖ := by
  calc
    _ ≤ ∑ a,taylorGeneratorWeight r a*(∑ k,‖Q k a‖) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (norm_sum_le _ _) (taylorGeneratorWeight_nonneg r a))
    _ = _ := by simp only [Finset.mul_sum];exact Finset.sum_comm

lemma flatRaisingScalarCoefficients_weighted_bound (Q0 : SmoothCoefficientJets 2) (i : I) (r : ℝ) :
    (∑ a,taylorGeneratorWeight r a*‖flatRaisingScalarCoefficients Q0 i a‖) ≤
      4*firstErrorScalarFixedBudget Q0 := by
  let J := firstErrorScalarFixedBudget Q0
  have hC := (firstErrorScalarFixedBudget_bounds Q0).2.2.1
  have hR (k j : I) : ‖if j=i then -(smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k)) else 0‖=
      if j=i then ‖smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k)‖ else 0 := by
    by_cases hj : j=i <;> simp only [hj,ite_true,ite_false,norm_neg,norm_zero]
  rw [taylorGeneratorIndex_sum]
  simp only [flatRaisingScalarCoefficients,taylorGeneratorWeight,norm_zero,mul_zero,zero_add,one_mul,hR,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hSum : (∑ k : I,‖smoothCoefficientClosureInclusionL 3 (coordinateScalarSmoothJet Q0 k)‖) ≤ 3*J :=
    (Finset.sum_le_sum (fun k _ => hC k)).trans_eq (by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      change (3:ℝ)*firstErrorScalarFixedBudget Q0=3*J
      rfl)
  exact (add_le_add (hC i) hSum).trans_eq (by ring)
end ShrinkingSpheres
