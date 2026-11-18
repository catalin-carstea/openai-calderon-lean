import Proof.TaylorScalarCoefficientCalculus
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma taylor_scalar_weighted_sum_nonneg (r : ℝ) (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3) :
    0 ≤ ∑ a,taylorGeneratorWeight r a*‖Q a‖ :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (taylorGeneratorWeight_nonneg r a) (norm_nonneg _))

lemma weighted_three_taylor_scalar_combination (r : ℝ)
    (Q : I → TaylorGeneratorIndex → ClosedCoefficientJets 3) (u : I → ℝ)
    (U B : ℝ) (hU : 0 ≤ U) (hu : ∀ i,|u i| ≤ U)
    (hQ : ∀ i,(∑ a,taylorGeneratorWeight r a*‖Q i a‖) ≤ B) :
    (∑ a,taylorGeneratorWeight r a*‖(∑ i : I,u i • Q i) a‖) ≤ 3*U*B := by
  have hSum := taylor_scalar_weighted_sum_finite_le r (fun i a => u i • Q i a)
  have hTerm (i : I) : (∑ a,taylorGeneratorWeight r a*‖u i • Q i a‖) ≤ U*B := by
    rw [taylor_scalar_weighted_sum_smul]
    exact mul_le_mul (hu i) (hQ i) (taylor_scalar_weighted_sum_nonneg r (Q i)) hU
  have hh := hSum.trans (Finset.sum_le_sum (fun i _ => hTerm i))
  simpa only [Finset.sum_apply,Pi.smul_apply,Fin.sum_univ_three] using hh.trans_eq
    (by simp only [Fin.sum_univ_three];ring : (∑ _i : I,U*B)=3*U*B)
end ShrinkingSpheres
