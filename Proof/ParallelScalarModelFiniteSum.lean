import Proof.ParallelScalarFirstTripleIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy

lemma scalar_model_finite_integral_sum_bound {ι : Type*} [Fintype ι]
    (Y : Set X) (r C : ℝ) (f : ι → X → ℝ)
    (hI : ∀ i,IntegrableOn (f i) Y) (hB : ∀ i,|r*(∫ y in Y,f i y)| ≤ C) :
    IntegrableOn (fun y => ∑ i,f i y) Y ∧
      |r*(∫ y in Y,∑ i,f i y)| ≤ (Fintype.card ι:ℝ)*C := by
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hI i),?_⟩
  rw [integral_finsetSum Finset.univ (f:=f) (fun i _ => hI i),Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => hB i)).trans_eq
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]))

end ShrinkingSpheres.ParallelEnergy
