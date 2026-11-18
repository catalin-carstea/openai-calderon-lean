import Proof.FirstErrorScalarCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily

/-- Shared radius-weight bookkeeping for the three native generator kinds. -/
lemma weighted_taylor_coefficient_norm_sum
    (f : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (r A BV BB BQ J : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hA : 0 ≤ A)
    (hBV : 0 ≤ BV) (hBB : 0 ≤ BB) (hBQ : 0 ≤ BQ) (hJ : 0 ≤ J)
    (hT : ‖f .taylor‖ ≤ r⁻¹*(3*J*BV*A)+(BB*A*r⁻¹)*J+r⁻¹*(3*J*BQ*A*r^2))
    (hD : ‖f .degree‖ ≤ r⁻¹*(3*J*BQ*A*r^2))
    (hR : ∀ i j : I,‖f (.rotation i j)‖ ≤ r⁻¹*(J*(BQ*A*r^2))) :
    (∑ a,taylorGeneratorWeight r a*‖f a‖) ≤ J*(3*BV+BB+15*BQ)*A*r := by
  have hRS : (∑ i : I,∑ j : I,‖f (.rotation i j)‖) ≤
      9*(r⁻¹*(J*(BQ*A*r^2))) := by
    calc
      _ ≤ ∑ i : I,∑ j : I,r⁻¹*(J*(BQ*A*r^2)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hR i j))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  rw [taylorGeneratorIndex_sum]
  simp only [taylorGeneratorWeight,one_mul]
  calc
    _ ≤ r^2*(r⁻¹*(3*J*BV*A)+(BB*A*r⁻¹)*J+r⁻¹*(3*J*BQ*A*r^2))+
      r⁻¹*(3*J*BQ*A*r^2)+9*(r⁻¹*(J*(BQ*A*r^2))) := by
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hT (sq_nonneg _)) hD) hRS
    _ = J*(3*BV+BB+12*BQ)*A*r+(3*J*BQ*A)*r^3 := by field_simp [hr.ne'];ring
    _ ≤ _ := by
      have hr2 : r^2 ≤ r := by nlinarith
      have hr3 : r^3 ≤ r := (show r^3 ≤ r^2 by nlinarith [mul_le_mul_of_nonneg_left hr1 (sq_nonneg r)]).trans hr2
      have hh := mul_le_mul_of_nonneg_left hr3 (show 0 ≤ 3*J*BQ*A by positivity)
      nlinarith only [hh]
end ShrinkingSpheres
