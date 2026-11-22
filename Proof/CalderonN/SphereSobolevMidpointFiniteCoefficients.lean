module

public import Proof.CalderonN.SphereSobolevMidpointCompatibility

/-! From the Proposition 5.3 release f308cb9d, Proof/Archive/SphereSobolevMidpointFiniteCoefficients.lean. -/

public section

set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace CalderonN
open OAI.AnisotropicCalderon.SphereHarmonic

variable {dim : ℕ} [NeZero dim]

lemma sphereSobolev_eq_sum_lp_single_of_zero (s : ℝ) (u : SphereSobolev dim s)
    (S : Finset ℕ) (hu : ∀ k ∉ S, u k = 0) :
    u = ∑ k ∈ S, lp.single (E := fun j => ↥(harmonicSphereSubspace dim j)) 2 k (u k) := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_sum,lp.coeFn_single,Finset.sum_apply,Finset.sum_pi_single]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
  · rw [ite_eq_right (fun h => absurd h hk),hu k hk]

lemma sphereSobolev_eq_sum_lp_single_of_finiteSupport
    (s : ℝ) (u : SphereSobolev dim s) (n : ℕ)
    (hu : ∀ k : ℕ, n ≤ k → sphereSobolevCoefficientL s k u = 0)
    (S : Finset ℕ) (hS : Finset.range n ⊆ S) :
    u = ∑ k ∈ S, lp.single (E := fun j => ↥(harmonicSphereSubspace dim j)) 2 k (u k) := by
  apply sphereSobolev_eq_sum_lp_single_of_zero s u S
  intro k hk
  have hnk : n ≤ k := by
    by_contra hn
    exact hk (hS (Finset.mem_range.mpr (lt_of_not_ge hn)))
  rw [← sphereSobolevCoefficientL_reconstruct s k u,hu k hnk,smul_zero]

lemma sphereSobolev_midpoint_coefficient_finite_sum
    (T0 : SphereSobolev dim (1/2 : ℝ) →L[ℝ] SphereSobolev dim (-1/2 : ℝ))
    (u : SphereSobolev dim 1) (S : Finset ℕ)
    (hu : u = ∑ k ∈ S, lp.single (E := fun j => ↥(harmonicSphereSubspace dim j)) 2 k (u k))
    (i : ℕ) :
    sphereSobolevCoefficientL (-1/2 : ℝ) i
      (T0 (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) u)) =
      ∑ j ∈ S, (besselWeight (1/2 : ℝ) i/besselWeight (1/2 : ℝ) j) •
        (T0 (lp.single (E := fun k => ↥(harmonicSphereSubspace dim k)) 2 j (u j))) i := by
  rw [sphereSobolevCoefficientL_apply]
  conv_lhs => rw [hu]
  simp only [map_sum,sphereSobolevInclusionL_lp_single,map_smul,
    lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have hn : ((1/2 : ℝ)-1) = -(1/2 : ℝ) := by norm_num
  rw [show -(-1/2 : ℝ)=(1/2 : ℝ) by norm_num,hn]
  unfold besselWeight
  rw [Real.rpow_neg (by positivity : 0 ≤ 1+(j:ℝ)),div_eq_mul_inv]
  simp only [div_eq_mul_inv]

end CalderonN
