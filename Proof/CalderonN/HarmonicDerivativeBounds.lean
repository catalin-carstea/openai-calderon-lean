module

public import Proof.CalderonN.HarmonicDerivativeOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint

import Mathlib.Tactic

@[expose] public section

noncomputable section
open MvPolynomial
open scoped InnerProductSpace

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial

variable {n : ℕ} [NeZero n]

lemma sum_norm_sq_polynomialDerivative (hF : SphereFischerInner n) (m : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n (m+1)) :
    (∑ i : Fin n, ‖polynomialSphereL2 (pderiv i p)‖^2) =
      (((m:ℝ)+1)*((n:ℝ)+2*(m:ℝ))) * ‖polynomialSphereL2 p‖^2 := by
  simp_rw [polynomialSphereL2_norm_sq hF m _
    (pderiv_harmonicHomogeneous_succ m _ p hp)]
  rw [polynomialSphereL2_norm_sq hF (m+1) p hp]
  unfold normalizedFischerSquare normalizedFischerInner
  rw [← Finset.sum_div,sum_fischerInner_pderiv_self hp.1,
    sphereNormalization_succ]
  have hN : sphereNormalization n m ≠ 0 :=
    ne_of_gt (sphereNormalization_pos (NeZero.pos n) m)
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hc : (n:ℝ)+2*(m:ℝ) ≠ 0 := by positivity
  field_simp [hN,hc]
  <;> ring

lemma sum_norm_sq_harmonicDerivative (hF : SphereFischerInner n) (m : ℕ)
    (u : harmonicSphereSubspace n (m+1)) :
    (∑ i : Fin n, ‖harmonicDerivative hF m i u‖^2) =
      (((m:ℝ)+1)*((n:ℝ)+2*(m:ℝ))) * ‖u‖^2 := by
  rcases harmonicPolynomialSphereMap_surjective (m+1) u with ⟨p,rfl⟩
  simp_rw [harmonicDerivative_apply_image]
  exact sum_norm_sq_polynomialDerivative hF m p p.property

attribute [local irreducible] harmonicDerivative harmonicDerivativeAdjoint

lemma norm_harmonicDerivative_apply_le (hF : SphereFischerInner n) (m : ℕ)
    (i : Fin n) (u : harmonicSphereSubspace n (m+1)) :
    ‖harmonicDerivative hF m i u‖ ≤ (((n:ℝ)+2)*((m:ℝ)+1))*‖u‖ := by
  have hs : ‖harmonicDerivative hF m i u‖^2 ≤
      ∑ j : Fin n, ‖harmonicDerivative hF m j u‖^2 :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin n => ‖harmonicDerivative hF m j u‖^2)
      (fun j _ => sq_nonneg ‖harmonicDerivative hF m j u‖) (Finset.mem_univ i)
  rw [sum_norm_sq_harmonicDerivative] at hs
  have hc : ((m:ℝ)+1)*((n:ℝ)+2*(m:ℝ)) ≤ (((n:ℝ)+2)*((m:ℝ)+1))^2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hs : (n : ℝ) + 2 * (m : ℝ) ≤ ((n : ℝ)+2)^2 * ((m : ℝ)+1) := by
      nlinarith [mul_nonneg hn hm, mul_nonneg (sq_nonneg (n:ℝ)) hm]
    nlinarith [mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (m:ℝ)+1)]
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖u‖)
  have hn : 0 ≤ (((n:ℝ)+2)*((m:ℝ)+1))*‖u‖ := by positivity
  nlinarith [norm_nonneg (harmonicDerivative hF m i u)]

lemma norm_harmonicDerivative_le (hF : SphereFischerInner n) (m : ℕ) (i : Fin n) :
    ‖harmonicDerivative hF m i‖ ≤ ((n:ℝ)+2)*((m:ℝ)+1) := by
  apply (harmonicDerivative hF m i).opNorm_le_bound (by positivity)
  exact norm_harmonicDerivative_apply_le hF m i

lemma norm_harmonicDerivativeAdjoint_le (hF : SphereFischerInner n) (m : ℕ) (i : Fin n) :
    ‖harmonicDerivativeAdjoint hF m i‖ ≤ ((n:ℝ)+2)*((m:ℝ)+1) := by
  rw [harmonicDerivativeAdjoint_eq_adjoint,
    ContinuousLinearMap.adjoint.norm_map]
  exact norm_harmonicDerivative_le hF m i

lemma norm_harmonicDerivativeAdjoint_apply_le (hF : SphereFischerInner n) (m : ℕ)
    (i : Fin n) (u : harmonicSphereSubspace n m) :
    ‖harmonicDerivativeAdjoint hF m i u‖ ≤ (((n:ℝ)+2)*((m:ℝ)+1))*‖u‖ :=
  (harmonicDerivativeAdjoint hF m i).le_of_opNorm_le
    (norm_harmonicDerivativeAdjoint_le hF m i) u

end CalderonN
