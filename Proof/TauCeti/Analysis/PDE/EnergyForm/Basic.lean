/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.PDE.Ellipticity.Basic
public import Proof.TauCeti.Analysis.PDE.LowerOrder

 




















































public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

 
noncomputable local instance energyFormDecidableEq : DecidableEq n := Classical.decEq n

 







noncomputable def energyIntegrand (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ) :
    (ℝ × EuclideanSpace ℝ n) →L[ℝ] (ℝ × EuclideanSpace ℝ n) →L[ℝ] ℝ :=
  letI := Classical.decEq n
  (matrixBilinearForm A).flip.bilinearComp
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ n))
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ n))
    + (driftForm b).flip.bilinearComp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ n))
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ n))
    + (massForm c).bilinearComp
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ n))
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ n))

 
@[simp]
lemma energyIntegrand_apply (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ)
    (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A b c U V
      = matrixBilinearForm A V.2 U.2 + driftForm b V.1 U.2 + massForm c U.1 V.1 := by
  simp [energyIntegrand]

 
lemma energyIntegrand_self (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n)
    (c : ℝ) (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A b c U U
      = A.toQuadraticForm' U.2 + ⟪b, U.2⟫_ℝ * U.1 + c * U.1 ^ 2 := by
  rw [energyIntegrand_apply, matrixBilinearForm_self, driftForm_apply, massForm_apply]
  ring

 

lemma energyIntegrand_one_zero_zero_apply (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 0 U V = V.2 ⬝ᵥ U.2 := by
  simp [energyIntegrand_apply]

 
lemma energyIntegrand_one_zero_zero_self (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 0 U U = ‖U.2‖ ^ 2 := by
  rw [energyIntegrand_self, toQuadraticForm'_one]
  simp

 

lemma energyIntegrand_one_zero_mass_apply (c : ℝ) (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 c U V = V.2 ⬝ᵥ U.2 + c * U.1 * V.1 := by
  simp [energyIntegrand_apply, massForm_apply]

 

lemma energyIntegrand_one_zero_mass_self (c : ℝ) (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 c U U = ‖U.2‖ ^ 2 + c * U.1 ^ 2 := by
  rw [energyIntegrand_self, toQuadraticForm'_one]
  simp

variable {lam Lam beta gamma : ℝ}

 

private lemma mul_norm_abs_le_half_mul_sq_add (hlam : 0 < lam) (beta u : ℝ) (r : ℝ) :
    beta * r * |u| ≤ lam / 2 * r ^ 2 + beta ^ 2 / (2 * lam) * u ^ 2 := by
  have hkey := two_mul_le_add_sq (lam * r) (beta * |u|)
  rw [mul_pow, mul_pow, sq_abs] at hkey
  have h2lam : (0 : ℝ) < 2 * lam := mul_pos two_pos hlam
  rw [← sub_nonneg]
  have expand : lam / 2 * r ^ 2 + beta ^ 2 / (2 * lam) * u ^ 2 - beta * r * |u|
      = (lam ^ 2 * r ^ 2 + beta ^ 2 * u ^ 2 - 2 * lam * beta * r * |u|)
          / (2 * lam) := by
    field_simp
  rw [expand]
  apply div_nonneg _ h2lam.le
  nlinarith [hkey]

private lemma abs_dotProduct_one_mulVec_le (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ ξ)| ≤ 1 * ‖η‖ * ‖ξ‖ := by
  rw [one_mulVec, one_mul]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    abs_real_inner_le_norm η ξ

 


lemma norm_energyIntegrand_apply_le_of_bounds (hLam : 0 ≤ Lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (ha : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb : ‖b₀‖ ≤ beta) (hc : ‖c₀‖ ≤ gamma) (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand A b₀ c₀ U V‖ ≤ (Lam + beta + gamma) * ‖U‖ * ‖V‖ := by
   
  have step : ∀ {K p q : ℝ}, 0 ≤ K → 0 ≤ p → p ≤ ‖U‖ → q ≤ ‖V‖ →
      K * p * q ≤ K * ‖U‖ * ‖V‖ := fun hK hp hpU hqV =>
    (mul_le_mul_of_nonneg_left hqV (mul_nonneg hK hp)).trans (by gcongr)
  have hbeta : 0 ≤ beta := (norm_nonneg b₀).trans hb
  have hgamma : 0 ≤ gamma := (norm_nonneg c₀).trans hc
  have hmat : ‖matrixBilinearForm A V.2 U.2‖ ≤ Lam * ‖U‖ * ‖V‖ := by
    have h := norm_matrixBilinearForm_le_of_upper_bound A ha V.2 U.2
    rw [mul_right_comm] at h
    exact h.trans (step hLam (norm_nonneg _) (norm_snd_le U) (norm_snd_le V))
  have hdrift : ‖driftForm b₀ V.1 U.2‖ ≤ beta * ‖U‖ * ‖V‖ := by
    rw [driftForm_apply, norm_mul]
    calc
      ‖⟪b₀, U.2⟫_ℝ‖ * ‖V.1‖ ≤ (‖b₀‖ * ‖U.2‖) * ‖V.1‖ := by
        gcongr
        exact norm_inner_le_norm b₀ U.2
      _ ≤ (beta * ‖U.2‖) * ‖V.1‖ := by
        gcongr
      _ = beta * ‖U.2‖ * ‖V.1‖ := by ring
      _ ≤ beta * ‖U‖ * ‖V‖ :=
        step hbeta (norm_nonneg _) (norm_snd_le U) (norm_fst_le V)
  have hmass : ‖massForm c₀ U.1 V.1‖ ≤ gamma * ‖U‖ * ‖V‖ := by
    rw [massForm_apply, norm_mul, norm_mul]
    calc
      ‖c₀‖ * ‖U.1‖ * ‖V.1‖ ≤ gamma * ‖U.1‖ * ‖V.1‖ := by
        gcongr
      _ ≤ gamma * ‖U‖ * ‖V‖ :=
        step hgamma (norm_nonneg _) (norm_fst_le U) (norm_fst_le V)
  rw [energyIntegrand_apply]
  calc ‖matrixBilinearForm A V.2 U.2 + driftForm b₀ V.1 U.2 + massForm c₀ U.1 V.1‖
      ≤ ‖matrixBilinearForm A V.2 U.2 + driftForm b₀ V.1 U.2‖
          + ‖massForm c₀ U.1 V.1‖ := norm_add_le _ _
    _ ≤ ‖matrixBilinearForm A V.2 U.2‖ + ‖driftForm b₀ V.1 U.2‖
          + ‖massForm c₀ U.1 V.1‖ := by gcongr; exact norm_add_le _ _
    _ ≤ Lam * ‖U‖ * ‖V‖ + beta * ‖U‖ * ‖V‖ + gamma * ‖U‖ * ‖V‖ :=
        add_le_add (add_le_add hmat hdrift) hmass
    _ = (Lam + beta + gamma) * ‖U‖ * ‖V‖ := by ring

 



lemma opNorm_energyIntegrand_le_of_bounds (hLam : 0 ≤ Lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (ha : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb : ‖b₀‖ ≤ beta) (hc : ‖c₀‖ ≤ gamma) :
    ‖energyIntegrand A b₀ c₀‖ ≤ Lam + beta + gamma := by
  have hbeta : 0 ≤ beta := (norm_nonneg b₀).trans hb
  have hgamma : 0 ≤ gamma := (norm_nonneg c₀).trans hc
  refine (energyIntegrand A b₀ c₀).opNorm_le_bound₂
    (_root_.add_nonneg (_root_.add_nonneg hLam hbeta) hgamma) ?_
  intro U V
  exact norm_energyIntegrand_apply_le_of_bounds hLam ha hb hc U V

 
lemma norm_energyIntegrand_one_zero_mass_apply_le (c : ℝ) (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand (1 : Matrix n n ℝ) 0 c U V‖ ≤
      (1 + ‖c‖) * ‖U‖ * ‖V‖ := by
  simpa using
    norm_energyIntegrand_apply_le_of_bounds (n := n) (Lam := 1) (beta := 0) (b₀ := 0)
      (gamma := ‖c‖) zero_le_one
      (fun η ξ => abs_dotProduct_one_mulVec_le η ξ) (by simp) le_rfl U V

 
lemma opNorm_energyIntegrand_one_zero_mass_le (c : ℝ) :
    ‖energyIntegrand (1 : Matrix n n ℝ) 0 c‖ ≤ 1 + ‖c‖ := by
  simpa using
    opNorm_energyIntegrand_le_of_bounds (n := n) (Lam := 1) (beta := 0) (b₀ := 0)
      (gamma := ‖c‖) zero_le_one
      (fun η ξ => abs_dotProduct_one_mulVec_le η ξ) (by simp) le_rfl

 

lemma garding_energyIntegrand_self_of_bounds_with_parameter {eps : ℝ} (heps : 0 < eps)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hQ : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : 0 ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    (lam - eps) * ‖U.2‖ ^ 2 - beta ^ 2 / (4 * eps) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  rw [energyIntegrand_self]
  have hQ' : lam * ‖U.2‖ ^ 2 ≤ A.toQuadraticForm' U.2 := hQ U.2
  have hM : 0 ≤ c₀ * U.1 ^ 2 := mul_nonneg hc (sq_nonneg _)
  have hbip : |⟪b₀, U.2⟫_ℝ| ≤ beta * ‖U.2‖ :=
    (abs_real_inner_le_norm b₀ U.2).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hD : -(beta * ‖U.2‖ * |U.1|) ≤ ⟪b₀, U.2⟫_ℝ * U.1 := by
    have habs : |⟪b₀, U.2⟫_ℝ * U.1| ≤ beta * ‖U.2‖ * |U.1| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hbip (abs_nonneg _)
    have := neg_abs_le (⟪b₀, U.2⟫_ℝ * U.1)
    linarith
  have hYoung : beta * ‖U.2‖ * |U.1| ≤
      eps * ‖U.2‖ ^ 2 + beta ^ 2 / (4 * eps) * U.1 ^ 2 := by
    convert mul_norm_abs_le_half_mul_sq_add (mul_pos two_pos heps) beta U.1 ‖U.2‖ using 1
    ring
  nlinarith [hQ', hM, hD, hYoung]

 




lemma garding_energyIntegrand_self_of_bounds (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hQ : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : 0 ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  convert garding_energyIntegrand_self_of_bounds_with_parameter (half_pos hlam) hQ hb hc U
    using 1
  ring

end PDE

end TauCeti
