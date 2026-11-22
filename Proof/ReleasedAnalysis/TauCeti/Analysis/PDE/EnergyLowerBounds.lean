/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Normed.Group.Prod
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.Basic

/-! From Proof/TauCeti/Analysis/PDE/EnergyLowerBounds.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 





































public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

 
noncomputable local instance energyLowerBoundsDecidableEq : DecidableEq n := Classical.decEq n

variable {lam mu beta : ℝ}

 

lemma garding_energyIntegrand_self_of_mass_lower_bound_of_bounds_with_parameter
    {eps : ℝ} (heps : 0 < eps)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    (lam - eps) * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (4 * eps)) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hgard := garding_energyIntegrand_self_of_bounds_with_parameter heps hA hb
    (sub_nonneg.mpr hc) U
  rw [energyIntegrand_self] at hgard ⊢
  linarith

 




lemma garding_energyIntegrand_self_of_mass_lower_bound_of_bounds (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  convert garding_energyIntegrand_self_of_mass_lower_bound_of_bounds_with_parameter
    (half_pos hlam) hA hb hc U using 1
  ring

 

lemma min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hnorm := U.min_mul_norm_sq_le_add
    (a := mu - beta ^ 2 / (2 * lam)) (b := lam / 2)
    ((half_pos hlam).le.trans (le_max_right _ _))
  rw [min_comm, add_comm, Real.norm_eq_abs, sq_abs] at hnorm
  exact hnorm.trans
    (garding_energyIntegrand_self_of_mass_lower_bound_of_bounds hlam hA hb hc U)

 

lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self {A : Matrix n n ℝ}
    {c₀ : ℝ} (hlam : 0 ≤ lam) (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (U : ℝ × EuclideanSpace ℝ n) :
    min lam c₀ * ‖U‖ ^ 2 ≤ energyIntegrand A 0 c₀ U U := by
  have hprod := U.min_mul_norm_sq_le_add (a := c₀) (b := lam)
    (hlam.trans (le_max_right _ _))
  have hA' := hA U.2
  rw [energyIntegrand_self]
  simp only [inner_zero_left, zero_mul, add_zero]
  rw [min_comm, add_comm, Real.norm_eq_abs, sq_abs] at hprod
  exact hprod.trans (add_le_add hA' le_rfl)

 

lemma mul_norm_snd_sq_le_energyIntegrand_zero_drift_self {A : Matrix n n ℝ} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam * ‖U.2‖ ^ 2 ≤ energyIntegrand A 0 c₀ U U := by
  rw [energyIntegrand_self]
  simp only [inner_zero_left, zero_mul, add_zero]
  exact (hA U.2).trans (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _)))

 
lemma min_one_mass_mul_norm_sq_le_energyIntegrand_one_zero_mass_self {c : ℝ}
    (U : ℝ × EuclideanSpace ℝ n) :
    min 1 c * ‖U‖ ^ 2 ≤ energyIntegrand (1 : Matrix n n ℝ) 0 c U U :=
  min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self zero_le_one
    (by intro ξ; simp) U

end PDE

end TauCeti
