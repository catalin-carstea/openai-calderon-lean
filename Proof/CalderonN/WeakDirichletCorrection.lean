module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.Normed.Operator.Bilinear

import Mathlib.Tactic

/-! The weak Poisson correction on a closed zero-Dirichlet subspace.
This is the dimension-independent part of the released weak Poisson
operator construction. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CalderonN

open ContinuousLinearMap
open scoped InnerProductSpace

variable {H Z F : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Weak energy restricted to zero-Dirichlet inputs and tests. -/
def zeroDirichletEnergy (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ) :=
  E.bilinearComp j j

omit [CompleteSpace Z] in
theorem zeroDirichletEnergy_apply (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ) (u v : Z) :
    zeroDirichletEnergy j E u v = E (j u) (j v) := by
  unfold zeroDirichletEnergy
  rw [bilinearComp_apply]

/-- Correct an arbitrary Dirichlet lift by the Lax–Milgram solution of the
negative residual on zero-Dirichlet tests. -/
def weakDirichletCorrectionL (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P0 : F →L[ℝ] H) : F →L[ℝ] Z :=
  -(hE.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    ((InnerProductSpace.toDual ℝ Z).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (E.bilinearComp P0 j)))

theorem weakDirichletCorrectionL_equation (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P0 : F →L[ℝ] H) (f : F) (v : Z) :
    E (j (weakDirichletCorrectionL j E hE P0 f)) (j v) = -E (P0 f) (j v) := by
  rw [← zeroDirichletEnergy_apply, ← hE.continuousLinearEquivOfBilin_apply]
  unfold weakDirichletCorrectionL
  simp only [neg_apply,comp_apply,ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    map_neg, ContinuousLinearEquiv.apply_symm_apply, inner_neg_left]
  congr 1
  rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply, bilinearComp_apply]

/-- The corrected lift solves the weak homogeneous equation. -/
def weakDirichletPoissonL (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P0 : F →L[ℝ] H) : F →L[ℝ] H :=
  P0+j.comp (weakDirichletCorrectionL j E hE P0)

theorem weakDirichletPoissonL_equation (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P0 : F →L[ℝ] H) (f : F) (v : Z) :
    E (weakDirichletPoissonL j E hE P0 f) (j v) = 0 := by
  unfold weakDirichletPoissonL
  simp only [add_apply, comp_apply, map_add]
  rw [weakDirichletCorrectionL_equation, add_neg_cancel]

theorem weakDirichletPoissonL_sub (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P0 : F →L[ℝ] H) :
    weakDirichletPoissonL j E hE P0-P0 = j.comp (weakDirichletCorrectionL j E hE P0) := by
  unfold weakDirichletPoissonL
  abel

theorem eq_weakDirichletPoissonL_of_equation (j : Z →L[ℝ] H) (E : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P0 : F →L[ℝ] H) (f : F) (u : H)
    (hDiff : ∃ w : Z, u-P0 f = j w) (hu : ∀ v : Z, E u (j v) = 0) :
    u = weakDirichletPoissonL j E hE P0 f := by
  obtain ⟨w, hw⟩ := hDiff
  have hu' : u = P0 f + j w := by rw [← hw]; abel
  have hZ (v : Z) : E (j w) (j v) = -E (P0 f) (j v) := by
    have he := hu v
    rw [hu', map_add, add_apply] at he
    linarith only [he]
  have hW : w = weakDirichletCorrectionL j E hE P0 f := by
    apply hE.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [hE.continuousLinearEquivOfBilin_apply, hE.continuousLinearEquivOfBilin_apply,
      zeroDirichletEnergy_apply, zeroDirichletEnergy_apply, hZ, weakDirichletCorrectionL_equation]
  rw [hu', hW, weakDirichletPoissonL, add_apply, comp_apply]

/-- Uniform weak ellipticity controls the lift perturbation in the native
first-order norm by the difference between the two coefficient energies. -/
theorem norm_weakDirichletPoissonL_sub_le
    (j : Z →L[ℝ] H) (hj : ‖j‖ ≤ 1) (E E0 : H →L[ℝ] H →L[ℝ] ℝ)
    (hE : IsCoercive (zeroDirichletEnergy j E)) (P0 : F →L[ℝ] H)
    (hP0 : ∀ f v, E0 (P0 f) (j v) = 0)
    (α : ℝ) (hα : 0 < α) (hCoer : ∀ v, α * ‖v‖ * ‖v‖ ≤ E (j v) (j v)) :
    ‖weakDirichletPoissonL j E hE P0-P0‖ ≤ α⁻¹ * ‖E-E0‖ * ‖P0‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [weakDirichletPoissonL_sub, comp_apply]
  let w := weakDirichletCorrectionL j E hE P0 f
  change ‖j w‖ ≤ _
  have hjw : ‖j w‖ ≤ ‖w‖ := (j.le_opNorm w).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (norm_nonneg w))
  refine hjw.trans ?_
  by_cases h : w = 0
  · rw [h, norm_zero]
    positivity
  have hw := norm_pos_iff.mpr h
  have hR : E (j w) (j w) = -(E-E0) (P0 f) (j w) := by
    change E (j (weakDirichletCorrectionL j E hE P0 f)) (j w) = _
    rw [weakDirichletCorrectionL_equation, sub_apply, sub_apply, hP0, sub_zero]
  have hh : α * ‖w‖ * ‖w‖ ≤ (‖E-E0‖ * (‖P0‖ * ‖f‖)) * ‖w‖ :=
    (hCoer w).trans (by
      rw [hR]
      refine (neg_le_abs _).trans (((E-E0).le_opNorm₂ _ _).trans ?_)
      gcongr
      exact P0.le_opNorm f)
  have hh' := (mul_le_mul_iff_of_pos_right hw).mp hh
  have hl := mul_le_mul_of_nonneg_left hh' (inv_nonneg.mpr hα.le)
  rw [← mul_assoc, inv_mul_cancel₀ hα.ne', one_mul] at hl
  exact hl.trans_eq (by ring)

end CalderonN
