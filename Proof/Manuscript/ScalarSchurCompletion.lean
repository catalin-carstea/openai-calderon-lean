module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic

@[expose] public section

open Matrix

namespace CalderonPaper

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Symmetric completion with prescribed positive Schur coefficients.
The last coordinate fixes the total determinant at one. -/
def schurDetOne (A : Matrix n n ℝ) (Q : Matrix n (Fin 3) ℝ) (s t : ℝ) :
    Matrix (n ⊕ Fin 3) (n ⊕ Fin 3) ℝ :=
  fromBlocks A Q Qᴴ (Qᴴ * A⁻¹ * Q + diagonal ![s, t, (A.det * s * t)⁻¹])

theorem schurDetOne_posDef_and_det (A : Matrix n n ℝ) (hA : A.PosDef)
    (Q : Matrix n (Fin 3) ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (schurDetOne A Q s t).PosDef ∧ (schurDetOne A Q s t).det = 1 := by
  let : Invertible A := invertibleOfIsUnitDet A ((isUnit_iff_isUnit_det A).mp hA.isUnit)
  let d : Fin 3 → ℝ := ![s, t, (A.det * s * t)⁻¹]
  let D := Qᴴ * A⁻¹ * Q + diagonal d
  have hD : D - Qᴴ * A⁻¹ * Q = diagonal d := add_sub_cancel_left _ _
  have hd : (diagonal d).PosDef := Matrix.posDef_diagonal_iff.mpr fun i => by
    have hApos := hA.det_pos
    fin_cases i <;> simp [d] <;> positivity
  have hdet : (schurDetOne A Q s t).det = 1 := by
    change (fromBlocks A Q Qᴴ D).det = 1
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv, hD, det_diagonal, Fin.prod_univ_three]
    change A.det * (s * t * (A.det * s * t)⁻¹) = 1
    field_simp [hA.det_pos.ne', hs.ne', ht.ne']
  have hsemi : (schurDetOne A Q s t).PosSemidef := by
    change (fromBlocks A Q Qᴴ D).PosSemidef
    apply (hA.fromBlocks₁₁ Q D).mpr
    rw [hD]
    exact hd.posSemidef
  have hu : IsUnit (schurDetOne A Q s t).det := hdet ▸ isUnit_one
  exact ⟨hsemi.posDef_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hu), hdet⟩

end
end CalderonPaper
