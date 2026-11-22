/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-! From Proof/TauCeti/LinearAlgebra/Matrix/ToQuadraticForm.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 






















public section

open QuadraticMap

namespace Matrix

variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

 
theorem toQuadraticForm'_apply (A : Matrix ι ι R) (x : ι → R) :
    A.toQuadraticForm' x = x ⬝ᵥ A *ᵥ x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

 
@[simp]
theorem toQuadraticForm'_smul (c : R) (A : Matrix ι ι R) :
    (c • A).toQuadraticForm' = c • A.toQuadraticForm' := by
  simp [Matrix.toQuadraticForm']

 
 
 
theorem toQuadraticForm'_transpose (A : Matrix ι ι R) :
    (Aᵀ).toQuadraticForm' = A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, toQuadraticForm'_apply, ← vecMul_transpose, transpose_transpose,
    dotProduct_comm, dotProduct_mulVec]

 
theorem toQuadraticForm'_add_transpose (A : Matrix ι ι R) :
    (A + Aᵀ).toQuadraticForm' = (2 : R) • A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, _root_.smul_apply, smul_eq_mul, toQuadraticForm'_apply,
    add_mulVec, dotProduct_add, ← toQuadraticForm'_apply, ← toQuadraticForm'_apply,
    toQuadraticForm'_transpose]
  ring

 
@[simp]
theorem toQuadraticForm'_neg (A : Matrix ι ι R) :
    (-A).toQuadraticForm' = -A.toQuadraticForm' := by
  ext x
  rw [toQuadraticForm'_apply, _root_.neg_apply, toQuadraticForm'_apply, neg_mulVec,
    dotProduct_neg]

 
theorem toQuadraticForm'_diagonal (d : ι → R) :
    (diagonal d).toQuadraticForm' = weightedSumSquares R d := by
  ext x
  rw [toQuadraticForm'_apply, weightedSumSquares_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal, smul_eq_mul]
  ring

 

@[expose] noncomputable def isometryEquivCongr {P : Matrix ι ι R} (hP : IsUnit P.det) (A : Matrix ι ι R) :
    (P * A * Pᵀ).toQuadraticForm'.IsometryEquiv A.toQuadraticForm' where
  toLinearEquiv :=
    { toFun := fun x => Pᵀ *ᵥ x
      map_add' := fun x y => by rw [mulVec_add]
      map_smul' := fun c x => by rw [mulVec_smul, RingHom.id_apply]
      invFun := fun x => (Pᵀ)⁻¹ *ᵥ x
      left_inv := fun x => by
        dsimp only
        rw [mulVec_mulVec, nonsing_inv_mul _ (by rwa [det_transpose]), one_mulVec]
      right_inv := fun x => by
        dsimp only
        rw [mulVec_mulVec, mul_nonsing_inv _ (by rwa [det_transpose]), one_mulVec] }
  map_app' x := by
    have h₁ : (P * A * Pᵀ) *ᵥ x = P *ᵥ A *ᵥ Pᵀ *ᵥ x := by
      rw [mulVec_mulVec, mulVec_mulVec, mul_assoc]
    have h₂ : x ⬝ᵥ P *ᵥ A *ᵥ Pᵀ *ᵥ x = (x ᵥ* P) ⬝ᵥ A *ᵥ Pᵀ *ᵥ x := dotProduct_mulVec _ _ _
    dsimp only
    rw [toQuadraticForm'_apply, toQuadraticForm'_apply, h₁, h₂, mulVec_transpose]

 

@[expose] def isometryEquivFromBlocks (A : Matrix ι ι R) (B : Matrix κ κ R) :
    (fromBlocks A 0 0 B).toQuadraticForm'.IsometryEquiv
      (A.toQuadraticForm'.prod B.toQuadraticForm') where
  toLinearEquiv :=
    { toFun := fun x => (fun i => x (Sum.inl i), fun j => x (Sum.inr j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p => Sum.elim p.1 p.2
      left_inv := fun x => funext fun p => by cases p <;> rfl
      right_inv := fun _ => rfl }
  map_app' x := by
    have hx : Sum.elim (fun i => x (Sum.inl i)) (fun j => x (Sum.inr j)) = x :=
      funext fun p => by cases p <;> rfl
    rw [QuadraticMap.prod_apply, toQuadraticForm'_apply, toQuadraticForm'_apply,
      toQuadraticForm'_apply, ← hx, fromBlocks_mulVec]
    simp [sumElim_dotProduct_sumElim]

 

@[expose] def isometryEquivReindex (e : ι ≃ κ) (A : Matrix ι ι R) :
    (reindex e e A).toQuadraticForm'.IsometryEquiv A.toQuadraticForm' where
  toLinearEquiv := LinearEquiv.funCongrLeft R R e
  map_app' x := by
    rw [toQuadraticForm'_apply, toQuadraticForm'_apply, reindex_apply, submatrix_mulVec_equiv,
      ← comp_equiv_dotProduct_comp_equiv (e := e)]
    simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    rfl

end Matrix
