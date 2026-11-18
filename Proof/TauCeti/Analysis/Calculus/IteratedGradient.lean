/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
 
import Mathlib.Analysis.Calculus.ContDiff.Comp

 






























public section

noncomputable section

namespace TauCeti

open scoped ContDiff

universe u

 
structure IteratedGradientModel : Type (u + 1) where
   
  Space : Type u
   
  [normedAddCommGroup : NormedAddCommGroup Space]
   
  [normedSpace : NormedSpace ℝ Space]

 
@[reducible, expose] noncomputable def iteratedGradientModel (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : ℕ → IteratedGradientModel.{u}
  | 0 => { Space := E }
  | j + 1 =>
      let S := iteratedGradientModel E j
      letI : NormedAddCommGroup S.Space := S.normedAddCommGroup
      letI : NormedSpace ℝ S.Space := S.normedSpace
      { Space := E →L[ℝ] S.Space }

 


abbrev IteratedGradient (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) : Type u :=
  (iteratedGradientModel E j).Space

section IteratedGradient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable instance (j : ℕ) : NormedAddCommGroup (IteratedGradient E j) :=
  (iteratedGradientModel E j).normedAddCommGroup

noncomputable instance (j : ℕ) : NormedSpace ℝ (IteratedGradient E j) :=
  (iteratedGradientModel E j).normedSpace

noncomputable instance [CompleteSpace E] (j : ℕ) : CompleteSpace (IteratedGradient E j) := by
  induction j with
  | zero => exact inferInstance
  | succ j ih =>
      let _ : CompleteSpace (IteratedGradient E j) := ih
      exact inferInstance

end IteratedGradient

section IteratedGradientChain

variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

 


noncomputable def iteratedGradientChain (f : F → ℝ) :
    (j : ℕ) → F → IteratedGradient F j
  | 0 => fun x => gradient f x
  | j + 1 => fderiv ℝ (iteratedGradientChain f j)

@[simp]
theorem iteratedGradientChain_zero (f : F → ℝ) :
    iteratedGradientChain f 0 = gradient f :=
  (rfl)

@[simp]
theorem iteratedGradientChain_succ (f : F → ℝ) (j : ℕ) :
    iteratedGradientChain f (j + 1) = fderiv ℝ (iteratedGradientChain f j) :=
  (rfl)

 

theorem contDiffAt_iteratedGradientChain {f : F → ℝ} {x : F} {m n : ℕ∞ω}
    (hf : ContDiffAt ℝ n f x) (j : ℕ) (h : m + j + 1 ≤ n) :
    ContDiffAt ℝ m (iteratedGradientChain f j) x := by
  induction j generalizing m with
  | zero =>
      rw [iteratedGradientChain_zero]
      exact (InnerProductSpace.toDual ℝ F).symm.contDiff.contDiffAt.comp x
        (hf.fderiv_right (by simpa using h))
  | succ j ih =>
      rw [iteratedGradientChain_succ]
      have hs := ih (m := m + 1) (by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using h)
      exact hs.fderiv_right le_rfl

 

theorem tsupport_iteratedGradientChain_subset (f : F → ℝ) (j : ℕ) :
    tsupport (iteratedGradientChain f j) ⊆ tsupport f := by
  induction j with
  | zero =>
      rw [iteratedGradientChain_zero]
      exact (tsupport_comp_subset (map_zero (InnerProductSpace.toDual ℝ F).symm) _).trans
        (tsupport_fderiv_subset ℝ)
  | succ j ih =>
      rw [iteratedGradientChain_succ]
      exact (tsupport_fderiv_subset ℝ).trans ih

 

theorem hasCompactSupport_iteratedGradientChain {f : F → ℝ} (hf : HasCompactSupport f) :
    ∀ j, HasCompactSupport (iteratedGradientChain f j)
  | 0 => by
      rw [iteratedGradientChain_zero]
      exact (hf.fderiv ℝ).comp_left (map_zero _)
  | j + 1 => by
      rw [iteratedGradientChain_succ]
      exact (hasCompactSupport_iteratedGradientChain hf j).fderiv ℝ

end IteratedGradientChain

end TauCeti
