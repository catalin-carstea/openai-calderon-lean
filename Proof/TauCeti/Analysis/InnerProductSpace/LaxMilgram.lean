/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

 





























public section

noncomputable section

open scoped InnerProductSpace

namespace IsCoercive

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

 
theorem apply_self_nonneg (hB : IsCoercive B) (v : V) : 0 ≤ B v v := by
  obtain ⟨C, hC, hle⟩ := id hB
  refine le_trans ?_ (hle v)
  positivity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

 



def solutionOfInner (hB : IsCoercive B) (F : V) : V :=
  hB.continuousLinearEquivOfBilin.symm F

 
theorem solutionOfInner_def (hB : IsCoercive B) (F : V) :
    solutionOfInner hB F = hB.continuousLinearEquivOfBilin.symm F :=
  by simp [solutionOfInner]

 

@[simp]
theorem continuousLinearEquivOfBilin_solutionOfInner (hB : IsCoercive B) (F : V) :
    hB.continuousLinearEquivOfBilin (solutionOfInner hB F) = F := by
  simp [solutionOfInner]

 

@[simp]
theorem solutionOfInner_continuousLinearEquivOfBilin (hB : IsCoercive B) (u : V) :
    solutionOfInner hB (hB.continuousLinearEquivOfBilin u) = u := by
  simp [solutionOfInner]

 
@[simp]
theorem apply_solutionOfInner_eq_inner (hB : IsCoercive B) (F v : V) :
    B (solutionOfInner hB F) v = ⟪F, v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  simp [solutionOfInner]

 
theorem eq_solutionOfInner (hB : IsCoercive B) {F u : V} (hu : ∀ v : V, B u v = ⟪F, v⟫_ℝ) :
    u = solutionOfInner hB F := by
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hB.continuousLinearEquivOfBilin_apply, hu]
  simp [solutionOfInner]

 



theorem existsUnique_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃! u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  ⟨solutionOfInner hB F, apply_solutionOfInner_eq_inner hB F,
    fun _ hu => eq_solutionOfInner hB hu⟩

 
theorem exists_forall_eq_inner (hB : IsCoercive B) (F : V) :
    ∃ u : V, ∀ v : V, B u v = ⟪F, v⟫_ℝ :=
  (existsUnique_forall_eq_inner hB F).exists

 


def solutionOfFunctional (hB : IsCoercive B) (ℓ : StrongDual ℝ V) : V :=
  solutionOfInner hB ((InnerProductSpace.toDual ℝ V).symm ℓ)

 
theorem solutionOfFunctional_def (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    solutionOfFunctional hB ℓ =
      solutionOfInner hB ((InnerProductSpace.toDual ℝ V).symm ℓ) :=
  by simp [solutionOfFunctional]

 
@[simp]
theorem solutionOfFunctional_toDual (hB : IsCoercive B) (F : V) :
    solutionOfFunctional hB ((InnerProductSpace.toDual ℝ V) F) = solutionOfInner hB F := by
  simp [solutionOfFunctional]

 

@[simp]
theorem apply_solutionOfFunctional_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) (v : V) :
    B (solutionOfFunctional hB ℓ) v = ℓ v := by
  rw [solutionOfFunctional, apply_solutionOfInner_eq_inner, InnerProductSpace.toDual_symm_apply]

 

theorem eq_solutionOfFunctional (hB : IsCoercive B) {ℓ : StrongDual ℝ V} {u : V}
    (hu : ∀ v : V, B u v = ℓ v) :
    u = solutionOfFunctional hB ℓ := by
  apply eq_solutionOfInner hB
  intro v
  rw [hu, InnerProductSpace.toDual_symm_apply]

 

theorem existsUnique_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃! u : V, ∀ v : V, B u v = ℓ v :=
  ⟨solutionOfFunctional hB ℓ, apply_solutionOfFunctional_eq hB ℓ,
    fun _ hu => eq_solutionOfFunctional hB hu⟩

 
theorem exists_forall_eq (hB : IsCoercive B) (ℓ : StrongDual ℝ V) :
    ∃ u : V, ∀ v : V, B u v = ℓ v :=
  (existsUnique_forall_eq hB ℓ).exists

end IsCoercive
