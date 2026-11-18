/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.PDE.EnergyForm.Basic

 

































public section

namespace TauCeti

namespace PDE

open Matrix

variable {n : Type*} [Fintype n]

 
noncomputable local instance symmetricEnergyDecidableEq : DecidableEq n := Classical.decEq n

 
lemma energyIntegrand_zero_drift_transpose_apply (A : Matrix n n ℝ) (c : ℝ)
    (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand Aᵀ 0 c U V = energyIntegrand A 0 c V U := by
  rw [energyIntegrand_apply, energyIntegrand_apply, matrixBilinearForm_transpose_apply]
  simp [driftForm_apply, massForm_apply, mul_comm, mul_left_comm]

 
lemma energyIntegrand_zero_drift_comm_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm)
    (c : ℝ) (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A 0 c U V = energyIntegrand A 0 c V U := by
  calc
    energyIntegrand A 0 c U V = energyIntegrand Aᵀ 0 c U V := by rw [hA.eq]
    _ = energyIntegrand A 0 c V U := energyIntegrand_zero_drift_transpose_apply A c U V

 






@[simp]
lemma energyIntegrand_zero_drift_flip_eq_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) (c : ℝ) :
    (energyIntegrand A 0 c).flip = energyIntegrand A 0 c := by
  apply ContinuousLinearMap.ext
  intro U
  apply ContinuousLinearMap.ext
  intro V
  exact energyIntegrand_zero_drift_comm_of_isSymm hA c V U

 

lemma energyIntegrand_coefficientSymmetricPart_zero_drift_apply (A : Matrix n n ℝ)
    (c : ℝ) (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (coefficientSymmetricPart A) 0 c U V =
      (energyIntegrand A 0 c U V + energyIntegrand A 0 c V U) / 2 := by
  rw [energyIntegrand_apply, matrixBilinearForm_coefficientSymmetricPart_apply,
    energyIntegrand_apply, energyIntegrand_apply]
  simp [driftForm_apply, massForm_apply, mul_comm, mul_left_comm]
  ring

 

lemma energyIntegrand_coefficientSymmetricPart_self (A : Matrix n n ℝ)
    (b : EuclideanSpace ℝ n) (c : ℝ) (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (coefficientSymmetricPart A) b c U U =
      energyIntegrand A b c U U := by
  classical
  rw [energyIntegrand_self, energyIntegrand_self, toQuadraticForm'_coefficientSymmetricPart]

 
@[simp]
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq (A : Matrix n n ℝ) (c : ℝ) :
    (energyIntegrand (coefficientSymmetricPart A) 0 c).flip =
      energyIntegrand (coefficientSymmetricPart A) 0 c :=
  energyIntegrand_zero_drift_flip_eq_of_isSymm (coefficientSymmetricPart_isSymm A) c

end PDE

end TauCeti
