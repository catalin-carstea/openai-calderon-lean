/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Proof.TauCeti.Analysis.Calculus.Gradient
public import Proof.TauCeti.LinearAlgebra.Matrix.ToQuadraticForm

 





























































public section

namespace TauCeti

namespace PDE

open Matrix

 

section SymmetricPart

variable {n : Type*}

 





noncomputable def coefficientSymmetricPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

 
lemma coefficientSymmetricPart_isSymm (A : Matrix n n ℝ) : (coefficientSymmetricPart A).IsSymm :=
  (isSymm_add_transpose_self A).smul (1 / 2 : ℝ)

 
@[simp]
lemma coefficientSymmetricPart_apply (A : Matrix n n ℝ) (i j : n) :
    coefficientSymmetricPart A i j = (A i j + A j i) / 2 := by
  simp [coefficientSymmetricPart, div_eq_mul_inv, mul_comm]

 
@[simp]
lemma coefficientSymmetricPart_eq_self_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) :
    coefficientSymmetricPart A = A := by
  ext i j
  rw [coefficientSymmetricPart_apply, hA.apply i j]
  ring

end SymmetricPart

 

section BilinearForm

variable {n : Type*} [Fintype n]

 





noncomputable def matrixBilinearForm (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap
    ((Matrix.toBilin'Aux A).comp (EuclideanSpace.equiv n ℝ).toLinearEquiv.toLinearMap
      (EuclideanSpace.equiv n ℝ).toLinearEquiv.toLinearMap)

 
@[simp]
lemma matrixBilinearForm_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A η ξ = η ⬝ᵥ (A *ᵥ ξ) := by
  rw [matrixBilinearForm, LinearMap.toContinuousBilinearMap_apply, LinearMap.BilinForm.comp_apply]
  simp [Matrix.toBilin'Aux, Matrix.toLinearMap₂'Aux, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm, mul_comm]

 
lemma matrixBilinearForm_smul_apply (c : ℝ) (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (c • A) η ξ = c * matrixBilinearForm A η ξ := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, smul_mulVec, dotProduct_smul]
  simp [smul_eq_mul]

 
lemma matrixBilinearForm_add_apply (A B : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (A + B) η ξ = matrixBilinearForm A η ξ + matrixBilinearForm B η ξ := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, matrixBilinearForm_apply,
    add_mulVec, dotProduct_add]

 

lemma matrixBilinearForm_transpose_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm Aᵀ η ξ = matrixBilinearForm A ξ η := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, Matrix.dotProduct_transpose_mulVec]

 

lemma matrixBilinearForm_coefficientSymmetricPart_apply (A : Matrix n n ℝ)
    (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (coefficientSymmetricPart A) η ξ =
      (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η) / 2 := by
  rw [coefficientSymmetricPart, matrixBilinearForm_smul_apply, matrixBilinearForm_add_apply,
    matrixBilinearForm_transpose_apply]
  ring

 
noncomputable def matrixBilinearFormLinear :
    Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        matrixBilinearForm A
      map_add' := by
        intro A B
        ext η ξ
        exact matrixBilinearForm_add_apply A B η ξ
      map_smul' := by
        intro r A
        ext η ξ
        exact matrixBilinearForm_smul_apply r A η ξ }

 
@[simp]
lemma matrixBilinearFormLinear_apply (A : Matrix n n ℝ) :
    matrixBilinearFormLinear (n := n) A = matrixBilinearForm A :=
  by
    ext η ξ
    simp [matrixBilinearFormLinear]

 
lemma continuous_matrixBilinearForm :
    Continuous (fun A : Matrix n n ℝ => matrixBilinearForm A) :=
  (matrixBilinearFormLinear (n := n)).continuous.congr fun A =>
    matrixBilinearFormLinear_apply A

section Continuity

variable {X : Type*} [TopologicalSpace X]

namespace Continuous

 

lemma matrixBilinearForm {a : X → Matrix n n ℝ} (ha : Continuous a) :
    Continuous (fun x => PDE.matrixBilinearForm (a x)) :=
  continuous_matrixBilinearForm.comp ha

end Continuous

namespace ContinuousOn

 

lemma matrixBilinearForm {s : Set X} {a : X → Matrix n n ℝ} (ha : ContinuousOn a s) :
    ContinuousOn (fun x => PDE.matrixBilinearForm (a x)) s :=
  continuous_matrixBilinearForm.comp_continuousOn ha

end ContinuousOn

end Continuity

 

lemma norm_matrixBilinearForm_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
  simpa [Real.norm_eq_abs] using hA η ξ

 




lemma matrixBilinearForm_opNorm_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hLam_nonneg : 0 ≤ Lam) (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    ‖matrixBilinearForm A‖ ≤ Lam := by
  refine (matrixBilinearForm A).opNorm_le_bound₂ hLam_nonneg ?_
  intro η ξ
  exact norm_matrixBilinearForm_le_of_upper_bound A hA η ξ

 

lemma matrixBilinearForm_apply_norm_le_of_upper_bound {A : Matrix n n ℝ} {Lam R S : ℝ}
    (hLam_nonneg : 0 ≤ Lam) (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm A η ξ‖ ≤ Lam * R * S :=
  (matrixBilinearForm A).le_of_opNorm₂_le_of_le
    (matrixBilinearForm_opNorm_le_of_upper_bound A hLam_nonneg hA) hη hξ

 
lemma abs_dotProduct_add_mulVec_le {A B : Matrix n n ℝ} {Lam Mu : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hB : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (B *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((A + B) *ᵥ ξ)| ≤ (Lam + Mu) * ‖η‖ * ‖ξ‖ := by
  rw [add_mulVec, dotProduct_add]
  calc
    |η ⬝ᵥ (A *ᵥ ξ) + η ⬝ᵥ (B *ᵥ ξ)|
        ≤ |η ⬝ᵥ (A *ᵥ ξ)| + |η ⬝ᵥ (B *ᵥ ξ)| := abs_add_le _ _
    _ ≤ Lam * ‖η‖ * ‖ξ‖ + Mu * ‖η‖ * ‖ξ‖ := add_le_add (hA η ξ) (hB η ξ)
    _ = (Lam + Mu) * ‖η‖ * ‖ξ‖ := by ring

 

lemma abs_dotProduct_coefficientSymmetricPart_mulVec_le {A : Matrix n n ℝ} {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (coefficientSymmetricPart A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  classical
  rw [← matrixBilinearForm_apply, matrixBilinearForm_coefficientSymmetricPart_apply]
  have hηξ : ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
    norm_matrixBilinearForm_le_of_upper_bound A hA η ξ
  have hξη : ‖matrixBilinearForm A ξ η‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
    rw [mul_right_comm]
    exact norm_matrixBilinearForm_le_of_upper_bound A hA ξ η
  have hsum :
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
        ≤ 2 * (Lam * ‖η‖ * ‖ξ‖) := by
    calc
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
          ≤ ‖matrixBilinearForm A η ξ‖ + ‖matrixBilinearForm A ξ η‖ := norm_add_le _ _
      _ ≤ Lam * ‖η‖ * ‖ξ‖ + Lam * ‖η‖ * ‖ξ‖ := add_le_add hηξ hξη
      _ = 2 * (Lam * ‖η‖ * ‖ξ‖) := by ring
  rw [abs_div]
  rw [abs_of_pos (a := (2 : ℝ)) two_pos]
  exact (div_le_iff₀' two_pos).2 (by
    simpa [Real.norm_eq_abs] using hsum)

end BilinearForm

 

variable {X n : Type*} [Fintype n] [DecidableEq n]

 
@[simp]
lemma toQuadraticForm'_one (ξ : EuclideanSpace ℝ n) :
    (1 : Matrix n n ℝ).toQuadraticForm' ξ = ‖ξ‖ ^ 2 := by
  rw [Matrix.toQuadraticForm'_apply, one_mulVec]
  simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq ξ).symm

 
lemma matrixBilinearForm_one_apply (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (1 : Matrix n n ℝ) η ξ = η ⬝ᵥ ξ := by
  rw [matrixBilinearForm_apply, one_mulVec]

 
lemma toQuadraticForm'_smul_one (c : ℝ) (ξ : EuclideanSpace ℝ n) :
    (c • (1 : Matrix n n ℝ)).toQuadraticForm' ξ = c * ‖ξ‖ ^ 2 := by
  rw [toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul, toQuadraticForm'_one]

 
@[simp]
lemma toQuadraticForm'_add (A B : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (A + B).toQuadraticForm' ξ = A.toQuadraticForm' ξ + B.toQuadraticForm' ξ := by
  rw [Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply,
    Matrix.toQuadraticForm'_apply, add_mulVec, dotProduct_add]

 
@[simp]
lemma toQuadraticForm'_transpose (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    Aᵀ.toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply,
    Matrix.dotProduct_transpose_mulVec]

 
lemma matrixBilinearForm_smul_one_apply (c : ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (c • (1 : Matrix n n ℝ)) η ξ = c * (η ⬝ᵥ ξ) := by
  rw [matrixBilinearForm_smul_apply, matrixBilinearForm_one_apply]

 
lemma matrixBilinearForm_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A ξ ξ = A.toQuadraticForm' ξ := by
  rw [matrixBilinearForm_apply, Matrix.toQuadraticForm'_apply]

 
@[simp]
lemma toQuadraticForm'_coefficientSymmetricPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (coefficientSymmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [coefficientSymmetricPart, toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul,
    toQuadraticForm'_add, toQuadraticForm'_transpose]
  ring

 



theorem mul_sq_mul_norm_sq_le_matrixBilinearForm_add {A : Matrix n n ℝ} {lam Lam : ℝ}
    (hlam : 0 < lam) (z w : ℝ) (g q : EuclideanSpace ℝ n)
    (hlower : lam * ‖g‖ ^ 2 ≤ A.toQuadraticForm' g)
    (hupper : |q ⬝ᵥ (A *ᵥ g)| ≤ Lam * ‖q‖ * ‖g‖) :
    lam * (z ^ 2 * ‖g‖ ^ 2) ≤
      matrixBilinearForm A (z • (z • g + w • q) + (z * w) • q) g
        + lam / 2 * (z ^ 2 * ‖g‖ ^ 2) + 2 * Lam ^ 2 / lam * (‖q‖ ^ 2 * w ^ 2) := by
  have hexp : matrixBilinearForm A (z • (z • g + w • q) + (z * w) • q) g =
      z ^ 2 * A.toQuadraticForm' g + 2 * (z * w) * (q ⬝ᵥ (A *ᵥ g)) := by
    rw [← matrixBilinearForm_self, ← matrixBilinearForm_apply]
    simp only [map_add, map_smul, _root_.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hcross : |q ⬝ᵥ (A *ᵥ g)| ≤ Lam * ‖q‖ * ‖g‖ := hupper
   
   
  have hyoung : 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) ≤
      lam / 2 * (|z| * ‖g‖) ^ 2 + 2 / lam * (Lam * |w| * ‖q‖) ^ 2 := by
    have h := two_mul_le_add_mul_sq (a := |z| * ‖g‖) (b := Lam * |w| * ‖q‖)
      (ε := lam / 2) (by linarith)
    rwa [inv_div] at h
  have hzw : |2 * (z * w) * (q ⬝ᵥ (A *ᵥ g))| ≤ 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc 2 * (|z| * |w|) * |q ⬝ᵥ (A *ᵥ g)| ≤ 2 * (|z| * |w|) * (Lam * ‖q‖ * ‖g‖) := by
          gcongr
      _ = 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) := by ring
  have hsqz : |z| ^ 2 = z ^ 2 := sq_abs z
  have hsqw : |w| ^ 2 = w ^ 2 := sq_abs w
  have hyoung' : 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) ≤
      lam / 2 * (z ^ 2 * ‖g‖ ^ 2) + 2 * Lam ^ 2 / lam * (‖q‖ ^ 2 * w ^ 2) := by
    refine hyoung.trans_eq ?_
    rw [mul_pow, mul_pow, mul_pow, hsqz, hsqw]
    ring
  rw [hexp]
  nlinarith [neg_abs_le (2 * (z * w) * (q ⬝ᵥ (A *ᵥ g))), sq_nonneg z,
    mul_le_mul_of_nonneg_left hlower (sq_nonneg z)]

 

lemma abs_dotProduct_smul_one_mulVec_le_of_abs_le {c Lam : ℝ} (hc : |c| ≤ Lam)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((c • (1 : Matrix n n ℝ)) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  rw [smul_mulVec, one_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, abs_mul]
  calc
    |c| * |η ⬝ᵥ ξ| ≤ |c| * (‖η‖ * ‖ξ‖) := by
      gcongr
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
        abs_real_inner_le_norm η ξ
    _ ≤ Lam * ‖η‖ * ‖ξ‖ := by
      have hnorm : 0 ≤ ‖η‖ * ‖ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hc hnorm

 

lemma norm_matrixBilinearForm_smul_one_le_of_abs_le {c Lam : ℝ} (hc : |c| ≤ Lam)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm (c • (1 : Matrix n n ℝ)) η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
  norm_matrixBilinearForm_le_of_upper_bound (c • (1 : Matrix n n ℝ))
    (abs_dotProduct_smul_one_mulVec_le_of_abs_le hc) η ξ

 
lemma lower_bound_toQuadraticForm'_add {A B : Matrix n n ℝ} {lam : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ (A + B).toQuadraticForm' ξ := by
  rw [toQuadraticForm'_add]
  exact (hA ξ).trans (le_add_of_nonneg_right (hB ξ))

 

lemma lower_bound_toQuadraticForm'_add_of_lower_bound {A B : Matrix n n ℝ} {lam Mu : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hB : ∀ ξ : EuclideanSpace ℝ n, -(Mu * ‖ξ‖ ^ 2) ≤ B.toQuadraticForm' ξ)
    (ξ : EuclideanSpace ℝ n) : (lam - Mu) * ‖ξ‖ ^ 2 ≤ (A + B).toQuadraticForm' ξ := by
  rw [toQuadraticForm'_add]
  have hA_lower := hA ξ
  have hB_lower := hB ξ
  nlinarith

 

lemma abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le {B : Matrix n n ℝ} {Mu : ℝ}
    (hB : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (B *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) (ξ : EuclideanSpace ℝ n) :
    |B.toQuadraticForm' ξ| ≤ Mu * ‖ξ‖ ^ 2 := by
  rw [Matrix.toQuadraticForm'_apply]
  have h := hB ξ ξ
  simpa [sq, mul_assoc] using h

 

lemma isCoercive_matrixBilinearForm_of_lower_bound (A : Matrix n n ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) :
    IsCoercive (matrixBilinearForm A) := by
  refine ⟨lam, hlam, fun ξ => ?_⟩
  rw [matrixBilinearForm_self]
  simpa [sq, pow_two, mul_assoc] using hA ξ

 
lemma isCoercive_matrixBilinearForm_one :
    IsCoercive (matrixBilinearForm (1 : Matrix n n ℝ)) := by
  refine isCoercive_matrixBilinearForm_of_lower_bound (1 : Matrix n n ℝ) zero_lt_one ?_
  intro ξ
  simp

 
lemma isCoercive_matrixBilinearForm_smul_one {c : ℝ} (hc : 0 < c) :
    IsCoercive (matrixBilinearForm (c • (1 : Matrix n n ℝ))) := by
  refine isCoercive_matrixBilinearForm_of_lower_bound (c • (1 : Matrix n n ℝ)) hc ?_
  intro ξ
  simp

 





def UniformlyEllipticOn (Ω : Set X) (a : X → Matrix n n ℝ) (lam Lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧
    ∀ ⦃x⦄, x ∈ Ω →
      (∀ ξ : EuclideanSpace ℝ n,
        lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
        ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖

 
lemma uniformlyEllipticOn_iff :
    UniformlyEllipticOn Ω a lam Lam ↔
      0 < lam ∧ lam ≤ Lam ∧
        ∀ ⦃x⦄, x ∈ Ω →
          (∀ ξ : EuclideanSpace ℝ n,
            lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
            ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  Iff.rfl

namespace UniformlyEllipticOn

variable {Ω Ω' : Set X} {a b : X → Matrix n n ℝ}
  {lam Lam lam' Lam' : ℝ}

 
@[grind →]
lemma pos (h : UniformlyEllipticOn Ω a lam Lam) : 0 < lam :=
  h.1

 
@[grind →]
lemma le (h : UniformlyEllipticOn Ω a lam Lam) : lam ≤ Lam :=
  h.2.1

 
lemma upper_nonneg (h : UniformlyEllipticOn Ω a lam Lam) : 0 ≤ Lam :=
  h.pos.le.trans h.le

 
@[grind =>]
lemma lower_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ :=
  (h.2.2 hx).1 ξ

 
@[grind =>]
lemma upper_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  (h.2.2 hx).2 η ξ

 
lemma quadraticForm_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    0 ≤ (a x).toQuadraticForm' ξ := by
  exact (mul_nonneg h.pos.le (sq_nonneg ‖ξ‖)).trans (h.lower_bound hx ξ)

 
lemma quadraticForm_pos (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {ξ : EuclideanSpace ℝ n} (hξ : ξ ≠ 0) :
    0 < (a x).toQuadraticForm' ξ := by
  exact (mul_pos h.pos (sq_pos_of_ne_zero (by simpa using hξ))).trans_le
    (h.lower_bound hx ξ)

 
lemma mono_set (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : Ω' ⊆ Ω) :
    UniformlyEllipticOn Ω' a lam Lam :=
  ⟨h.pos, h.le, fun {_} hx => h.2.2 (hΩ hx)⟩

 

lemma mono_constants (h : UniformlyEllipticOn Ω a lam Lam) (hlam' : 0 < lam')
    (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') :
    UniformlyEllipticOn Ω a lam' Lam' := by
  refine ⟨hlam', hlam'_le.trans (h.le.trans hLam_le), fun {x} hx => ?_⟩
  refine ⟨fun ξ => ?_, fun η ξ => ?_⟩
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    exact (mul_le_mul_of_nonneg_right hlam'_le hnorm).trans (h.lower_bound hx ξ)
  · exact (h.upper_bound hx η ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLam_le (norm_nonneg _))
        (norm_nonneg _))

 

lemma of_bounds (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hbounds : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hupper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω a lam Lam :=
  ⟨hlam, hlamLam, fun {_} hx => ⟨hbounds hx, hupper hx⟩⟩

 
lemma congr (h : UniformlyEllipticOn Ω a lam Lam) (hab : Set.EqOn b a Ω) :
    UniformlyEllipticOn Ω b lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · rw [hab hx]
    exact h.lower_bound hx ξ
  · rw [hab hx]
    exact h.upper_bound hx η ξ

 

@[grind =>]
lemma norm_point_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
  norm_matrixBilinearForm_le_of_upper_bound (a x) (h.upper_bound hx) η ξ

 

@[grind =>]
lemma opNorm_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    ‖matrixBilinearForm (a x)‖ ≤ Lam :=
  matrixBilinearForm_opNorm_le_of_upper_bound (a x) h.upper_nonneg (h.upper_bound hx)

 

@[grind =>]
lemma norm_point_matrixBilinearForm_le_mul_of_norm_le
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {R S : ℝ}
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * R * S :=
  (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le
    (h.opNorm_matrixBilinearForm_le hx) hη hξ

 

@[grind =>]
lemma isCoercive_matrixBilinearForm (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    IsCoercive (matrixBilinearForm (a x)) :=
  isCoercive_matrixBilinearForm_of_lower_bound (a x) h.pos (h.lower_bound hx)

 



lemma transpose (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => (a x)ᵀ) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · rw [Matrix.dotProduct_transpose_mulVec]
    rw [mul_right_comm]
    exact h.upper_bound hx ξ η

 





lemma coefficientSymmetricPart (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => coefficientSymmetricPart (a x)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · exact abs_dotProduct_coefficientSymmetricPart_mulVec_le (h.upper_bound hx) η ξ

 





lemma add_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {b : X → Matrix n n ℝ}
    {Mu : ℝ} (hMu : 0 ≤ Mu) (hb_nonneg : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      0 ≤ (b x).toQuadraticForm' ξ)
    (hb_upper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (b x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω (fun x => a x + b x) lam (Lam + Mu) := by
  refine UniformlyEllipticOn.of_bounds h.pos ?_ (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · exact h.le.trans (le_add_of_nonneg_right hMu)
  · exact lower_bound_toQuadraticForm'_add (h.lower_bound hx) (hb_nonneg hx) ξ
  · exact abs_dotProduct_add_mulVec_le (h.upper_bound hx) (hb_upper hx) η ξ

 






lemma add_bounded (h : UniformlyEllipticOn Ω a lam Lam) {b : X → Matrix n n ℝ}
    {Mu : ℝ} (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hb_upper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (b x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω (fun x => a x + b x) (lam - Mu) (Lam + Mu) := by
  refine UniformlyEllipticOn.of_bounds (sub_pos.mpr hMu_lt) ?_ (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · linarith [h.le, hMu_nonneg]
  · refine lower_bound_toQuadraticForm'_add_of_lower_bound (h.lower_bound hx) ?_ ξ
    intro ζ
    exact (neg_le_neg
      (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (hb_upper hx) ζ)).trans
      (neg_abs_le ((b x).toQuadraticForm' ζ))
  · exact abs_dotProduct_add_mulVec_le (h.upper_bound hx) (hb_upper hx) η ξ

 




lemma add_smul_one_bounded (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ} {Mu : ℝ}
    (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam) (hc_abs : ∀ ⦃x⦄, x ∈ Ω → |c x| ≤ Mu) :
    UniformlyEllipticOn Ω (fun x => a x + c x • (1 : Matrix n n ℝ)) (lam - Mu)
      (Lam + Mu) :=
  h.add_bounded hMu_nonneg hMu_lt
    (fun {_} hx η ξ => abs_dotProduct_smul_one_mulVec_le_of_abs_le (hc_abs hx) η ξ)

 

lemma add_const_smul_one_bounded (h : UniformlyEllipticOn Ω a lam Lam) {c Mu : ℝ}
    (hMu_lt : Mu < lam) (hc_abs : |c| ≤ Mu) :
    UniformlyEllipticOn Ω (fun y => a y + c • (1 : Matrix n n ℝ)) (lam - Mu)
      (Lam + Mu) :=
  h.add_smul_one_bounded ((abs_nonneg c).trans hc_abs) hMu_lt (fun {_} _ => hc_abs)

 

lemma add_smul_one (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ} {Mu : ℝ}
    (hMu : 0 ≤ Mu) (hc_nonneg : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x) (hc_upper : ∀ ⦃x⦄, x ∈ Ω → c x ≤ Mu) :
    UniformlyEllipticOn Ω (fun x => a x + c x • (1 : Matrix n n ℝ)) lam (Lam + Mu) := by
  refine h.add_nonneg hMu (fun {x} hx ξ => ?_) (fun {x} hx η ξ => ?_)
  · simp only [toQuadraticForm'_smul_one]
    exact mul_nonneg (hc_nonneg hx) (sq_nonneg ‖ξ‖)
  · have hcx_abs : |c x| ≤ Mu := by
      simpa [abs_of_nonneg (hc_nonneg hx)] using hc_upper hx
    exact abs_dotProduct_smul_one_mulVec_le_of_abs_le hcx_abs η ξ

 

lemma add_const_smul_one (h : UniformlyEllipticOn Ω a lam Lam) {c : ℝ} (hc : 0 ≤ c) :
    UniformlyEllipticOn Ω (fun x => a x + c • (1 : Matrix n n ℝ)) lam (Lam + c) :=
  h.add_smul_one hc (fun {_} _ => hc) (fun {_} _ => le_rfl)

end UniformlyEllipticOn

variable {Ω : Set X} {a b : X → Matrix n n ℝ}
  {lam Lam : ℝ}

 
lemma uniformlyEllipticOn_congr (hab : Set.EqOn a b Ω) :
    UniformlyEllipticOn Ω a lam Lam ↔ UniformlyEllipticOn Ω b lam Lam := by
  constructor
  · intro h
    exact h.congr (fun x hx => (hab hx).symm)
  · intro h
    exact h.congr hab

 

lemma uniformlyEllipticOn_const_one (Ω : Set X) {lam Lam : ℝ} (hlam : 0 < lam)
    (hlam_one : lam ≤ 1) (hone_Lam : 1 ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam (hlam_one.trans hone_Lam) (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    simp only [toQuadraticForm'_one]
    simpa using mul_le_mul_of_nonneg_right hlam_one hnorm
  · rw [one_mulVec]
    calc
      |η ⬝ᵥ ξ| ≤ ‖η‖ * ‖ξ‖ := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
          abs_real_inner_le_norm η ξ
      _ ≤ Lam * ‖η‖ * ‖ξ‖ := by
        have hnorm : 0 ≤ ‖η‖ * ‖ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hone_Lam hnorm

 

lemma uniformlyEllipticOn_const_one_one (Ω : Set X) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) 1 1 :=
  uniformlyEllipticOn_const_one Ω zero_lt_one le_rfl le_rfl

 




lemma uniformlyEllipticOn_smul_one (Ω : Set X) (c : X → ℝ) {lam Lam : ℝ}
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hbound : ∀ ⦃x⦄, x ∈ Ω → lam ≤ c x ∧ c x ≤ Lam) :
    UniformlyEllipticOn Ω (fun x => c x • (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam hlamLam (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simp only [toQuadraticForm'_smul_one]
    exact mul_le_mul_of_nonneg_right (hbound hx).1 (sq_nonneg ‖ξ‖)
  · have hcx_nonneg : 0 ≤ c x := hlam.le.trans (hbound hx).1
    have hcx_abs : |c x| ≤ Lam := by simpa [abs_of_nonneg hcx_nonneg] using (hbound hx).2
    exact abs_dotProduct_smul_one_mulVec_le_of_abs_le hcx_abs η ξ

 

lemma uniformlyEllipticOn_const_smul_one_self (Ω : Set X) {c : ℝ} (hc : 0 < c) :
    UniformlyEllipticOn Ω (fun _ => c • (1 : Matrix n n ℝ)) c c :=
  uniformlyEllipticOn_smul_one Ω (fun _ => c) hc le_rfl (fun {_} _ => ⟨le_rfl, le_rfl⟩)

 

lemma uniformlyEllipticOn_const_smul_one (Ω : Set X) {c lam Lam : ℝ} (hlam : 0 < lam)
    (hlamc : lam ≤ c) (hcLam : c ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => c • (1 : Matrix n n ℝ)) lam Lam :=
  uniformlyEllipticOn_smul_one Ω (fun _ => c) hlam (hlamc.trans hcLam)
    (fun {_} _ => ⟨hlamc, hcLam⟩)

 

section Calculus

open Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

variable {n : Type*} [Fintype n]

 
theorem sum_inner_mul_matrixBilinearForm {A : Matrix n n ℝ} (ξ η : EuclideanSpace ℝ n) :
    ∑ i, ⟪ξ, EuclideanSpace.basisFun n ℝ i⟫_ℝ *
        matrixBilinearForm A (EuclideanSpace.basisFun n ℝ i) η = matrixBilinearForm A ξ η := by
  conv_rhs => rw [← (EuclideanSpace.basisFun n ℝ).sum_repr' ξ]
  simp [map_sum, map_smul]

 

theorem contDiff_matrixBilinearForm_gradient {A : Matrix n n ℝ}
    {ψ : EuclideanSpace ℝ n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (η : EuclideanSpace ℝ n) :
    ContDiff ℝ ∞ (fun y => matrixBilinearForm A η (∇ ψ y)) :=
  (matrixBilinearForm A η).contDiff.comp (hψ.gradient_right (m := ∞) (by simp))

 
theorem tsupport_matrixBilinearForm_gradient_subset {A : Matrix n n ℝ}
    (ψ : EuclideanSpace ℝ n → ℝ) (η : EuclideanSpace ℝ n) :
    tsupport (fun y => matrixBilinearForm A η (∇ ψ y)) ⊆ tsupport ψ :=
  closure_minimal (fun x hx => by_contra fun hxψ => hx (by
    simp [gradient_of_notMem_tsupport hxψ])) (isClosed_tsupport ψ)

end Calculus

end PDE

end TauCeti
