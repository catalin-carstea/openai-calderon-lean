module

public import Proof.CalderonN.BallRotationFlux
public import Proof.CalderonN.MatrixFieldJetNorms

import Mathlib.Tactic

/-! A solid angular derivative uses one spatial derivative of the
coefficient. Its uniform local C1 bound uses the spatial C2 bound. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem norm_entrywise_matrix_mul (A B : Mat dim) :
    ‖A*B‖ ≤ (dim : ℝ)*‖A‖*‖B‖ := by
  rw [mul_assoc]
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro k l
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin dim, ‖A‖*‖B‖ := Finset.sum_le_sum fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

private def matrixCommuteRightL (B : Mat dim) : Mat dim →L[ℝ] Mat dim :=
  (⟨⟨fun A => A*B-B*A, fun A C => by
    rw [add_mul,mul_add]; abel⟩, fun r A => by
      change (r • A)*B-B*(r • A) = r • (A*B-B*A)
      rw [smul_mul_assoc,mul_smul_comm,smul_sub]⟩ : Mat dim →ₗ[ℝ] Mat dim).mkContinuous
      (2*(dim : ℝ)*‖B‖) (fun A => by
        change ‖A*B-B*A‖ ≤ _
        calc
          _ ≤ ‖A*B‖+‖B*A‖ := norm_sub_le _ _
          _ ≤ _ := by
            have hl := norm_entrywise_matrix_mul A B
            have hr := norm_entrywise_matrix_mul B A
            linarith only [hl, hr, show 2*(dim : ℝ)*‖B‖*‖A‖ =
              (dim : ℝ)*‖A‖*‖B‖+(dim : ℝ)*‖B‖*‖A‖ by ring])

private theorem matrixCommuteRightL_apply (B A : Mat dim) :
    matrixCommuteRightL B A = A*B-B*A := rfl

private theorem norm_matrixCommuteRightL_le (B : Mat dim) :
    ‖matrixCommuteRightL B‖ ≤ 2*(dim : ℝ)*‖B‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

private theorem norm_coordinateMatrix_le (J : X dim →L[ℝ] X dim) :
    ‖coordinateMatrix J‖ ≤ ‖J‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro k l
  rw [coordinateMatrix_apply]
  change ‖EuclideanSpace.proj k (J (axis l))‖ ≤ _
  have h := PiLp.norm_apply_le (J (axis l)) k
  exact h.trans ((J.le_opNorm (axis l)).trans_eq (by simp [axis]))

private theorem ballRotationCoefficient_eq_directional_add (i j : Fin dim)
    (a : X dim → Mat dim) (z : X dim) :
    let J := ballRotationGeneratorL i j
    ballRotationCoefficient i j a z =
      fderiv ℝ a z (J z)+matrixCommuteRightL (coordinateMatrix J) (a z) := by
  let J := ballRotationGeneratorL i j
  let B := coordinateMatrix J
  change fderiv ℝ a z (J z)+a z*B-B*a z = fderiv ℝ a z (J z)+matrixCommuteRightL B (a z)
  rw [matrixCommuteRightL_apply]
  abel

/-- On the ball of radius two, rotation of a coefficient with spatial
jets bounded by q has its first two jets bounded linearly in q. -/
theorem norm_ballRotationCoefficient_jets_le (i j : Fin dim) {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (z : X dim) (hz : ‖z‖ ≤ 2)
    (q : ℝ) (hq : 0 ≤ q) (h0 : ‖a z‖ ≤ q) (h1 : ‖fderiv ℝ a z‖ ≤ q)
    (h2 : ‖fderiv ℝ (fderiv ℝ a) z‖ ≤ q) :
    ‖ballRotationCoefficient i j a z‖ ≤ (6+4*(dim : ℝ))*q ∧
    ‖fderiv ℝ (ballRotationCoefficient i j a) z‖ ≤ (6+4*(dim : ℝ))*q := by
  let J := ballRotationGeneratorL i j
  let C := matrixCommuteRightL (coordinateMatrix J)
  have hJ : ‖J‖ ≤ 2 := norm_ballRotationGeneratorL_le i j
  have hC : ‖C‖ ≤ 4*(dim : ℝ) := by
    have hB := (norm_coordinateMatrix_le J).trans hJ
    exact (norm_matrixCommuteRightL_le _).trans
      ((mul_le_mul_of_nonneg_left hB (by positivity)).trans_eq (by ring))
  have hJz : ‖J z‖ ≤ 4 :=
    (J.le_opNorm z).trans ((mul_le_mul hJ hz (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
  have hExpr : ballRotationCoefficient i j a = (fun x => fderiv ℝ a x (J x)) + C ∘ a :=
    funext (ballRotationCoefficient_eq_directional_add i j a)
  constructor
  · rw [hExpr,Pi.add_apply,Function.comp_apply]
    calc
      _ ≤ ‖fderiv ℝ a z (J z)‖+‖C (a z)‖ := norm_add_le _ _
      _ ≤ q*4+(4*(dim : ℝ))*q := by
        exact add_le_add (((fderiv ℝ a z).le_opNorm _).trans
          (mul_le_mul h1 hJz (norm_nonneg _) hq)) ((C.le_opNorm _).trans
          (mul_le_mul hC h0 (norm_nonneg _) (by positivity)))
      _ ≤ _ := by nlinarith only [hq]
  · have hU := (((ha.fderiv_right (m := ∞) (by simp)).clm_apply J.contDiff).differentiable (by simp) z)
    have hV := (C.contDiff.comp ha).differentiable (by simp) z
    have hD := (C.hasFDerivAt.comp z (ha.differentiable (by simp) z).hasFDerivAt).fderiv
    rw [hExpr,fderiv_add hU hV,hD]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [add_apply,ContinuousLinearMap.comp_apply,fderiv_linearDirectional_apply J ha]
    have hJv := (J.le_opNorm v).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg v))
    calc
      _ ≤ (‖fderiv ℝ (fderiv ℝ a) z v (J z)‖+‖fderiv ℝ a z (J v)‖)+
            ‖C (fderiv ℝ a z v)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (q*‖v‖*4+q*(2*‖v‖))+(4*(dim : ℝ))*(q*‖v‖) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact (ContinuousLinearMap.le_opNorm₂ _ _ _).trans
            (mul_le_mul (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) hJz (norm_nonneg _) (by positivity))
        · exact ((fderiv ℝ a z).le_opNorm _).trans (mul_le_mul h1 hJv (norm_nonneg _) hq)
        · exact (C.le_opNorm _).trans (mul_le_mul hC
            (((fderiv ℝ a z).le_opNorm _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
            (norm_nonneg _) (by positivity))
      _ = _ := by ring

/-- Rotation of the normalized affine scalar coefficient is the affine
coefficient with the differentiated linear functional. -/
theorem ballRotationCoefficient_affine (i j : Fin dim) (ell : X dim →L[ℝ] ℝ)
    (r : ℝ) (R : X dim → Mat dim) (hR : ContDiff ℝ ∞ R) :
    ballRotationCoefficient i j (fun x => (1+r*ell x) • (1 : Mat dim)+R x) =
      fun z => r • (((ell.comp (ballRotationGeneratorL i j)) z) • (1 : Mat dim))+
        ballRotationCoefficient i j R z := by
  let J := ballRotationGeneratorL i j
  let B := coordinateMatrix J
  let L : X dim →L[ℝ] Mat dim := (r • ell).smulRight (1 : Mat dim)
  have hAffine : (fun x => (1+r*ell x) • (1 : Mat dim)) = fun x => 1+L x := by
    funext x
    simp only [add_smul,one_smul,L,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  have hRewrite : (fun x => (1+r*ell x) • (1 : Mat dim)+R x) = fun x => (1+L x)+R x := by
    exact congrArg (fun f : X dim → Mat dim => f+R) hAffine
  rw [hRewrite]
  funext z
  rw [ballRotationCoefficient_eq_directional_add,ballRotationCoefficient_eq_directional_add]
  change fderiv ℝ (fun x => (1+L x)+R x) z (J z)+matrixCommuteRightL B ((1+L z)+R z) = _
  have hD := (((L.hasFDerivAt (x := z)).const_add (1 : Mat dim)).add
    (hR.differentiable (by simp) z).hasFDerivAt).fderiv
  change fderiv ℝ (fun x => 1+L x+R x) z = _ at hD
  rw [hD,add_apply,map_add,map_add,matrixCommuteRightL_apply B 1,matrixCommuteRightL_apply B (L z)]
  simp only [L,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.comp_apply,one_mul,mul_one,sub_self,zero_add,
    smul_mul_assoc,mul_smul_comm,smul_smul]
  abel

end CalderonN
