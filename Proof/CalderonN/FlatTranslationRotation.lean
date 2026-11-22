module

public import Proof.CalderonN.CoordinateHarmonicRaising
public import Proof.CalderonN.SmoothAngularCasimir

import Mathlib.Tactic

/-! The flat tangential term in the Gauss adjoint on each homogeneous
polynomial, with the same rotation convention as the actual trace. -/

public section

noncomputable section
open MvPolynomial
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace CalderonN

open OAI.AnisotropicCalderon AngularPolynomial GreenRadialTrace SmoothSphereRotation

variable {dim : ℕ}

theorem polynomial_rotation_sum_mul_coordinate (k : ℕ) (i : Fin dim)
    (p : MvPolynomial (Fin dim) ℝ) (hp : p.IsHomogeneous k) :
    (∑ j, polynomialRotation j i (MvPolynomial.X j*p)) =
      radiusSq*pderiv i p-C ((dim:ℝ)+(k:ℝ)-1)*(MvPolynomial.X i*p) := by
  classical
  have h (j : Fin dim) : polynomialRotation j i (MvPolynomial.X j*p) =
      (if i=j then MvPolynomial.X i*p else 0)+(MvPolynomial.X j)^2*pderiv i p-
        (MvPolynomial.X i*p+MvPolynomial.X i*(MvPolynomial.X j*pderiv j p)) := by
    simp only [polynomialRotation,pderiv_mul,pderiv_X,Pi.single_apply]
    by_cases hij : i=j
    · subst j
      simp only [ite_true,one_mul]
      ring
    · simp only [if_neg hij,if_neg (Ne.symm hij),ite_true,zero_mul,one_mul]
      ring
  simp only [h,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    ← Finset.sum_mul,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← radiusSq,← polynomialEuler,polynomialEuler_homogeneous k p hp,nsmul_eq_mul]
  rw [← map_natCast (C : ℝ →+* MvPolynomial (Fin dim) ℝ) dim]
  simp only [map_sub,map_add,map_one]
  ring

variable [NeZero dim]

theorem sphere_rotation_sum_mul_coordinate (k : ℕ) (i : Fin dim)
    (p : MvPolynomial (Fin dim) ℝ) (hp : p.IsHomogeneous k) (z : X dim)
    (hz : z ∈ standardSphere dim) :
    (∑ j, sphereRotationDerivative j i (fun x => polynomialEvaluation p x*x j) z) =
      polynomialEvaluation (pderiv i p) z-
        ((dim:ℝ)+(k:ℝ)-1)*(z i*polynomialEvaluation p z) := by
  have hEq (j : Fin dim) : (fun x => polynomialEvaluation p x*x j) =
      polynomialEvaluation (MvPolynomial.X j*p) := by
    funext x
    change polynomialEvaluation p x*x j = eval (euclideanCoordinates dim x) (MvPolynomial.X j*p)
    rw [map_mul,eval_X]
    change polynomialEvaluation p x*x j = x j*polynomialEvaluation p x
    exact mul_comm _ _
  simp_rw [hEq,sphereRotationDerivative_polynomialEvaluation]
  change (∑ j, eval (euclideanCoordinates dim z) (polynomialRotation j i (MvPolynomial.X j*p))) = _
  rw [← map_sum,polynomial_rotation_sum_mul_coordinate k i p hp,map_sub,map_mul,map_mul,map_mul,eval_C,eval_X]
  have hRadius : eval (euclideanCoordinates dim z) (radiusSq : MvPolynomial (Fin dim) ℝ) = 1 := by
    simp only [radiusSq,map_sum,map_pow,eval_X]
    exact unitSphere_sum_sq ⟨z,hz⟩
  rw [hRadius,one_mul]
  rfl

end CalderonN
