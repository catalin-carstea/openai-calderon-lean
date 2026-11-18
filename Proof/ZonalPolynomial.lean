import Proof.PolynomialTests
import Mathlib.Tactic.Module

noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

def zonalLinear (w : I → ℝ) : MvPolynomial I ℝ := ∑ i, C (w i) * MvPolynomial.X i

/-- Homogeneous extension of the normalized Legendre recurrence. -/
def zonalPolynomial (w : I → ℝ) : ℕ → MvPolynomial I ℝ
  | 0 => 1
  | 1 => zonalLinear w
  | k+2 => (((k : ℝ)+2)⁻¹) •
      ((2*(k : ℝ)+3) • (zonalLinear w * zonalPolynomial w (k+1)) -
       ((k : ℝ)+1) • (radiusSq * zonalPolynomial w k))

lemma zonalLinear_homogeneous (w : I → ℝ) : (zonalLinear w).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun i _ => (isHomogeneous_X (R:=ℝ) i).C_mul (w i))

lemma zonalPolynomial_homogeneous (w : I → ℝ) (k : ℕ) : (zonalPolynomial w k).IsHomogeneous k := by
  induction k using Nat.twoStepInduction with
  | zero => exact isHomogeneous_one I ℝ
  | one => exact zonalLinear_homogeneous w
  | more k hk hk1 =>
    have h1 : (zonalLinear w * zonalPolynomial w (k+1)).IsHomogeneous (k+2) := by
      convert (zonalLinear_homogeneous w).mul hk1 using 1 <;> omega
    have h0 : (radiusSq * zonalPolynomial w k).IsHomogeneous (k+2) := by
      convert radiusSq_isHomogeneous.mul hk using 1 <;> omega
    simpa only [zonalPolynomial, smul_eq_C_mul] using
      (((h1.C_mul (2*(k : ℝ)+3)).sub (h0.C_mul ((k : ℝ)+1))).C_mul (((k : ℝ)+2)⁻¹))

lemma eval_zonalLinear (w z : I → ℝ) : eval z (zonalLinear w) = ∑ i, w i*z i := by
  simp [zonalLinear]

lemma eval_radiusSq_unitSphere (z : UnitSphere) : eval (z.val : I → ℝ) (radiusSq : MvPolynomial I ℝ) = 1 :=
  eval_normSqPoly_sphere z

lemma eval_zonalPolynomial_unitSphere (w : I → ℝ) (z : UnitSphere) (k : ℕ) :
    eval (z.val : I → ℝ) (zonalPolynomial w k) = legendre (∑ i, w i*z.val i) k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [zonalPolynomial,legendre]
  | one => simp [zonalPolynomial,legendre,eval_zonalLinear]
  | more k hk hk1 =>
    simp only [zonalPolynomial, smul_eq_C_mul, map_sub, map_mul, eval_C, eval_zonalLinear,
      eval_radiusSq_unitSphere, one_mul, hk, hk1, legendre]
    rw [div_eq_mul_inv]
    ring

lemma directionalDerivative_add (w : I → ℝ) (p q : MvPolynomial I ℝ) :
    directionalDerivative w (p+q) = directionalDerivative w p + directionalDerivative w q := by
  simp [directionalDerivative, polynomialContraction, map_add, mul_add, Finset.sum_add_distrib]

lemma directionalDerivative_sub (w : I → ℝ) (p q : MvPolynomial I ℝ) :
    directionalDerivative w (p-q) = directionalDerivative w p - directionalDerivative w q := by
  simp [directionalDerivative, polynomialContraction, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma directionalDerivative_smul (w : I → ℝ) (a : ℝ) (p : MvPolynomial I ℝ) :
    directionalDerivative w (a • p) = a • directionalDerivative w p := by
  simp [directionalDerivative, polynomialContraction, smul_eq_C_mul, pderiv_C_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm]

lemma directionalDerivative_mul (w : I → ℝ) (p q : MvPolynomial I ℝ) :
    directionalDerivative w (p*q) = directionalDerivative w p*q+p*directionalDerivative w q := by
  simp only [directionalDerivative, polynomialContraction, pderiv_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma directionalDerivative_one (w : I → ℝ) : directionalDerivative w (1 : MvPolynomial I ℝ) = 0 := by
  simp [directionalDerivative, polynomialContraction]

lemma pderiv_zonalLinear (w : I → ℝ) (i : I) : pderiv i (zonalLinear w) = C (w i) := by
  simp [zonalLinear, pderiv_C_mul, pderiv_X, Pi.single_apply]

lemma directionalDerivative_zonalLinear (w : I → ℝ) :
    directionalDerivative w (zonalLinear w) = C (∑ i, (w i)^2) := by
  simp [directionalDerivative, polynomialContraction, pderiv_zonalLinear, pow_two]

lemma directionalDerivative_radiusSq (w : I → ℝ) :
    directionalDerivative w (radiusSq : MvPolynomial I ℝ) = (2 : ℝ) • zonalLinear w := by
  change directionalDerivative w normSqPoly = _
  simp only [directionalDerivative, polynomialContraction, pderiv_normSqPoly, zonalLinear,
    Finset.smul_sum, smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_ofNat]
  ring

lemma laplacian_zonalLinear (w : I → ℝ) : laplacian (zonalLinear w) = 0 := by
  simp [laplacian, pderiv_zonalLinear]

lemma laplacian_zonalLinear_mul (w : I → ℝ) (p : MvPolynomial I ℝ) :
    laplacian (zonalLinear w*p) = zonalLinear w*laplacian p + (2 : ℝ) • directionalDerivative w p := by
  rw [laplacian_mul,laplacian_zonalLinear,zero_mul,zero_add]
  simp_rw [pderiv_zonalLinear]
  change 2*(directionalDerivative w p)+zonalLinear w*laplacian p = _
  rw [smul_eq_C_mul,map_ofNat]
  ring

end ShrinkingSpheres
