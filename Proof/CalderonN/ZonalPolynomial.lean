module

public import Proof.Archive.AngularCoefficient
public import Proof.CalderonN.Coercivity

import Mathlib.Tactic

@[expose] public section

/- Port of ZonalPolynomial and ZonalHarmonic, Proposition 5.3 check f308cb9d.
   The coefficient recurrence now depends on dimension. -/
noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace CalderonN

variable {n : ℕ}
open OAI.AnisotropicCalderon.AngularPolynomial

def zonalLinear (w : I n → ℝ) : MvPolynomial (I n) ℝ := ∑ i, C (w i) * MvPolynomial.X i

/-- Homogeneous extension of the normalized zonal recurrence. -/
def zonalPolynomial (w : I n → ℝ) : ℕ → MvPolynomial (I n) ℝ
  | 0 => 1
  | 1 => zonalLinear w
  | k+2 => (((k : ℝ)+(n : ℝ)-1)⁻¹) •
      ((2*(k : ℝ)+n) • (zonalLinear w * zonalPolynomial w (k+1)) -
       ((k : ℝ)+1) • (radiusSq * zonalPolynomial w k))

lemma zonalLinear_homogeneous (w : I n → ℝ) : (zonalLinear w).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun i _ => (isHomogeneous_X (R:=ℝ) i).C_mul (w i))

lemma zonalPolynomial_homogeneous (w : I n → ℝ) (k : ℕ) : (zonalPolynomial w k).IsHomogeneous k := by
  induction k using Nat.twoStepInduction with
  | zero => exact isHomogeneous_one (I n) ℝ
  | one => exact zonalLinear_homogeneous w
  | more k hk hk1 =>
    have h1 : (zonalLinear w * zonalPolynomial w (k+1)).IsHomogeneous (k+2) := by
      convert (zonalLinear_homogeneous w).mul hk1 using 1
      omega
    have h0 : (radiusSq * zonalPolynomial w k).IsHomogeneous (k+2) := by
      convert radiusSq_isHomogeneous.mul hk using 1
      omega
    simpa only [zonalPolynomial, smul_eq_C_mul] using
      (((h1.C_mul (2*(k : ℝ)+n)).sub (h0.C_mul ((k : ℝ)+1))).C_mul (((k : ℝ)+(n : ℝ)-1)⁻¹))

lemma eval_zonalLinear (w z : I n → ℝ) : eval z (zonalLinear w) = ∑ i, w i*z i := by
  simp [zonalLinear]

lemma eval_radiusSq_of_unit (z : I n → ℝ) (hz : ∑ i, (z i)^2 = 1) :
    eval z (radiusSq : MvPolynomial (I n) ℝ) = 1 := by
  simpa only [radiusSq, map_sum, map_pow, eval_X] using hz

lemma eval_zonalPolynomial_of_unit (w z : I n → ℝ) (hz : ∑ i, (z i)^2 = 1)
    (k : ℕ) :
    eval z (zonalPolynomial w k) = zonal n (∑ i, w i*z i) k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [zonalPolynomial,zonal]
  | one => simp [zonalPolynomial,zonal,eval_zonalLinear]
  | more k hk hk1 =>
    simp only [zonalPolynomial, smul_eq_C_mul, map_sub, map_mul, eval_C, eval_zonalLinear,
      eval_radiusSq_of_unit z hz, one_mul, hk, hk1, zonal]
    rw [div_eq_mul_inv]
    ring

lemma directionalDerivative_add (w : I n → ℝ) (p q : MvPolynomial (I n) ℝ) :
    directionalDerivative w (p+q) = directionalDerivative w p + directionalDerivative w q := by
  simp [directionalDerivative, polynomialContraction, map_add, mul_add, Finset.sum_add_distrib]

lemma directionalDerivative_sub (w : I n → ℝ) (p q : MvPolynomial (I n) ℝ) :
    directionalDerivative w (p-q) = directionalDerivative w p - directionalDerivative w q := by
  simp [directionalDerivative, polynomialContraction, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma directionalDerivative_smul (w : I n → ℝ) (a : ℝ) (p : MvPolynomial (I n) ℝ) :
    directionalDerivative w (a • p) = a • directionalDerivative w p := by
  simp [directionalDerivative, polynomialContraction, smul_eq_C_mul, Finset.mul_sum, mul_left_comm]

lemma directionalDerivative_mul (w : I n → ℝ) (p q : MvPolynomial (I n) ℝ) :
    directionalDerivative w (p*q) = directionalDerivative w p*q+p*directionalDerivative w q := by
  simp only [directionalDerivative, polynomialContraction, pderiv_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma directionalDerivative_one (w : I n → ℝ) : directionalDerivative w (1 : MvPolynomial (I n) ℝ) = 0 := by
  simp [directionalDerivative, polynomialContraction]

lemma pderiv_zonalLinear (w : I n → ℝ) (i : I n) : pderiv i (zonalLinear w) = C (w i) := by
  simp [zonalLinear, pderiv_X, Pi.single_apply]

lemma directionalDerivative_zonalLinear (w : I n → ℝ) :
    directionalDerivative w (zonalLinear w) = C (∑ i, (w i)^2) := by
  simp [directionalDerivative, polynomialContraction, pderiv_zonalLinear, pow_two]

lemma directionalDerivative_radiusSq (w : I n → ℝ) :
    directionalDerivative w (radiusSq : MvPolynomial (I n) ℝ) = (2 : ℝ) • zonalLinear w := by
  simp only [directionalDerivative, polynomialContraction, pderiv_radiusSq, zonalLinear,
    Finset.smul_sum, smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_ofNat]
  ring

lemma laplacian_zonalLinear (w : I n → ℝ) : laplacian (zonalLinear w) = 0 := by
  simp [laplacian, pderiv_zonalLinear]

private theorem polynomial_laplacian_mul (f g : MvPolynomial (I n) ℝ) :
    laplacian (f * g) = laplacian f * g + 2 * (∑ i, pderiv i f * pderiv i g) +
      f * laplacian g := by
  simp only [laplacian, pderiv_mul, map_add, Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma laplacian_zonalLinear_mul (w : I n → ℝ) (p : MvPolynomial (I n) ℝ) :
    laplacian (zonalLinear w*p) = zonalLinear w*laplacian p + (2 : ℝ) • directionalDerivative w p := by
  rw [polynomial_laplacian_mul,laplacian_zonalLinear,zero_mul,zero_add]
  simp_rw [pderiv_zonalLinear]
  change 2*(directionalDerivative w p)+zonalLinear w*laplacian p = _
  rw [smul_eq_C_mul,map_ofNat]
  ring

lemma directionalDerivative_zonalPolynomial (hn : 3 ≤ n) (w : I n → ℝ) (hw : ∑ i, (w i)^2 = 1) (k : ℕ) :
    directionalDerivative w (zonalPolynomial w (k+1)) = ((k : ℝ)+1) • zonalPolynomial w k := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  induction k using Nat.twoStepInduction with
  | zero =>
    simp [zonalPolynomial, directionalDerivative_zonalLinear, hw]
  | one =>
    simp only [zonalPolynomial]
    rw [directionalDerivative_smul, directionalDerivative_sub,
      directionalDerivative_smul, directionalDerivative_smul, directionalDerivative_mul,
      directionalDerivative_mul]
    simp only [directionalDerivative_zonalLinear, hw, map_one, one_mul, mul_one,
      directionalDerivative_one, directionalDerivative_radiusSq, mul_zero, add_zero]
    push_cast
    have hden : (n : ℝ) - 1 ≠ 0 := by linarith
    have hcoeff : ((n : ℝ) - 1)⁻¹ * (2 * (n : ℝ) - 2) = 2 := by
      field_simp [hden]
    calc
      _ = (((n : ℝ) - 1)⁻¹ * (2 * (n : ℝ) - 2)) • zonalLinear w := by module
      _ = _ := by rw [hcoeff]; norm_num [zonalPolynomial]
  | more k hk hk1 =>
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have h2 : (k : ℝ)+(n : ℝ)-1 ≠ 0 := by linarith
    have h3 : (k : ℝ)+1+(n : ℝ)-1 ≠ 0 := by linarith
    change directionalDerivative w (zonalPolynomial w ((k+1)+2)) = _
    rw [zonalPolynomial, directionalDerivative_smul, directionalDerivative_sub,
      directionalDerivative_smul, directionalDerivative_smul, directionalDerivative_mul,
      directionalDerivative_mul, directionalDerivative_zonalLinear, hw, map_one, one_mul,
      directionalDerivative_radiusSq, hk, hk1]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [zonalPolynomial]
    simp only [mul_smul_comm, smul_mul_assoc]
    match_scalars <;> field_simp [h2,h3] <;> ring

lemma laplacian_smul_real (a : ℝ) (p : MvPolynomial (I n) ℝ) :
    laplacian (a • p) = a • laplacian p := by
  simpa only [smul_eq_C_mul] using laplacian_C_mul a p

/-- The homogeneous zonal kernel is harmonic for a unit axial vector. -/
theorem zonalPolynomial_harmonic (hn : 3 ≤ n) (w : I n → ℝ) (hw : ∑ i, (w i)^2 = 1) (k : ℕ) :
    laplacian (zonalPolynomial w k) = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [zonalPolynomial,laplacian]
  | one => exact laplacian_zonalLinear w
  | more k hk hk1 =>
    rw [zonalPolynomial, laplacian_smul_real, laplacian_sub, laplacian_smul_real,
      laplacian_smul_real, laplacian_zonalLinear_mul,
      laplacian_radiusSq_mul_of_isHomogeneous (zonalPolynomial_homogeneous w k), hk, hk1,
      directionalDerivative_zonalPolynomial hn w hw k]
    simp only [mul_zero, zero_add, Fintype.card_fin, ← smul_eq_C_mul]
    have hzero : (2*(k : ℝ)+n) • ((2 : ℝ) • (((k : ℝ)+1) • zonalPolynomial w k)) -
        ((k : ℝ)+1) • ((4*(k : ℝ)+2*(n : ℝ)) • zonalPolynomial w k) = 0 := by module
    rw [hzero, smul_zero]

end CalderonN
