module

public import Proof.CalderonN.ZonalPolynomial

import Mathlib.Tactic

@[expose] public section

/- Reproducing identity ported from ZonalReproduction in Proposition 5.3 check
   f308cb9d. The spherical normalization is kept separate from the Fischer pairing. -/

noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace CalderonN

variable {n : ℕ}
open OAI.AnisotropicCalderon.AngularPolynomial

lemma directionalDerivative_homogeneous (w : I n → ℝ) {k : ℕ} (p : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) : (directionalDerivative w p).IsHomogeneous (k-1) :=
  IsHomogeneous.sum _ _ _ (fun i _ => hp.pderiv.C_mul (w i))

lemma laplacian_directionalDerivative (w : I n → ℝ) (p : MvPolynomial (I n) ℝ) (hp : laplacian p = 0) :
    laplacian (directionalDerivative w p) = 0 := by
  simp [directionalDerivative, polynomialContraction, laplacian_sum, laplacian_C_mul, laplacian_pderiv, hp]

lemma eval_directionalDerivative_self {k : ℕ} (w : I n → ℝ) (p : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) : eval w (directionalDerivative w p) = (k : ℝ)*eval w p := by
  have hh := congrArg (eval w) hp.sum_X_mul_pderiv
  simpa only [directionalDerivative, polynomialContraction, map_sum, map_mul, eval_X,
    eval_C, map_nsmul, nsmul_eq_mul, map_natCast] using hh

lemma fischerInner_zonalLinear_mul (w : I n → ℝ) (p q : MvPolynomial (I n) ℝ) :
    fischerInner (zonalLinear w*p) q = fischerInner p (directionalDerivative w q) := by
  simp only [zonalLinear, Finset.sum_mul, mul_assoc, fischerInner_sum_left,
    fischerInner_C_mul_left, fischerInner_X_mul_left, directionalDerivative,
    polynomialContraction, fischerInner_sum_right, fischerInner_C_mul_right]

lemma fischerInner_one_left (p : MvPolynomial (I n) ℝ) : fischerInner 1 p = p.coeff 0 := by
  simpa [fischerWeight] using fischerInner_monomial_left (0 : I n →₀ ℕ) 1 p

lemma fischerInner_zonal_zero (w : I n → ℝ) (p : MvPolynomial (I n) ℝ) (hp : p.IsHomogeneous 0) :
    fischerInner (zonalPolynomial w 0) p = eval w p := by
  have hh : p = C (p.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (I n)).mpr hp)
  rw [zonalPolynomial, fischerInner_one_left, hh]
  simp

lemma fischerInner_smul_left (a : ℝ) (p q : MvPolynomial (I n) ℝ) :
    fischerInner (a • p) q = a*fischerInner p q := by
  simpa only [smul_eq_C_mul] using fischerInner_C_mul_left a p q

/-- Degreewise Fischer factor in the reproducing identity. -/
def zonalFischerFactor (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | k+2 => ((k:ℝ)+2) * ((2*(k:ℝ)+n) / ((k:ℝ)+(n:ℝ)-1)) *
      zonalFischerFactor n (k+1)

/-- The solid zonal kernel reproduces evaluation on harmonic homogeneous polynomials.
    This is proved from Fischer adjunction and Euler's identity. -/
theorem fischerInner_zonalPolynomial (w : I n → ℝ) (k : ℕ) (p : MvPolynomial (I n) ℝ)
    (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    fischerInner (zonalPolynomial w k) p = zonalFischerFactor n k * eval w p := by
  induction k using Nat.twoStepInduction generalizing p with
  | zero => simpa [zonalFischerFactor] using fischerInner_zonal_zero w p hp
  | one =>
    have hD := directionalDerivative_homogeneous w p hp
    have hh := fischerInner_zonal_zero w (directionalDerivative w p) hD
    change fischerInner 1 (directionalDerivative w p) = _ at hh
    have ha := fischerInner_zonalLinear_mul w 1 p
    rw [mul_one] at ha
    rw [zonalPolynomial, ha, hh, eval_directionalDerivative_self w p hp]
    norm_num [zonalFischerFactor]
  | more k hk hk1 =>
    have hD : (directionalDerivative w p).IsHomogeneous (k+1) := by
      simpa using directionalDerivative_homogeneous w p hp
    have hΔD := laplacian_directionalDerivative w p hΔ
    have hR : fischerInner (radiusSq*zonalPolynomial w k) p = 0 := by
      rw [fischerInner_radiusSq_mul_left, hΔ, fischerInner_zero_right]
    rw [zonalPolynomial, fischerInner_smul_left, fischerInner_sub_left,
      fischerInner_smul_left, fischerInner_smul_left, hR, mul_zero, sub_zero,
      fischerInner_zonalLinear_mul, hk1 _ hD hΔD, eval_directionalDerivative_self w p hp,
      zonalFischerFactor]
    simp only [Nat.cast_add]
    rw [div_eq_mul_inv]
    ring

end CalderonN
