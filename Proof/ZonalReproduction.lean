import Proof.ZonalHarmonic

noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

lemma directionalDerivative_homogeneous (w : I → ℝ) {k : ℕ} (p : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) : (directionalDerivative w p).IsHomogeneous (k-1) :=
  IsHomogeneous.sum _ _ _ (fun i _ => hp.pderiv.C_mul (w i))

lemma laplacian_directionalDerivative (w : I → ℝ) (p : MvPolynomial I ℝ) (hp : laplacian p = 0) :
    laplacian (directionalDerivative w p) = 0 := by
  simp [directionalDerivative, polynomialContraction, laplacian_sum, laplacian_C_mul, laplacian_pderiv, hp]

lemma eval_directionalDerivative_self {k : ℕ} (w : I → ℝ) (p : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) : eval w (directionalDerivative w p) = (k : ℝ)*eval w p := by
  have hh := congrArg (eval w) hp.sum_X_mul_pderiv
  simpa only [directionalDerivative, polynomialContraction, map_sum, map_mul, eval_X,
    eval_C, map_nsmul, nsmul_eq_mul, map_natCast] using hh

lemma fischerInner_zonalLinear_mul (w : I → ℝ) (p q : MvPolynomial I ℝ) :
    fischerInner (zonalLinear w*p) q = fischerInner p (directionalDerivative w q) := by
  simp only [zonalLinear, Finset.sum_mul, mul_assoc, fischerInner_sum_left,
    fischerInner_C_mul_left, fischerInner_X_mul_left, directionalDerivative,
    polynomialContraction, fischerInner_sum_right, fischerInner_C_mul_right]

lemma fischerInner_one_left (p : MvPolynomial I ℝ) : fischerInner 1 p = p.coeff 0 := by
  simpa [fischerWeight] using fischerInner_monomial_left (0 : I →₀ ℕ) 1 p

lemma fischerInner_zonal_zero (w : I → ℝ) (p : MvPolynomial I ℝ) (hp : p.IsHomogeneous 0) :
    fischerInner (zonalPolynomial w 0) p = eval w p := by
  have hh : p = C (p.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous I).mpr hp)
  rw [zonalPolynomial, fischerInner_one_left, hh]
  simp

lemma fischerInner_smul_left (a : ℝ) (p q : MvPolynomial I ℝ) :
    fischerInner (a • p) q = a*fischerInner p q := by
  simpa only [smul_eq_C_mul] using fischerInner_C_mul_left a p q

/-- The solid Legendre kernel reproduces evaluation on harmonic homogeneous polynomials.
    This is proved from Fischer adjunction and Euler's identity. -/
theorem fischerInner_zonalPolynomial (w : I → ℝ) (k : ℕ) (p : MvPolynomial I ℝ)
    (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0) :
    fischerInner (zonalPolynomial w k) p = sphereNormalization 1 k * eval w p := by
  induction k using Nat.twoStepInduction generalizing p with
  | zero => simpa using fischerInner_zonal_zero w p hp
  | one =>
    have hD := directionalDerivative_homogeneous w p hp
    have hh := fischerInner_zonal_zero w (directionalDerivative w p) hD
    change fischerInner 1 (directionalDerivative w p) = _ at hh
    have ha := fischerInner_zonalLinear_mul w 1 p
    rw [mul_one] at ha
    rw [zonalPolynomial, ha, hh, eval_directionalDerivative_self w p hp]
    norm_num [sphereNormalization]
  | more k hk hk1 =>
    have hD : (directionalDerivative w p).IsHomogeneous (k+1) := by
      simpa using directionalDerivative_homogeneous w p hp
    have hΔD := laplacian_directionalDerivative w p hΔ
    have hR : fischerInner (radiusSq*zonalPolynomial w k) p = 0 := by
      rw [fischerInner_radiusSq_mul_left, hΔ, fischerInner_zero_right]
    rw [zonalPolynomial, fischerInner_smul_left, fischerInner_sub_left,
      fischerInner_smul_left, fischerInner_smul_left, hR, mul_zero, sub_zero,
      fischerInner_zonalLinear_mul, hk1 _ hD hΔD, eval_directionalDerivative_self w p hp,
      sphereNormalization_succ 1 (k+1)]
    simp only [Nat.cast_add, Nat.cast_one]
    have h2 : (k : ℝ)+2 ≠ 0 := by positivity
    field_simp [h2]
    ring

lemma sphereNormalization_three_one (k : ℕ) :
    sphereNormalization 3 k = (2*(k : ℝ)+1)*sphereNormalization 1 k := by
  induction k with
  | zero => norm_num
  | succ k hk =>
    rw [sphereNormalization_succ, sphereNormalization_succ, hk]
    push_cast
    ring

end ShrinkingSpheres
