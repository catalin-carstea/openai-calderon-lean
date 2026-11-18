import Proof.ZonalPolynomial

noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

lemma directionalDerivative_zonalPolynomial (w : I → ℝ) (hw : ∑ i, (w i)^2 = 1) (k : ℕ) :
    directionalDerivative w (zonalPolynomial w (k+1)) = ((k : ℝ)+1) • zonalPolynomial w k := by
  induction k using Nat.twoStepInduction with
  | zero =>
    simp [zonalPolynomial, directionalDerivative_zonalLinear, hw]
  | one =>
    simp only [zonalPolynomial]
    rw [directionalDerivative_smul, directionalDerivative_sub,
      directionalDerivative_smul, directionalDerivative_smul, directionalDerivative_mul,
      directionalDerivative_mul]
    simp only [zonalPolynomial, directionalDerivative_zonalLinear, hw, map_one, one_mul,
      directionalDerivative_one, directionalDerivative_radiusSq, mul_zero, add_zero]
    norm_num
    module
  | more k hk hk1 =>
    have h2 : (k : ℝ)+2 ≠ 0 := by positivity
    have h3 : (k : ℝ)+3 ≠ 0 := by positivity
    change directionalDerivative w (zonalPolynomial w ((k+1)+2)) = _
    rw [zonalPolynomial, directionalDerivative_smul, directionalDerivative_sub,
      directionalDerivative_smul, directionalDerivative_smul, directionalDerivative_mul,
      directionalDerivative_mul, directionalDerivative_zonalLinear, hw, map_one, one_mul,
      directionalDerivative_radiusSq, hk, hk1]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [zonalPolynomial]
    simp only [mul_smul_comm, smul_mul_assoc]
    match_scalars <;> field_simp [h2,h3] <;> ring

lemma laplacian_smul_real (a : ℝ) (p : MvPolynomial I ℝ) :
    laplacian (a • p) = a • laplacian p := by
  simpa only [smul_eq_C_mul] using laplacian_C_mul a p

/-- The homogeneous Legendre kernel is harmonic for a unit axial vector. -/
theorem zonalPolynomial_harmonic (w : I → ℝ) (hw : ∑ i, (w i)^2 = 1) (k : ℕ) :
    laplacian (zonalPolynomial w k) = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [zonalPolynomial,laplacian]
  | one => exact laplacian_zonalLinear w
  | more k hk hk1 =>
    rw [zonalPolynomial, laplacian_smul_real, laplacian_sub, laplacian_smul_real,
      laplacian_smul_real, laplacian_zonalLinear_mul,
      laplacian_radiusSq_mul_of_isHomogeneous (zonalPolynomial_homogeneous w k), hk, hk1,
      directionalDerivative_zonalPolynomial w hw k]
    simp only [mul_zero, zero_add, Fintype.card_fin, ← smul_eq_C_mul]
    have hzero : (2*(k : ℝ)+3) • ((2 : ℝ) • (((k : ℝ)+1) • zonalPolynomial w k)) -
        ((k : ℝ)+1) • ((4*(k : ℝ)+6) • zonalPolynomial w k) = 0 := by module
    norm_num only [Nat.cast_ofNat]
    rw [hzero, smul_zero]

end ShrinkingSpheres
