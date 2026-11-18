import Proof.ParallelScalarFirstRemainderPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Weighted products retain the scalar defect's inverse-beta gain
against a complete background model output. -/
lemma scalar_model_defect_product_real (s u B Z Q R ε β En : ℝ)
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) (hβ : 0 < β)
    (hGrad : β⁻¹*s^2 ≤ 3*En) (hMass : β*u^2 ≤ En) :
    (B*ε/β*s+Z*ε*u)*(Q*s+R*β*u) ≤
      (3*B*Q+4*Z*Q+4*B*R+Z*R)*ε*En := by
  have hProd : s*u ≤ 4*En := by
    have hh := weighted_product_le s u β hβ
    linarith only [hh,hGrad,hMass]
  have hG := mul_le_mul_of_nonneg_left hGrad (by positivity : 0 ≤ B*Q*ε)
  have hM := mul_le_mul_of_nonneg_left hMass (by positivity : 0 ≤ Z*R*ε)
  have hP0 := mul_le_mul_of_nonneg_left hProd (by positivity : 0 ≤ Z*Q*ε)
  have hP1 := mul_le_mul_of_nonneg_left hProd (by positivity : 0 ≤ B*R*ε)
  have hEq : (B*ε/β*s+Z*ε*u)*(Q*s+R*β*u)=
      (B*Q*ε)*(β⁻¹*s^2)+(Z*R*ε)*(β*u^2)+(Z*Q*ε)*(s*u)+(B*R*ε)*(s*u) := by
    field_simp [hβ.ne'] <;> ring
  rw [hEq]
  nlinarith only [hG,hM,hP0,hP1]

lemma scalar_model_defect_pair_bound
    (F : SphereSobolev (1/2:ℝ)) (M : SphereSobolev (-(1/2:ℝ)))
    (s u B Z Q R ε β En : ℝ)
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) (hβ : 0 < β)
    (hF : ‖F‖ ≤ B*ε/β*s+Z*ε*u) (hM : ‖M‖ ≤ Q*s+R*β*u)
    (hGrad : β⁻¹*s^2 ≤ 3*En) (hMass : β*u^2 ≤ En) :
    |sphereSobolevDualPairing (1/2:ℝ) F M| ≤
      (3*B*Q+4*Z*Q+4*B*R+Z*R)*ε*En := by
  exact ((abs_sphereSobolevDualPairing_le _ _ _).trans
    (mul_le_mul hF hM (norm_nonneg _) (by positivity))).trans
      (scalar_model_defect_product_real s u B Z Q R ε β En hs hu hB hZ hQ hR hε hβ hGrad hMass)

end ShrinkingSpheres.ParallelEnergy
