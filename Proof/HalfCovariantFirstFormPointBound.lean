import Proof.FirstOperatorFormPointBound
import Proof.HalfCovariantEnergyControl
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def halfDualPairingNorm : ℝ :=
  ‖(innerSL ℝ : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) →L[ℝ] ℝ)‖

/-- Pointwise bound for the actual covariant Green integrand. The only
    analytic inputs are the displayed coefficient and covariant-derivative
    norms, with the manuscript's epsilon/beta and epsilon weights. -/
lemma half_covariant_first_integrand_bound (d : Data) (U : X → SphereSobolev (3/2:ℝ)) (y a : X)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (mu dmu β Q M eps : ℝ) (hmu : 0 ≤ mu) (hβ : 1 ≤ β) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hC : ‖C y‖ ≤ Q*eps/β) (hDC : ‖halfOperatorCovariantDerivativeL d C Ch y a‖ ≤ Q*eps)
    (hdmu : |dmu| ≤ M*mu) :
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let V := halfSectionCovariantDerivativeL d U y a
    |dmu*sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (J (U y)))+
      mu*sphereSobolevDualPairing (1/2:ℝ) V (C y (J (U y)))+
      mu*sphereSobolevDualPairing (1/2:ℝ) (J (U y))
        (halfOperatorCovariantDerivativeL d C Ch y a (U y))| ≤
      (halfDualPairingNorm*Q*(M+3)*eps)*(mu*halfCovariantDirectionEnergy d U y β a) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let P : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) →L[ℝ] ℝ := innerSL ℝ
  let V := halfSectionCovariantDerivativeL d U y a
  let W := halfCovariantDirectionEnergy d U y β a
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hW : 0 ≤ W := by dsimp only [W,halfCovariantDirectionEnergy];positivity
  have hMass : ‖U y‖^2 ≤ W := by
    have hh := mul_le_mul_of_nonneg_right hβ (sq_nonneg ‖U y‖)
    have h0 : 0 ≤ β⁻¹*‖V‖^2 := by positivity
    dsimp only [W,halfCovariantDirectionEnergy]
    dsimp only [V] at h0
    nlinarith only [hh,h0]
  have hMixed : ‖V‖*‖U y‖ ≤ W :=
    weighted_product_le ‖V‖ ‖U y‖ β (zero_lt_one.trans_le hβ)
  have hJN : ‖J‖ ≤ 1 := norm_sphereSobolevInclusionL_le _ _ _
  have hCN : ‖(C y).comp J‖ ≤ Q*eps/β :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul_of_nonneg_left hJN (norm_nonneg (C y))).trans_eq (mul_one _)).trans hC)
  have hRaw := OperatorForms.reduced_first_point_bound P J ((C y).comp J)
    (halfOperatorCovariantDerivativeL d C Ch y a) (U y) V mu dmu β Q M eps W
    hmu hβ hQ hM heps hW hMass hMixed hCN hDC hdmu
  have hA : (M+1)*‖J‖+2 ≤ M+3 := by
    have hh := mul_le_mul_of_nonneg_left hJN (show 0 ≤ M+1 by linarith)
    linarith only [hh]
  have hCoef := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (mul_nonneg P.opNorm_nonneg hQ)) heps
  exact hRaw.trans (mul_le_mul_of_nonneg_right hCoef (mul_nonneg hmu hW))
end ShrinkingSpheres
