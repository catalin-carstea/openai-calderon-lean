import Proof.ParallelScalarFirstMassReduction
import Proof.ParallelScalarFirstRemainderPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A signed scalar second-order weight and a genuine first coefficient
jet give an original-energy bound after one covariant Green operation. -/
theorem halfCovariantSecondMassRemainder_bound
    (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U V : X → SphereSobolev (3/2:ℝ)) (y a : X)
    (A Q ε β μ E : ℝ) (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ)
    (hq : |q y| ≤ A*ε/β^2*μ) (hDq : |fderiv ℝ q y a| ≤ A*ε/β*μ)
    (hC : ‖C y‖ ≤ Q*ε)
    (hDC : ‖halfOperatorCovariantDerivativeL d C Ch y a (V y)‖ ≤
      Q*ε*β*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V y)‖)
    (hDU : β⁻¹*‖halfSectionCovariantDerivativeL d U y a‖^2 ≤ E)
    (hV : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V y)‖^2 ≤ E)
    (hU : β*‖U y‖^2 ≤ E) :
    |halfCovariantSecondMassRemainder d q C Ch U V a y| ≤ 6*A*Q*ε^2*μ*E := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let u := J (U y)
  let v := J (V y)
  let du := halfSectionCovariantDerivativeL d U y a
  have hβp : 0 < β := zero_lt_one.trans_le hβ
  have hu : ‖u‖ ≤ ‖U y‖ := by
    calc
      _ ≤ ‖J‖*‖U y‖ := J.le_opNorm _
      _ ≤ 1*‖U y‖ := mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)
      _ = _ := one_mul _
  have hE : 0 ≤ E := (mul_nonneg hβp.le (sq_nonneg ‖U y‖)).trans hU
  have hGrad : ‖du‖*‖v‖/β^2 ≤ 2*E := by
    have h0 := norm_product_inv_le_energy ‖du‖ ‖v‖ β E (norm_nonneg _) (norm_nonneg _) hβp hDU hV
    calc
      _ = (β⁻¹*‖du‖*‖v‖)/β := by field_simp <;> ring
      _ ≤ β⁻¹*‖du‖*‖v‖ := div_le_self (by positivity) hβ
      _ ≤ _ := h0
  have hMass : ‖u‖*‖v‖/β ≤ 2*E := by
    calc
      _ ≤ ‖U y‖*‖v‖/β := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hu (norm_nonneg _)) hβp.le
      _ ≤ ‖U y‖*‖v‖ := div_le_self (by positivity) hβ
      _ = ‖v‖*‖U y‖ := mul_comm _ _
      _ ≤ β⁻¹*‖v‖^2+β*‖U y‖^2 := weighted_product_le _ _ β hβp
      _ ≤ 2*E := by linarith only [hV,hU]
  have hMass2 : ‖u‖*‖v‖/β^2 ≤ 2*E := by
    calc
      _ = (‖u‖*‖v‖/β)/β := by ring
      _ ≤ ‖u‖*‖v‖/β := div_le_self (by positivity) hβ
      _ ≤ _ := hMass
  let B := 2*A*Q*ε^2*μ*E
  have h0 : |q y*sphereSobolevDualPairing (1/2:ℝ) du (C y v)| ≤ B := by
    have hPair : |sphereSobolevDualPairing (1/2:ℝ) du (C y v)| ≤ ‖du‖*(Q*ε*‖v‖) :=
      (abs_sphereSobolevDualPairing_le _ _ _).trans (mul_le_mul_of_nonneg_left
        (((C y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))) (norm_nonneg _))
    rw [abs_mul]
    calc
      _ ≤ (A*ε/β^2*μ)*(‖du‖*(Q*ε*‖v‖)) := mul_le_mul hq hPair (abs_nonneg _) (by positivity)
      _ = (A*Q*ε^2*μ)*(‖du‖*‖v‖/β^2) := by ring
      _ ≤ (A*Q*ε^2*μ)*(2*E) := mul_le_mul_of_nonneg_left hGrad (by positivity)
      _ = B := by dsimp only [B];ring
  have h1 : |q y*sphereSobolevDualPairing (1/2:ℝ) u
      (halfOperatorCovariantDerivativeL d C Ch y a (V y))| ≤ B := by
    have hPair : |sphereSobolevDualPairing (1/2:ℝ) u
        (halfOperatorCovariantDerivativeL d C Ch y a (V y))| ≤ ‖u‖*(Q*ε*β*‖v‖) :=
      (abs_sphereSobolevDualPairing_le _ _ _).trans (mul_le_mul_of_nonneg_left hDC (norm_nonneg _))
    rw [abs_mul]
    calc
      _ ≤ (A*ε/β^2*μ)*(‖u‖*(Q*ε*β*‖v‖)) := mul_le_mul hq hPair (abs_nonneg _) (by positivity)
      _ = (A*Q*ε^2*μ)*(‖u‖*‖v‖/β) := by field_simp <;> ring
      _ ≤ (A*Q*ε^2*μ)*(2*E) := mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = B := by dsimp only [B];ring
  have h2 : |fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) u (C y v)| ≤ B := by
    have hPair : |sphereSobolevDualPairing (1/2:ℝ) u (C y v)| ≤ ‖u‖*(Q*ε*‖v‖) :=
      (abs_sphereSobolevDualPairing_le _ _ _).trans (mul_le_mul_of_nonneg_left
        (((C y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))) (norm_nonneg _))
    rw [abs_mul]
    calc
      _ ≤ (A*ε/β*μ)*(‖u‖*(Q*ε*‖v‖)) := mul_le_mul hDq hPair (abs_nonneg _) (by positivity)
      _ = (A*Q*ε^2*μ)*(‖u‖*‖v‖/β) := by ring
      _ ≤ (A*Q*ε^2*μ)*(2*E) := mul_le_mul_of_nonneg_left hMass (by positivity)
      _ = B := by dsimp only [B];ring
  have hh := abs_negative_three_le
    (q y*sphereSobolevDualPairing (1/2:ℝ) du (C y v))
    (q y*sphereSobolevDualPairing (1/2:ℝ) u (halfOperatorCovariantDerivativeL d C Ch y a (V y)))
    (-fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) u (C y v)) B h0 h1
    (by simpa only [neg_mul,abs_neg] using h2)
  have hEq : halfCovariantSecondMassRemainder d q C Ch U V a y=
      -(q y*sphereSobolevDualPairing (1/2:ℝ) du (C y v))-
        (q y*sphereSobolevDualPairing (1/2:ℝ) u (halfOperatorCovariantDerivativeL d C Ch y a (V y)))+
        (-fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) u (C y v)) := by
    dsimp only [halfCovariantSecondMassRemainder,du,u,v,J]
    ring
  rw [hEq]
  exact hh.trans_eq (by dsimp only [B];ring)

end ShrinkingSpheres.ParallelEnergy
