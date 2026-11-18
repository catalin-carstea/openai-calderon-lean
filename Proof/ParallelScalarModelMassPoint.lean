import Proof.ParallelScalarModelPairedMass
import Proof.ParallelScalarFirstRemainderPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The paired degree remainder is controlled at linear epsilon scale,
retaining the mass/gradient beta weights before taking products. -/
theorem pairedHalfMassRemainderTerm_bound
    (d : Data) (q : X → ℝ)
    (C0 C1 : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch0 Ch1 : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U0 U1 V : X → SphereSobolev (3/2:ℝ)) (y a : X)
    (u : SphereSobolev (3/2:ℝ)) (A0 A1 L QR QD ε β μ E : ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hL : 0 ≤ L) (hQR : 0 ≤ QR) (hQD : 0 ≤ QD)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ)
    (hq : |q y| ≤ A0*ε/β*μ) (hDq : |fderiv ℝ q y a| ≤ A1*ε*μ)
    (hU0 : ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U0 y)‖ ≤ L*‖u‖)
    (hU1 : ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U1 y)‖ ≤ L*‖u‖)
    (hC0 : ‖C0 y‖ ≤ QR) (hC1 : ‖C1 y‖ ≤ QR)
    (hDC0 : ‖halfOperatorCovariantDerivativeL d C0 Ch0 y a (V y)‖ ≤
      QD*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V y)‖)
    (hDC1 : ‖halfOperatorCovariantDerivativeL d C1 Ch1 y a (V y)‖ ≤
      QD*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V y)‖)
    (hV : β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V y)‖^2 ≤ E)
    (hMass : β*‖u‖^2 ≤ E) :
    |pairedHalfMassRemainderTerm d q C0 C1 Ch0 Ch1 U0 U1 V a y| ≤
      4*L*(A0*QD+A1*QR)*ε*μ*E := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let v := J (V y)
  have hβp : 0 < β := zero_lt_one.trans_le hβ
  have hProd : ‖u‖*‖v‖ ≤ 2*E := by
    have hh := weighted_product_le ‖v‖ ‖u‖ β hβp
    nlinarith only [hh,hV,hMass]
  have hProdInv : ‖u‖*‖v‖/β ≤ 2*E :=
    (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hβ).trans hProd
  have hPair (U : SphereSobolev (1/2:ℝ)) (Z : SphereSobolev (-(1/2:ℝ)))
      (B : ℝ) (hB : 0 ≤ B) (hU : ‖U‖ ≤ L*‖u‖) (hZ : ‖Z‖ ≤ B*‖v‖) :
      |sphereSobolevDualPairing (1/2:ℝ) U Z| ≤ L*B*(‖u‖*‖v‖) := by
    exact ((abs_sphereSobolevDualPairing_le _ _ _).trans
      (mul_le_mul hU hZ (norm_nonneg _) (by positivity))).trans_eq (by ring)
  have hD0 := hPair (J (U0 y)) (halfOperatorCovariantDerivativeL d C0 Ch0 y a (V y)) QD hQD hU0 hDC0
  have hD1 := hPair (J (U1 y)) (halfOperatorCovariantDerivativeL d C1 Ch1 y a (V y)) QD hQD hU1 hDC1
  have hP0 := hPair (J (U0 y)) (C0 y v) QR hQR hU0
    (((C0 y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hC0 (norm_nonneg _)))
  have hP1 := hPair (J (U1 y)) (C1 y v) QR hQR hU1
    (((C1 y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hC1 (norm_nonneg _)))
  let D := sphereSobolevDualPairing (1/2:ℝ) (J (U0 y)) (halfOperatorCovariantDerivativeL d C0 Ch0 y a (V y))-
    sphereSobolevDualPairing (1/2:ℝ) (J (U1 y)) (halfOperatorCovariantDerivativeL d C1 Ch1 y a (V y))
  let P := sphereSobolevDualPairing (1/2:ℝ) (J (U0 y)) (C0 y v)-
    sphereSobolevDualPairing (1/2:ℝ) (J (U1 y)) (C1 y v)
  have hD : |D| ≤ 2*L*QD*(‖u‖*‖v‖) := by
    dsimp only [D]
    exact (abs_sub _ _).trans ((add_le_add hD0 hD1).trans_eq (by ring))
  have hP : |P| ≤ 2*L*QR*(‖u‖*‖v‖) := by
    dsimp only [P]
    exact (abs_sub _ _).trans ((add_le_add hP0 hP1).trans_eq (by ring))
  have hWD : |q y*D| ≤ 4*A0*L*QD*ε*μ*E := by
    rw [abs_mul]
    calc
      _ ≤ (A0*ε/β*μ)*(2*L*QD*(‖u‖*‖v‖)) := mul_le_mul hq hD (abs_nonneg _) (by positivity)
      _ = (2*A0*L*QD*ε*μ)*(‖u‖*‖v‖/β) := by ring
      _ ≤ (2*A0*L*QD*ε*μ)*(2*E) := mul_le_mul_of_nonneg_left hProdInv (by positivity)
      _ = _ := by ring
  have hWP : |fderiv ℝ q y a*P| ≤ 4*A1*L*QR*ε*μ*E := by
    rw [abs_mul]
    calc
      _ ≤ (A1*ε*μ)*(2*L*QR*(‖u‖*‖v‖)) := mul_le_mul hDq hP (abs_nonneg _) (by positivity)
      _ = (2*A1*L*QR*ε*μ)*(‖u‖*‖v‖) := by ring
      _ ≤ (2*A1*L*QR*ε*μ)*(2*E) := mul_le_mul_of_nonneg_left hProd (by positivity)
      _ = _ := by ring
  change |-q y*D-fderiv ℝ q y a*P| ≤ _
  have hh := abs_sub (-q y*D) (fderiv ℝ q y a*P)
  rw [neg_mul,abs_neg] at hh
  rw [neg_mul]
  calc
    _ ≤ |q y*D|+|fderiv ℝ q y a*P| := hh
    _ ≤ 4*A0*L*QD*ε*μ*E+4*A1*L*QR*ε*μ*E := add_le_add hWD hWP
    _ = 4*L*(A0*QD+A1*QR)*ε*μ*E := by ring

end ShrinkingSpheres.ParallelEnergy
