import Proof.ParallelScalarFirstTripleIntegral
import Proof.ScalarSecondCovariantFirstForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_product_inv_le_energy (u v β E : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hβ : 0 < β)
    (hU : β⁻¹*u^2 ≤ E) (hV : β⁻¹*v^2 ≤ E) : β⁻¹*u*v ≤ 2*E := by
  have hP : u*v ≤ u^2+v^2 := by nlinarith only [sq_nonneg (u-v)]
  have hQ := mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hβ.le)
  nlinarith only [hQ,hU,hV]

lemma abs_negative_three_le (x y z A : ℝ) (hx : |x| ≤ A) (hy : |y| ≤ A) (hz : |z| ≤ A) :
    |-x-y+z| ≤ 3*A := by
  have h1 := abs_add_le (-x-y) z
  have h2 := abs_sub (-x) y
  rw [abs_neg] at h2
  linarith only [h1,h2,hx,hy,hz]

lemma abs_positive_three_le (x y z A : ℝ) (hx : |x| ≤ A) (hy : |y| ≤ A) (hz : |z| ≤ A) :
    |x+y-z| ≤ 3*A := by
  have h1 := abs_sub (x+y) z
  have h2 := abs_add_le x y
  linarith only [h1,h2,hx,hy,hz]

/-- Pointwise original-energy form bound for the fully reduced leading
third-base remainder. Only strong low-domain first-jet values and the
actual curvature value bound are used. -/
theorem halfCovariantThirdRemainder_bound
    (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (H : X → X → SphereSobolev (3/2:ℝ))
    (R : X → X → X → SphereSobolev (1/2:ℝ)) (y : X) (i j k : I)
    (u : SphereSobolev (3/2:ℝ)) (Q M CR ε β E : ℝ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hCR : 0 ≤ CR) (hq : 0 ≤ q y) (hβ : 1 ≤ β)
    (hC : ‖C y‖ ≤ Q*ε^2/β)
    (hDC : ∀ a b : I,‖halfOperatorCovariantDerivativeL d C Ch y (axis a) (H (axis b) y)‖ ≤
      Q*ε^2/β*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H (axis b) y)‖)
    (hDq : ∀ a : I,|fderiv ℝ q y (axis a)| ≤ M*q y)
    (hR : ∀ a b : I,‖R (axis a) (axis b) y‖ ≤ CR*‖u‖)
    (hV : ∀ a : I,β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H (axis a) y)‖^2 ≤ E)
    (hU : β*‖u‖^2 ≤ E) :
    |halfCovariantThirdRemainder d q C Ch H R (axis i) (axis j) (axis k) y| ≤
      6*Q*(M+CR+1)*ε^2*q y*E := by
  let V := fun a : I => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H (axis a) y)
  have hβpos := zero_lt_one.trans_le hβ
  have hE : 0 ≤ E := (mul_nonneg (inv_nonneg.mpr hβpos.le) (sq_nonneg ‖V 0‖)).trans (hV 0)
  have hProd (a b : I) : β⁻¹*‖V a‖*‖V b‖ ≤ 2*E :=
    norm_product_inv_le_energy _ _ β E (norm_nonneg _) (norm_nonneg _) hβpos (hV a) (hV b)
  have hPair (a b : I) : |halfPair C (H (axis a)) (H (axis b)) y| ≤ 2*Q*ε^2*E := by
    calc
      _ ≤ ‖V a‖*‖C y (V b)‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖V a‖*(‖C y‖*‖V b‖) := mul_le_mul_of_nonneg_left ((C y).le_opNorm _) (norm_nonneg _)
      _ ≤ ‖V a‖*((Q*ε^2/β)*‖V b‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hC (norm_nonneg _)) (norm_nonneg _)
      _ = (Q*ε^2)*(β⁻¹*‖V a‖*‖V b‖) := by ring
      _ ≤ (Q*ε^2)*(2*E) := mul_le_mul_of_nonneg_left (hProd a b) (mul_nonneg hQ (sq_nonneg ε))
      _ = _ := by ring
  have hDer (a b c : I) : |halfPairCoefficientDerivative d C Ch (H (axis a)) (H (axis b)) y (axis c)| ≤
      2*Q*ε^2*E := by
    calc
      _ ≤ ‖V a‖*‖halfOperatorCovariantDerivativeL d C Ch y (axis c) (H (axis b) y)‖ :=
        abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖V a‖*((Q*ε^2/β)*‖V b‖) := mul_le_mul_of_nonneg_left (hDC c b) (norm_nonneg _)
      _ = (Q*ε^2)*(β⁻¹*‖V a‖*‖V b‖) := by ring
      _ ≤ (Q*ε^2)*(2*E) := mul_le_mul_of_nonneg_left (hProd a b) (mul_nonneg hQ (sq_nonneg ε))
      _ = _ := by ring
  have hMassProd (a : I) : β⁻¹*‖u‖*‖V a‖ ≤ 2*E := by
    calc
      _ = (‖u‖*‖V a‖)/β := by ring
      _ ≤ ‖u‖*‖V a‖ := div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hβ
      _ = ‖V a‖*‖u‖ := mul_comm _ _
      _ ≤ β⁻¹*‖V a‖^2+β*‖u‖^2 := weighted_product_le _ _ β hβpos
      _ ≤ 2*E := by linarith only [hV a,hU]
  have hCurv (a b c : I) : |sphereSobolevDualPairing (1/2:ℝ) (R (axis a) (axis b) y) (C y (V c))| ≤
      2*CR*Q*ε^2*E := by
    calc
      _ ≤ ‖R (axis a) (axis b) y‖*‖C y (V c)‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ (CR*‖u‖)*((Q*ε^2/β)*‖V c‖) := mul_le_mul (hR a b)
        (((C y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _)))
        (norm_nonneg _) (mul_nonneg hCR (norm_nonneg _))
      _ = (CR*Q*ε^2)*(β⁻¹*‖u‖*‖V c‖) := by ring
      _ ≤ (CR*Q*ε^2)*(2*E) := mul_le_mul_of_nonneg_left (hMassProd c) (by positivity)
      _ = _ := by ring
  let D0 := 2*Q*ε^2*q y*E
  have hWeightedPair (a b c : I) : |fderiv ℝ q y (axis a)*halfPair C (H (axis b)) (H (axis c)) y| ≤ M*D0 := by
    rw [abs_mul]
    exact (mul_le_mul (hDq a) (hPair b c) (abs_nonneg _) (mul_nonneg hM hq)).trans_eq (by dsimp only [D0];ring)
  have hWeightedDer (a b c : I) : |q y*halfPairCoefficientDerivative d C Ch (H (axis a)) (H (axis b)) y (axis c)| ≤ D0 := by
    rw [abs_mul,abs_of_nonneg hq]
    exact (mul_le_mul_of_nonneg_left (hDer a b c) hq).trans_eq (by dsimp only [D0];ring)
  have hWeightedCurv (a b c : I) : |q y*sphereSobolevDualPairing (1/2:ℝ) (R (axis a) (axis b) y) (C y (V c))| ≤ CR*D0 := by
    rw [abs_mul,abs_of_nonneg hq]
    exact (mul_le_mul_of_nonneg_left (hCurv a b c) hq).trans_eq (by dsimp only [D0];ring)
  have h1 := abs_negative_three_le _ _ _ (M*D0) (hWeightedPair i j k) (hWeightedPair j i k) (hWeightedPair k i j)
  have h2 := abs_negative_three_le _ _ _ D0 (hWeightedDer j k i) (hWeightedDer i k j) (hWeightedDer i j k)
  have h3 := abs_positive_three_le _ _ _ (CR*D0) (hWeightedCurv i j k) (hWeightedCurv k j i) (hWeightedCurv i k j)
  have hSum := abs_add_le
    (-fderiv ℝ q y (axis i)*halfPair C (H (axis j)) (H (axis k)) y-
      fderiv ℝ q y (axis j)*halfPair C (H (axis i)) (H (axis k)) y+
      fderiv ℝ q y (axis k)*halfPair C (H (axis i)) (H (axis j)) y)
    (-q y*halfPairCoefficientDerivative d C Ch (H (axis j)) (H (axis k)) y (axis i)-
      q y*halfPairCoefficientDerivative d C Ch (H (axis i)) (H (axis k)) y (axis j)+
      q y*halfPairCoefficientDerivative d C Ch (H (axis i)) (H (axis j)) y (axis k))
  have hAll := abs_add_le
    ((-fderiv ℝ q y (axis i)*halfPair C (H (axis j)) (H (axis k)) y-
      fderiv ℝ q y (axis j)*halfPair C (H (axis i)) (H (axis k)) y+
      fderiv ℝ q y (axis k)*halfPair C (H (axis i)) (H (axis j)) y)+
    (-q y*halfPairCoefficientDerivative d C Ch (H (axis j)) (H (axis k)) y (axis i)-
      q y*halfPairCoefficientDerivative d C Ch (H (axis i)) (H (axis k)) y (axis j)+
      q y*halfPairCoefficientDerivative d C Ch (H (axis i)) (H (axis j)) y (axis k)))
    (q y*sphereSobolevDualPairing (1/2:ℝ) (R (axis i) (axis j) y) (C y (V k))+
      q y*sphereSobolevDualPairing (1/2:ℝ) (R (axis k) (axis j) y) (C y (V i))-
      q y*sphereSobolevDualPairing (1/2:ℝ) (R (axis i) (axis k) y) (C y (V j)))
  have hExpr : halfCovariantThirdRemainder d q C Ch H R (axis i) (axis j) (axis k) y=
      (-fderiv ℝ q y (axis i)*halfPair C (H (axis j)) (H (axis k)) y-
        fderiv ℝ q y (axis j)*halfPair C (H (axis i)) (H (axis k)) y+
        fderiv ℝ q y (axis k)*halfPair C (H (axis i)) (H (axis j)) y)+
      (-q y*halfPairCoefficientDerivative d C Ch (H (axis j)) (H (axis k)) y (axis i)-
        q y*halfPairCoefficientDerivative d C Ch (H (axis i)) (H (axis k)) y (axis j)+
        q y*halfPairCoefficientDerivative d C Ch (H (axis i)) (H (axis j)) y (axis k))+
      (q y*sphereSobolevDualPairing (1/2:ℝ) (R (axis i) (axis j) y) (C y (V k))+
        q y*sphereSobolevDualPairing (1/2:ℝ) (R (axis k) (axis j) y) (C y (V i))-
        q y*sphereSobolevDualPairing (1/2:ℝ) (R (axis i) (axis k) y) (C y (V j))) := by
    dsimp only [halfCovariantThirdRemainder,V]
    ring
  rw [hExpr]
  dsimp only [D0] at h1 h2 h3
  simp only [neg_mul] at hSum hAll ⊢
  nlinarith only [h1,h2,h3,hSum,hAll]

end ShrinkingSpheres.ParallelEnergy
