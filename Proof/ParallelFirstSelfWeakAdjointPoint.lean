import Proof.ParallelFirstSelfAdjointNormalForm
import Proof.UniformEffectiveFirstLowEndpointData
import Proof.UniformEffectiveFirstBalancedDerivative
import Proof.UniformActualHalfCovariantFirstForm
import Proof.SphereFiberBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_three_sum_sq_le {F : Type*} [SeminormedAddCommGroup F] (a b c : F) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  simpa [Fin.sum_univ_three] using norm_fin_three_sum_sq_le ![a,b,c]

/-- A genuine weak adjoint row uses only the low coefficient, its genuine
covariant derivative, and the relative physical-density derivative. -/
lemma weak_adjoint_row_norm_sq_le
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev (1/2:ℝ))
    {CB CD MQ ε β q : ℝ} (hCB : 0 ≤ CB) (hCD : 0 ≤ CD) (hMQ : 0 ≤ MQ)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hC : ‖C‖ ≤ CB*ε/β) (hD : ‖D‖ ≤ CD*ε) (hq : |q| ≤ MQ) :
    ‖C v+D u+q • C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)‖^2 ≤
      (3*(CB^2+CD^2+(MQ*CB)^2))*ε^2*(β⁻¹*‖v‖^2+β*‖u‖^2) := by
  let W := β⁻¹*‖v‖^2+β*‖u‖^2
  have hβ0 : 0 < β := zero_lt_one.trans_le hβ
  have hi0 : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ0.le
  have hi1 : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  have hi2 : (β⁻¹)^2 ≤ β⁻¹ := by nlinarith only [hi0,hi1]
  have hWv : β⁻¹*‖v‖^2 ≤ W := le_add_of_nonneg_right (mul_nonneg hβ0.le (sq_nonneg _))
  have hWu : ‖u‖^2 ≤ W := by
    have hh := mul_le_mul_of_nonneg_right hβ (sq_nonneg ‖u‖)
    have hn : 0 ≤ β⁻¹*‖v‖^2 := mul_nonneg hi0 (sq_nonneg _)
    dsimp only [W]
    nlinarith only [hh,hn]
  have hCv : ‖C v‖ ≤ CB*ε*β⁻¹*‖v‖ := by
    simpa only [div_eq_mul_inv] using (C.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  have hCv2 : ‖C v‖^2 ≤ (CB^2*ε^2)*W := by
    calc
      _ ≤ (CB*ε*β⁻¹*‖v‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hCv
      _ = (CB^2*ε^2)*((β⁻¹)^2*‖v‖^2) := by ring
      _ ≤ (CB^2*ε^2)*(β⁻¹*‖v‖^2) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hi2 (sq_nonneg _)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hWv (by positivity)
  have hDu : ‖D u‖ ≤ CD*ε*‖u‖ := (D.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hDu2 : ‖D u‖^2 ≤ (CD^2*ε^2)*W := by
    calc
      _ ≤ (CD*ε*‖u‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hDu
      _ = (CD^2*ε^2)*‖u‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWu (by positivity)
  have hCJ : ‖C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)‖ ≤ CB*ε*‖u‖ := by
    have hCN : ‖C‖ ≤ CB*ε := hC.trans (div_le_self (mul_nonneg hCB hε) hβ)
    have hJN : ‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u‖ ≤ ‖u‖ :=
      ((sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).le_opNorm u).trans
        ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (one_mul _))
    exact (C.le_opNorm _).trans ((mul_le_mul hCN hJN (norm_nonneg _) (mul_nonneg hCB hε)).trans_eq (by ring))
  have hqC : ‖q • C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)‖ ≤ MQ*CB*ε*‖u‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hq hCJ (norm_nonneg _) hMQ).trans_eq (by ring)
  have hqC2 : ‖q • C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)‖^2 ≤ ((MQ*CB)^2*ε^2)*W := by
    calc
      _ ≤ (MQ*CB*ε*‖u‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hqC
      _ = ((MQ*CB)^2*ε^2)*‖u‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWu (by positivity)
  exact (norm_three_sum_sq_le _ _ _).trans
    ((mul_le_mul_of_nonneg_left (add_le_add (add_le_add hCv2 hDu2) hqC2) (by norm_num)).trans_eq (by ring))

end ShrinkingSpheres.ParallelEnergy
