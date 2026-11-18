import Proof.ParallelNormAssemblyReservedScalarGreen
import Proof.CoarseProductFirstDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma scalar_quadratic_green_row_bound
    (q dq Q0 Q1 CN CJ ε β μ En : ℝ)
    (v : SphereSobolev (1/2:ℝ)) (u : SphereSobolev (3/2:ℝ))
    (D N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hCN : 0 ≤ CN) (hCJ : 0 ≤ CJ)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ) (hEn : 0 ≤ En)
    (hq : |q| ≤ Q0*ε/β^2*μ) (hdq : |dq| ≤ Q1*ε/β*μ)
    (hD : ‖D‖ ≤ CN*ε) (hN : ‖N‖ ≤ CJ*ε*β)
    (hV : β⁻¹*‖v‖^2 ≤ En) (hM : β*‖u‖^2 ≤ En) :
    |-q*sphereSobolevDualPairing (1/2:ℝ) v (N u)-dq*sphereSobolevDualPairing (1/2:ℝ) v (D u)| ≤
      2*(Q0*CJ+Q1*CN)*ε^2*μ*En := by
  have hβp := zero_lt_one.trans_le hβ
  have hPairN : |sphereSobolevDualPairing (1/2:ℝ) v (N u)| ≤ ‖v‖*(CJ*ε*β*‖u‖) :=
    (abs_sphereSobolevDualPairing_le _ _ _).trans (mul_le_mul_of_nonneg_left
      ((N.le_opNorm u).trans (mul_le_mul_of_nonneg_right hN (norm_nonneg u))) (norm_nonneg v))
  have hPairD : |sphereSobolevDualPairing (1/2:ℝ) v (D u)| ≤ ‖v‖*(CN*ε*‖u‖) :=
    (abs_sphereSobolevDualPairing_le _ _ _).trans (mul_le_mul_of_nonneg_left
      ((D.le_opNorm u).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg u))) (norm_nonneg v))
  have hProd : ‖v‖*‖u‖ ≤ 2*En := (weighted_product_le ‖v‖ ‖u‖ β hβp).trans
    ((add_le_add hV hM).trans_eq (by ring))
  have hC : 0 ≤ (Q0*CJ+Q1*CN)*ε^2*μ := by positivity
  calc
    _ ≤ |-q*sphereSobolevDualPairing (1/2:ℝ) v (N u)|+
        |dq*sphereSobolevDualPairing (1/2:ℝ) v (D u)| := abs_sub _ _
    _ = |q| *|sphereSobolevDualPairing (1/2:ℝ) v (N u)|+
        |dq| *|sphereSobolevDualPairing (1/2:ℝ) v (D u)| := by rw [abs_mul,abs_neg,abs_mul]
    _ ≤ (Q0*ε/β^2*μ)*(‖v‖*(CJ*ε*β*‖u‖))+
        (Q1*ε/β*μ)*(‖v‖*(CN*ε*‖u‖)) := add_le_add
      (mul_le_mul hq hPairN (abs_nonneg _) (by positivity))
      (mul_le_mul hdq hPairD (abs_nonneg _) (by positivity))
    _ = ((Q0*CJ+Q1*CN)*ε^2*μ/β)*(‖v‖*‖u‖) := by field_simp <;> ring
    _ ≤ ((Q0*CJ+Q1*CN)*ε^2*μ/β)*(2*En) :=
      mul_le_mul_of_nonneg_left hProd (div_nonneg hC hβp.le)
    _ ≤ ((Q0*CJ+Q1*CN)*ε^2*μ)*(2*En) :=
      mul_le_mul_of_nonneg_right (div_le_self hC hβ) (mul_nonneg (by norm_num) hEn)
    _ = _ := by ring

/-- The entire scalar/quadratic Green remainder has epsilon squared
original-energy scale. Horizontal values are used ONLY at H1/2. -/
theorem scalar_quadratic_second_remainder_bound
    (q : I → I → X → ℝ)
    (D : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (DQ : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : I → X → SphereSobolev (3/2:ℝ)) (U : X → SphereSobolev (5/2:ℝ)) (y : X)
    (Q0 Q1 CN CJ ε β μ En : ℝ)
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hCN : 0 ≤ CN) (hCJ : 0 ≤ CJ)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ) (hEn : 0 ≤ En)
    (hq : ∀ a b,|q a b y| ≤ Q0*ε/β^2*μ)
    (hdq : ∀ a b,|fderiv ℝ (q a b) y (axis a)| ≤ Q1*ε/β*μ)
    (hD : ‖D y‖ ≤ CN*ε) (hN : ∀ a,‖DQ a y‖ ≤ CJ*ε*β)
    (hV : ∀ b,β⁻¹*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b y)‖^2 ≤ En)
    (hM : β*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 ≤ En) :
    |scalarQuadraticSecondRemainder q D DQ H U y| ≤ 18*(Q0*CJ+Q1*CN)*ε^2*μ*En := by
  have hRow (a b : I) := scalar_quadratic_green_row_bound (q a b y) (fderiv ℝ (q a b) y (axis a))
    Q0 Q1 CN CJ ε β μ En (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b y))
    (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) (D y) (DQ a y)
    hQ0 hQ1 hCN hCJ hε hβ hμ hEn (hq a b) (hdq a b) hD (hN a) (hV b) hM
  calc
    _ ≤ ∑ a : I,∑ b : I,|-q a b y*sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b y))
        (DQ a y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))-
      fderiv ℝ (q a b) y (axis a)*sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b y))
        (D y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _a : I,∑ _b : I,2*(Q0*CJ+Q1*CN)*ε^2*μ*En :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hRow a b))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

end ShrinkingSpheres.ParallelEnergy
