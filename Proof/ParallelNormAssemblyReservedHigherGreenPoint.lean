import Proof.ParallelNormAssemblyReservedHigherGreen

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

private lemma abs_applied_half_pair_le
    (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (B : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (u : SphereSobolev (3/2:ℝ)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) :
    |sphereSobolevDualPairing (1/2:ℝ) (A u) (B u)| ≤ a*b*‖u‖^2 := by
  calc
    _ ≤ ‖A u‖*‖B u‖ := abs_sphereSobolevDualPairing_le _ _ _
    _ ≤ (a*‖u‖)*(b*‖u‖) := mul_le_mul
      ((A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg u)))
      ((B.le_opNorm u).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg u)))
      (norm_nonneg _) (mul_nonneg ha (norm_nonneg u))
    _ = _ := by ring

/-- The paired Green remainder has only the original H3/2 mass term.
The derivative of the quadratic potential costs one beta, exactly matched
by the frozen energy. No horizontal H3/2 norm is introduced. -/
theorem quadratic_higher_pair_remainder_bound
    (q : X → ℝ)
    (H N : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C DQ : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) (a y : X)
    (Q Q1 CH CN CQ CD ε β μ : ℝ)
    (hQ : 0 ≤ Q) (hQ1 : 0 ≤ Q1) (hCH : 0 ≤ CH) (hCN : 0 ≤ CN)
    (hCQ : 0 ≤ CQ) (hCD : 0 ≤ CD) (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hμ : 0 ≤ μ)
    (hq : |q y| ≤ Q*μ) (hdq : |fderiv ℝ q y a| ≤ Q1*μ)
    (hH : ‖H y‖ ≤ CH) (hN : ‖N y‖ ≤ CN*β)
    (hC : ‖C y‖ ≤ CQ*ε) (hD : ‖DQ y‖ ≤ CD*ε*β) :
    |quadraticHigherPairRemainder q H N C DQ U a y| ≤
      (Q*(CN*CQ+CH*CD)+Q1*CH*CQ)*ε*β*μ*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  have hβ0 := zero_le_one.trans hβ
  have h1 := abs_applied_half_pair_le (N y) (C y) u (CN*β) (CQ*ε)
    (mul_nonneg hCN hβ0) (mul_nonneg hCQ hε) hN hC
  have h2 := abs_applied_half_pair_le (H y) (DQ y) u CH (CD*ε*β)
    hCH (by positivity) hH hD
  have h3 := abs_applied_half_pair_le (H y) (C y) u CH (CQ*ε)
    hCH (mul_nonneg hCQ hε) hH hC
  have h3β : (Q1*μ)*(CH*(CQ*ε)*‖u‖^2) ≤
      (Q1*μ)*(CH*(CQ*ε)*‖u‖^2)*β := by
    exact le_mul_of_one_le_right (by positivity) hβ
  dsimp only [quadraticHigherPairRemainder]
  change |-q y*(sphereSobolevDualPairing (1/2:ℝ) (N y u) (C y u)+
      sphereSobolevDualPairing (1/2:ℝ) (H y u) (DQ y u))-
    fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) (H y u) (C y u)| ≤ _
  calc
    _ ≤ |-q y*(sphereSobolevDualPairing (1/2:ℝ) (N y u) (C y u)+
          sphereSobolevDualPairing (1/2:ℝ) (H y u) (DQ y u))|+
        |fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) (H y u) (C y u)| := abs_sub _ _
    _ = |q y| *|sphereSobolevDualPairing (1/2:ℝ) (N y u) (C y u)+
          sphereSobolevDualPairing (1/2:ℝ) (H y u) (DQ y u)|+
        |fderiv ℝ q y a| *|sphereSobolevDualPairing (1/2:ℝ) (H y u) (C y u)| := by
      rw [abs_mul,abs_neg,abs_mul]
    _ ≤ (Q*μ)*((CN*β)*(CQ*ε)*‖u‖^2+CH*(CD*ε*β)*‖u‖^2)+
        (Q1*μ)*(CH*(CQ*ε)*‖u‖^2) := add_le_add
      (mul_le_mul hq ((abs_add_le _ _).trans (add_le_add h1 h2))
        (abs_nonneg _) (mul_nonneg hQ hμ))
      (mul_le_mul hdq h3 (abs_nonneg _) (mul_nonneg hQ1 hμ))
    _ ≤ (Q*μ)*((CN*β)*(CQ*ε)*‖u‖^2+CH*(CD*ε*β)*‖u‖^2)+
        (Q1*μ)*(CH*(CQ*ε)*‖u‖^2)*β := add_le_add (le_refl _) h3β
    _ = _ := by dsimp only [u];ring

end ShrinkingSpheres.ParallelEnergy
