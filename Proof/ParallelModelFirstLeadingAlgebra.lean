import Proof.ParallelFirstSelfLeadingAlgebra
import Proof.ParallelScalarFirstRemainderPoint
import Proof.PhysicalScalarSelfIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The two DISTINCT first-base orientations are paired before norms.
The output is an order-dropped angular commutator plus a genuine mixed
Hodge exchange; no product of uncontrolled horizontal norms remains hidden. -/
lemma model_first_leading_row_split
    (R B : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (RH BH RA BA : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hR : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp RH=
      R.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hBA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp BA=
      B.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hC : R.adjoint.comp BH-B.comp RA=
      C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (u v : SphereSobolev (3/2:ℝ)) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (RH u),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (BH v)⟫_ℝ-
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (RA u),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (BA v)⟫_ℝ=
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (C (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v))+
      (⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (RA v),
          sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (BA u)⟫_ℝ-
        ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (RA u),
          sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (BA v)⟫_ℝ) := by
  have h := first_leading_row_commutator_identity R B RH BH RA BA C hR hBA hC u v
  linarith only [h]

/-- The sharp angular commutator scale epsilon/beta pairs against ONLY
the actual half horizontal derivatives in the original weighted energy. -/
lemma model_first_leading_commutator_point_bound
    (C : I → I → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (V : I → SphereSobolev (1/2:ℝ)) (g : I → I → ℝ)
    (K Q ε β μ En : ℝ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hε : 0 ≤ ε) (hβ : 0 < β) (hμ : 0 ≤ μ)
    (hC : ∀ c b,‖C c b‖ ≤ Q*ε/β) (hg : ∀ k c,|g k c| ≤ K)
    (hV : ∀ k,β⁻¹*‖V k‖^2 ≤ En) :
    |μ*(∑ k : I,∑ b : I,∑ c : I,g k c*sphereSobolevDualPairing (1/2:ℝ) (V k) (C c b (V b)))| ≤
      54*K*Q*ε*μ*En := by
  have hPair (k b c : I) : |sphereSobolevDualPairing (1/2:ℝ) (V k) (C c b (V b))| ≤ 2*Q*ε*En := by
    have hp := norm_product_inv_le_energy ‖V k‖ ‖V b‖ β En (norm_nonneg _) (norm_nonneg _) hβ (hV k) (hV b)
    calc
      _ ≤ ‖V k‖*‖C c b (V b)‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ ‖V k‖*((Q*ε/β)*‖V b‖) := mul_le_mul_of_nonneg_left
        (((C c b).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC c b) (norm_nonneg _))) (norm_nonneg _)
      _ = (Q*ε)*(β⁻¹*‖V k‖*‖V b‖) := by ring
      _ ≤ (Q*ε)*(2*En) := mul_le_mul_of_nonneg_left hp (mul_nonneg hQ hε)
      _ = _ := by ring
  have hTerm (k b c : I) : |g k c*sphereSobolevDualPairing (1/2:ℝ) (V k) (C c b (V b))| ≤ K*(2*Q*ε*En) := by
    rw [abs_mul]
    exact mul_le_mul (hg k c) (hPair k b c) (abs_nonneg _) hK
  have hSum : |∑ k : I,∑ b : I,∑ c : I,g k c*sphereSobolevDualPairing (1/2:ℝ) (V k) (C c b (V b))| ≤
      3*(3*(3*(K*(2*Q*ε*En)))) :=
    abs_fin_three_sum_le _ _ (fun k => abs_fin_three_sum_le _ _ (fun b => abs_fin_three_sum_le _ _ (hTerm k b)))
  rw [abs_mul,abs_of_nonneg hμ]
  exact (mul_le_mul_of_nonneg_left hSum hμ).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
