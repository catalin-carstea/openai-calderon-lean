import Proof.CoarseDegreePairBound
import Proof.DenseBilinearCompletion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped InnerProductSpace ENNReal Topology
namespace OAI.AnisotropicCalderon.SphereHarmonic

/-- A finite half-order bound for a coarse dual form extends to every
    coarse input and test vector. -/
lemma coarse_dual_pair_bound_of_finite
    (T : SphereSobolev 2 →L[ℝ] SphereSobolev (-1:ℝ))
    (M : ℝ)
    (hFinite : ∀ u ∈ sphereSobolevFiniteSupport 2,
      ∀ v ∈ sphereSobolevFiniteSupport 1,
      |sphereSobolevDualPairing 1 v (T u)| ≤
        M*‖sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u‖*
          ‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v‖) :
    ∀ u v, |sphereSobolevDualPairing 1 v (T u)| ≤
      M*‖sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u‖*
        ‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v‖ := by
  let I := sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let L : SphereSobolev 2 →L[ℝ] StrongDual ℝ (SphereSobolev 1) :=
    (innerSLFlip ℝ).comp T
  have hV (u : SphereSobolev 2) (hu : u ∈ sphereSobolevFiniteSupport 2)
      (v : SphereSobolev 1) : |L u v| ≤ M*‖I u‖*‖J v‖ := by
    have hClosed : IsClosed {v : SphereSobolev 1 | |L u v| ≤ M*‖I u‖*‖J v‖} :=
      isClosed_le (L u).continuous.abs (continuous_const.mul J.continuous.norm)
    have hc := closure_minimal (s := sphereSobolevFiniteSupport 1) (hFinite u hu) hClosed
    rw [closure_sphereSobolevFiniteSupport] at hc
    exact hc (mem_univ v)
  intro u v
  have hLeft : Continuous (fun u : SphereSobolev 2 => |L u v|) := by fun_prop
  have hClosed : IsClosed {u : SphereSobolev 2 | |L u v| ≤ M*‖I u‖*‖J v‖} :=
    isClosed_le hLeft ((continuous_const.mul I.continuous.norm).mul continuous_const)
  have hc := closure_minimal (s := sphereSobolevFiniteSupport 2) (fun u hu => hV u hu v) hClosed
  rw [closure_sphereSobolevFiniteSupport] at hc
  exact hc (mem_univ u)

/-- Complete a coarse H2-by-H1 dual form in both half-order norms.
    No high/low endpoint response witnesses are needed. -/
theorem exists_half_operator_of_finite_coarse_dual_pairs
    (T : SphereSobolev 2 →L[ℝ] SphereSobolev (-1:ℝ))
    (M : ℝ) (hM : 0 ≤ M)
    (hFinite : ∀ u ∈ sphereSobolevFiniteSupport 2,
      ∀ v ∈ sphereSobolevFiniteSupport 1,
      |sphereSobolevDualPairing 1 v (T u)| ≤
        M*‖sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u‖*
          ‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v‖) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ M ∧
      (∀ u v,sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v)
        (S (sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num) u)) =
          sphereSobolevDualPairing 1 v (T u)) ∧
      (∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
          sphereSobolevCoefficientL (-1:ℝ) m (T (sphereSobolevSingleL 2 n z))) := by
  let I := sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let L : SphereSobolev 2 →L[ℝ] StrongDual ℝ (SphereSobolev 1) :=
    (innerSLFlip ℝ).comp T
  obtain ⟨Q,hQ,hGraph⟩ := DenseBilinearCompletion.exists_extension L I J
    (denseRange_sphereSobolevInclusionL 2 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) M hM
    (coarse_dual_pair_bound_of_finite T M hFinite)
  let S := (sphereSobolevDualRieszL (1/2:ℝ)).comp Q
  have hS (u : SphereSobolev (1/2:ℝ)) : ‖S u‖ ≤ M*‖u‖ := by
    change ‖sphereSobolevDualRieszL (1/2:ℝ) (Q u)‖ ≤ _
    rw [norm_sphereSobolevDualRieszL_apply]
    exact (Q.le_opNorm u).trans (mul_le_mul_of_nonneg_right hQ (norm_nonneg u))
  have hPair (u : SphereSobolev 2) (v : SphereSobolev 1) :
      sphereSobolevDualPairing (1/2:ℝ) (J v) (S (I u)) =
        sphereSobolevDualPairing 1 v (T u) := by
    exact (sphereSobolevDualPairing_dualRiesz (1/2:ℝ) (Q (I u)) (J v)).trans (hGraph u v)
  refine ⟨S,S.opNorm_le_bound hM hS,hPair,?_⟩
  intro m n z
  apply ext_inner_right ℝ
  intro w
  have h := hPair (sphereSobolevSingleL 2 n z) (sphereSobolevSingleL 1 m w)
  simp only [I,J,sphereSobolevInclusionL_single,
    sphereSobolevDualPairing_single_left_physical] at h
  exact h

end OAI.AnisotropicCalderon.SphereHarmonic
