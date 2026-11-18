import Proof.UniformActualRadialTaylorDegreeCommutator
import Proof.RadialConormalReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma coarsePhysicalHarmonicBlock_true_adjoint
    (R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ)
    (m n : ℕ) (u : harmonicSphereSubspace n) (v : harmonicSphereSubspace m) :
    ⟪coarsePhysicalHarmonicBlock R m n u,v⟫_ℝ =
      ⟪u,coarsePhysicalHarmonicBlock Ra n m v⟫_ℝ := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have h := hPair (sphereSobolevSingleL 1 n u) (sphereSobolevSingleL 1 m v)
  rw [sphereSobolevInclusionL_single,sphereSobolevInclusionL_single] at h
  rw [← Z.symm.inner_map_map,← Z.symm.inner_map_map] at h
  have hU : Z.symm (sphereSobolevSingleL 0 n u) = (u : SphereL2) := by
    rw [← zeroEquiv_harmonic_subtype,Z.symm_apply_apply]
  have hV : Z.symm (sphereSobolevSingleL 0 m v) = (v : SphereL2) := by
    rw [← zeroEquiv_harmonic_subtype,Z.symm_apply_apply]
  rw [hU,hV] at h
  calc
    _ = ⟪Z.symm (R (sphereSobolevSingleL 1 n u)),(v:SphereL2)⟫_ℝ :=
      coarsePhysicalHarmonicBlock_inner R m n u v
    _ = ⟪(u:SphereL2),Z.symm (Ra (sphereSobolevSingleL 1 m v))⟫_ℝ := h
    _ = ⟪Z.symm (Ra (sphereSobolevSingleL 1 m v)),(u:SphereL2)⟫_ℝ := real_inner_comm _ _
    _ = ⟪coarsePhysicalHarmonicBlock Ra n m v,u⟫_ℝ :=
      (coarsePhysicalHarmonicBlock_inner Ra n m v u).symm
    _ = _ := real_inner_comm _ _

/-- Negating the dual transpose reverses the sign of the degree difference.
    Therefore the true adjoint radial error has the SAME gained degree bound. -/
theorem half_degree_commutator_adjoint_block
    (R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPair : ∀ u v : SphereSobolev 1,
      ⟪R u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ)
    (S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hS : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock R m n z)
    (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (-(1/2:ℝ)) m
      ((-S.adjoint) (sphereSobolevSingleL (1/2:ℝ) n z)) =
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock Ra m n z := by
  apply ext_inner_right ℝ
  intro v
  rw [← sphereSobolevDualPairing_single_left_physical]
  change ⟪sphereSobolevSingleL (1/2:ℝ) m v,
    -(S.adjoint (sphereSobolevSingleL (1/2:ℝ) n z))⟫_ℝ = _
  rw [inner_neg_right,S.adjoint_inner_right,real_inner_comm]
  change -sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevSingleL (1/2:ℝ) n z)
    (S (sphereSobolevSingleL (1/2:ℝ) m v)) = _
  rw [sphereSobolevDualPairing_single_left_physical,hS,
    real_inner_smul_left,real_inner_smul_left,
    coarsePhysicalHarmonicBlock_true_adjoint R Ra hPair,real_inner_comm v]
  ring

end ShrinkingSpheres
