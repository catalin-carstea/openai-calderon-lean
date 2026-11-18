import Proof.DegreeCommutatorEndpointBlocks

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A genuine compatible endpoint operator and its distributional angular
    graphs suffice for the gained half-order degree commutator. The adjunction
    here is the actual probability-sphere pairing, not a weighted Hilbert adjoint. -/
theorem exists_half_degree_commutator_of_distribution_graphs
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hMid : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hLow : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hi =
      Lo.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (P Q : I × I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (MP MQ : ℝ) (hMP : 0 ≤ MP) (hMQ : 0 ≤ MQ)
    (hP : ∀ ij,‖P ij‖ ≤ MP) (hQ : ∀ ij,‖Q ij‖ ≤ MQ)
    (hPair : ∀ ij,∀ u v : SphereSobolev 1,
      ⟪P ij u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Q ij v⟫_ℝ)
    (hGraph : ∀ ij : I × I,∀ f : SphereSobolev 2,
      sphereSobolevRotationL 0 ij.1 ij.2 (R (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (P ij (sphereSobolevInclusionL 2 1 (by norm_num) f)+R (sphereSobolevRotationL 2 ij.1 ij.2 f))) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ‖S‖ ≤ (6*Real.sqrt 2)*(MP+MQ) ∧
      (∀ u,S (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) =
        degreeEndpointCommutator Hi Lo u) ∧
      ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) m (S (sphereSobolevSingleL (1/2:ℝ) n z)) =
          ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock R m n z := by
  apply exists_half_degree_commutator_of_rotation_blocks (degreeEndpointCommutator Hi Lo)
    (coarsePhysicalHarmonicBlock R)
    (degreeEndpointCommutator_physical_block Hi Lo R hMid hLow) P Q MP MQ hMP hMQ hP hQ
  · intro ij u v
    rw [(sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.inner_map_map,
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm.inner_map_map]
    exact hPair ij u v
  · intro ij m n z
    exact coarsePhysicalHarmonicBlock_of_rotation_distribution ij.1 ij.2 R (P ij) (hGraph ij) m n z

end ShrinkingSpheres
