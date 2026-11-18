import Proof.DegreeCommutatorEndpointBlocks
import Proof.UniformActualFirstAdjointDegree
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma balanced_endpoint_pair_of_coarse
    (E : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hLo : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp E=
      Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hHi : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      E.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Hi=
      Lo.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) (DFunLike.congr_fun hHi u)
  have hL := DFunLike.congr_fun hLo (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using h.trans hL

/-- The previously selected physical degree blocks determine the exact
    balanced graph of the SAME compatible endpoint pair. -/
lemma balanced_degree_commutator
    (E : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (Lo C : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hLo : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp E=
      Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hHi : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
      E.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hC : ∀ m n : ℕ,∀ z : harmonicSphereSubspace n,
      sphereSobolevCoefficientL (-(1/2:ℝ)) m (C (sphereSobolevSingleL (1/2:ℝ) n z))=
        ((m:ℝ)-(n:ℝ)) • coarsePhysicalHarmonicBlock E m n z) :
    degreeEndpointCommutator Hi Lo=C.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hPair := balanced_endpoint_pair_of_coarse E Lo Hi hLo hHi
  apply sphereSobolev_clm_eq_of_single (3/2:ℝ)
  intro n z
  apply sphereSobolev_ext (-(1/2:ℝ))
  intro m
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_single]
  exact (degreeEndpointCommutator_physical_block Hi Lo E hHi hPair m n z).trans (hC m n z).symm
end ShrinkingSpheres
