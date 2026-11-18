import Proof.Archive.SphereSobolevBalancedDualEndpointKernel
import Proof.Archive.SmoothKernelCodomainStructureTransport
import Proof.Archive.SphereSobolevBalancedDualEndpointExtension
import Proof.Archive.SphereSobolevCompatibleInterpolationTopology
import Proof.Archive.ProdInheritedStructureData

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevBalancedDualCompatible_mem_iff (T : SphereSobolevBalancedDualEndpointPair) :
    T ∈ sphereSobolevBalancedDualCompatibleEndpoints ↔
      (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)).comp T.2 =
        T.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) := by
  change
    (sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)).comp T.2 -
      T.1.comp (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)) = 0 ↔ _
  exact sub_eq_zero

end OAI.AnisotropicCalderon.SphereHarmonic
