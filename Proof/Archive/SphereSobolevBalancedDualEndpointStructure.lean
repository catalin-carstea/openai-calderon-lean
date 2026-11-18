import Proof.Archive.SphereSobolevBalancedDualEndpointNormedSpace

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevBalancedDualCompatibleNormedSpace_module_eq :
    sphereSobolevBalancedDualCompatibleNormedSpace.toModule =
      sphereSobolevBalancedDualCompatibleEndpoints.module := rfl

end OAI.AnisotropicCalderon.SphereHarmonic
