import Proof.OrderOneBoundaryCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem norm_coarse_boundary_coefficient_local_C1 (F : SmoothCoefficientJets 2)
    (q : ℝ) (hq : 0 ≤ q) (h : LocalC1Bound (coefficientValue 2 F) q) :
    ‖coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData F))‖ ≤ q :=
  (norm_coarseSphereScalarMulL_le _).trans
    ((ContinuousMap.norm_le _ hq).mpr (fun w => (h.on_unitSphere (contDiff_coefficientValue 2 F) w).1))

end ShrinkingSpheres
