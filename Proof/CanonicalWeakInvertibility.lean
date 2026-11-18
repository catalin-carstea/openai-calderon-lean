import Proof.NativeWeakEnergyData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- A coefficient-level bridge fixes the canonical inherited weak structures
    before an inverse is used in the affine perturbation calculus. -/
theorem canonicalWeakEnergy_isInvertible {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha)) :
    (TauCeti.PDE.energyFormH1L0 ha).IsInvertible := by
  exact isInvertible_of_bilinear_coercive _ hc

end ShrinkingSpheres
