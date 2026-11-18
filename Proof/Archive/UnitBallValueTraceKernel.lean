import Proof.Archive.NativeValueRadialTrace

 
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge SphereHarmonic

 

def UnitBallValueTraceKernel (τ0 : UnitBallValueTrace) : Prop :=
  ∀ u : BallH1, τ0.valueTraceL u = 0 ↔
    u ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2

end OAI.AnisotropicCalderon.DirichletFamily
