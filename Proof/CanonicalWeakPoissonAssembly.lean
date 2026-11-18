import Proof.WeakEnergyAffineTaylor
import Proof.WeakPoissonComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeCoefficientWeakFunctionalInverse

/-- The actual native weak lift uses the same canonical inverse as the
    quantitative affine perturbation calculus. -/
theorem nativeWeakHalfLift_canonical_assembly {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    nativeWeakHalfLift a 0 0 ha sphereFischerInner = fixedHarmonicH1LiftL-
      (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL.comp
        ((TauCeti.PDE.energyFormH1L0 ha).inverse.comp
          ((nativeCoefficientWeakEnergyL a 0 0 ha).comp fixedHarmonicH1LiftL)) := by
  let j := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let T := nativeCoefficientWeakEnergyL a 0 0 ha
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun S : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => S f)
    (nativeWeakHalfLift_eq_affineAssembly a 0 0 ha sphereFischerInner)
  have h' := h.trans (nativeWeakAffineLiftAssembly_apply j (nativeCoefficientWeakFunctionalInverse a 0 0 ha) T fixedHarmonicH1LiftL f)
  rw [nativeCoefficientWeakFunctionalInverse_eq_inverse (a:=a) ha] at h'
  exact h'

end ShrinkingSpheres
