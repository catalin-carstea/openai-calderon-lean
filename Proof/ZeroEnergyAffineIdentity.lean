import Proof.WeakEnergyAffineIdentity
import Proof.NativeWeakTaylorOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL

lemma nativeZeroEnergy_restriction_eq {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens)) :
    nativeZeroCoefficientEnergyL a 0 0 ha = (nativeCoefficientWeakEnergyL a 0 0 ha).comp
      (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (nativeZeroCoefficientEnergyL_apply _ _ _ _ u v).trans
    (nativeCoefficientWeakEnergyL_restriction _ _ _ _ u v)

/-- The actual zero-boundary energy inherits every exact local affine
    coefficient identity, with the same coefficient integrability witnesses. -/
theorem nativeZeroEnergy_affine_eq {a a0 a1 : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (a1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (r : ℝ) (hCoeff : ∀ z ∈ (ballOpens:Set X),a z = a0 z+r • a1 z) :
    nativeZeroCoefficientEnergyL a 0 0 ha =
      nativeZeroCoefficientEnergyL a0 0 0 ha0+r • nativeZeroCoefficientEnergyL a1 0 0 ha1 := by
  let J : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  have h := congrArg (fun T : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero => T.comp J)
    (nativeWeakEnergy_affine_eq ha ha0 ha1 r hCoeff)
  have hDistribute : (nativeCoefficientWeakEnergyL a0 0 0 ha0+r • nativeCoefficientWeakEnergyL a1 0 0 ha1).comp J =
      (nativeCoefficientWeakEnergyL a0 0 0 ha0).comp J+r • (nativeCoefficientWeakEnergyL a1 0 0 ha1).comp J := by
    simp only [ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp]
  have hBack := congrArg₂ (fun A B : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A+r • B)
    (nativeZeroEnergy_restriction_eq ha0).symm (nativeZeroEnergy_restriction_eq ha1).symm
  exact (nativeZeroEnergy_restriction_eq ha).trans (h.trans (hDistribute.trans hBack))

end ShrinkingSpheres
