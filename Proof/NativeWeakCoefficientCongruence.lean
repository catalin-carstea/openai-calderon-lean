import Proof.WeakPoissonTaylorDerivative
import Proof.ZeroEnergyAffineIdentity
import Proof.WeakConormalTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeWeakHalfLift nativeCoefficientWeakFunctionalInverse
  nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL

/-- All three actual weak energy forms depend only on coefficients on the
    physical ball, with arbitrary genuine integrability witnesses. -/
theorem nativeWeakEnergy_congr_unitBall {a b : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (b z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hPoint : ∀ z ∈ (ballOpens:Set X),a z = b z) :
    TauCeti.PDE.energyFormH1L ha = TauCeti.PDE.energyFormH1L hb ∧
    nativeCoefficientWeakEnergyL a 0 0 ha = nativeCoefficientWeakEnergyL b 0 0 hb ∧
    nativeZeroCoefficientEnergyL a 0 0 ha = nativeZeroCoefficientEnergyL b 0 0 hb := by
  have hAffine : ∀ z ∈ (ballOpens:Set X),a z = b z+(0:ℝ) • b z := by
    intro z hz
    simpa only [zero_smul,add_zero] using hPoint z hz
  have hF := fullWeakEnergy_affine_eq ha hb hb 0 hAffine
  have hW := nativeWeakEnergy_affine_eq ha hb hb 0 hAffine
  have hZ := nativeZeroEnergy_affine_eq ha hb hb 0 hAffine
  simpa only [zero_smul,add_zero] using And.intro hF (And.intro hW hZ)

/-- The actual native weak Poisson solution is independent of every exterior
    cutoff, because both its native inverse and weak energy are unchanged. -/
theorem nativeWeakHalfLift_congr_unitBall {a b : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (b z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hPoint : ∀ z ∈ (ballOpens:Set X),a z = b z) :
    nativeWeakHalfLift a 0 0 ha sphereFischerInner = nativeWeakHalfLift b 0 0 hb sphereFischerInner := by
  have hEnergy := nativeWeakEnergy_congr_unitBall ha hb hPoint
  have hInverse : nativeCoefficientWeakFunctionalInverse a 0 0 ha = nativeCoefficientWeakFunctionalInverse b 0 0 hb :=
    (nativeZeroCoefficientEnergy_inverse_eq ha).symm.trans
      ((congrArg (fun A : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => A.inverse) hEnergy.2.2).trans
        (nativeZeroCoefficientEnergy_inverse_eq hb))
  rw [nativeWeakHalfLift_native_assembly ha,nativeWeakHalfLift_native_assembly hb,hInverse,hEnergy.2.1]

/-- The actual conormal operator depends only on the physical coefficient,
    allowing checked point Taylor norms to use the same angular witnesses. -/
theorem nativeWeakConormal_congr_unitBall {a b : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (b z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hPoint : ∀ z ∈ (ballOpens:Set X),a z = b z) :
    nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner = nativeWeakConormalEndpoint b 0 0 hb sphereFischerInner := by
  have hE := (nativeWeakEnergy_congr_unitBall ha hb hPoint).1
  have hP := nativeWeakHalfLift_congr_unitBall ha hb hPoint
  rw [nativeWeakConormal_eq_full_energy ha,nativeWeakConormal_eq_full_energy hb,hE,hP]

end ShrinkingSpheres
