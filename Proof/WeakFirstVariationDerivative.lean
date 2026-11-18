import Proof.FirstPoissonEnergyDerivative
import Proof.WeakPoissonTaylorDerivative
import Proof.CommonSupportWeakEnergyRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakFunctionalInverse nativeCoefficientWeakEnergyL

/-- The actual first weak Poisson variation is a fixed linear image of the
    actual first weak energy family, retaining its chosen coefficient witness. -/
theorem commonSupport_weakFirstPoisson_family_eq
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (c : ℝ) :
    (fun p => weakFirstPoissonVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) =
      fun p => -((TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL.comp
        ((nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)).comp
          ((commonSupportWeakEnergy a1 ha1 p).comp fixedHarmonicH1LiftL))) := by
  funext p
  rfl

/-- Actual first Poisson variation derivatives use only the fixed flat inverse
    and the genuine first weak energy derivative bound. -/
theorem commonSupport_weakFirstPoisson_derivative
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a1 : P × X → Mat) (ha1 : ContDiff ℝ ∞ a1) (c : ℝ) (x : P)
    (hT1 : DifferentiableAt ℝ (commonSupportWeakEnergy a1 ha1) x)
    (C0 D1 : ℝ) (hC0 : 0 ≤ C0) (hD1 : 0 ≤ D1)
    (hI0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)‖ ≤ C0)
    (hDT1 : ‖fderiv ℝ (commonSupportWeakEnergy a1 ha1) x‖ ≤ D1) :
    DifferentiableAt ℝ (fun p => weakFirstPoissonVariationL c (fun z => a1 (p,z))
      (commonSupportEnergyMemLp a1 ha1 p)) x ∧
    ‖fderiv ℝ (fun p => weakFirstPoissonVariationL c (fun z => a1 (p,z))
      (commonSupportEnergyMemLp a1 ha1 p)) x‖ ≤ C0*D1*‖fixedHarmonicH1LiftL‖ := by
  let J : BallH1Zero →L[ℝ] BallH1 := (TauCeti.w1p0Submodule (volume:Measure X) ballOpens 2).toSubmodule.subtypeL
  let I0 := nativeCoefficientWeakFunctionalInverse (fun _ : X => c • (1:Mat)) 0 0 (flatCoefficientBound c)
  have hBound := fixed_first_poisson_energy_derivative (P:=P) (Z:=BallH1Zero) (E:=BallH1)
    (F:=StrongDual ℝ BallH1Zero) (H:=SphereSobolev (1/2:ℝ))
    J I0 fixedHarmonicH1LiftL (commonSupportWeakEnergy a1 ha1) x hT1 C0 D1 hC0 hD1
    norm_nativeWeakZeroInclusion_le_one hI0 hDT1
  have hFamily := commonSupport_weakFirstPoisson_family_eq a1 ha1 c
  constructor
  · exact hFamily.symm ▸ hBound.1
  · exact (congrArg (fun f : P → SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 => ‖fderiv ℝ f x‖) hFamily).le.trans hBound.2

end ShrinkingSpheres
