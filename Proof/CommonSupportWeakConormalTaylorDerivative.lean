import Proof.WeakConormalTaylorIdentity
import Proof.ConormalEnergyDerivative
import Proof.CommonSupportWeakPoissonRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativePolynomialBulkMoments
attribute [local irreducible] nativeWeakHalfLift weakFirstPoissonVariationL
  nativeWeakConormalEndpoint weakFirstConormalVariationL

/-- The true weak conormal Taylor remainder inherits the quadratic derivative
    estimate from its same actual energy and Poisson families. -/
theorem norm_commonSupportWeakConormal_first_remainder_derivative_le
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (c r : ℝ) (x : P) (CA DA DB V1 D1 CS DS DQ : ℝ)
    (hE : DifferentiableAt ℝ (fun p => commonSupportFullWeakEnergy a ha p) x)
    (hE1 : DifferentiableAt ℝ (fun p => commonSupportFullWeakEnergy a1 ha1 p) x)
    (hP : DifferentiableAt ℝ (fun p => commonSupportWeakHalfLift a ha p) x)
    (hP1 : DifferentiableAt ℝ (fun p => weakFirstPoissonVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) x)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCA : 0 ≤ CA) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hV1 : 0 ≤ V1) (hD1 : 0 ≤ D1) (hCS : 0 ≤ CS) (hDS : 0 ≤ DS) (hDQ : 0 ≤ DQ)
    (hNE : ‖commonSupportFullWeakEnergy a ha x‖ ≤ CA)
    (hDE : ‖fderiv ℝ (fun p => commonSupportFullWeakEnergy a ha p) x‖ ≤ DA*r)
    (hDiffE : ‖commonSupportFullWeakEnergy a ha x-TauCeti.PDE.energyFormH1L (a:=fun _ : X => c • (1:Mat)) (b:=fun _ : X => (0:X)) (c:=fun _ : X => (0:ℝ)) (flatCoefficientBound c)‖ ≤ DB*r)
    (hNP1 : ‖weakFirstPoissonVariationL c (fun z => a1 (x,z)) (commonSupportEnergyMemLp a1 ha1 x)‖ ≤ V1)
    (hDP1 : ‖fderiv ℝ (fun p => weakFirstPoissonVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) x‖ ≤ D1)
    (hNPQ : ‖commonSupportWeakHalfLift a ha x-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c (fun z => a1 (x,z)) (commonSupportEnergyMemLp a1 ha1 x)‖ ≤ CS*r^2)
    (hDPQ : ‖fderiv ℝ (fun p => commonSupportWeakHalfLift a ha p-fixedHarmonicH1LiftL-
      r • weakFirstPoissonVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) x‖ ≤ DS*r^2)
    (hDEQ : ‖fderiv ℝ (fun p => commonSupportFullWeakEnergy a ha p-
      TauCeti.PDE.energyFormH1L (a:=fun _ : X => c • (1:Mat)) (b:=fun _ : X => (0:X)) (c:=fun _ : X => (0:ℝ)) (flatCoefficientBound c)-r • commonSupportFullWeakEnergy a1 ha1 p) x‖ ≤ DQ*r^2) :
    ‖fderiv ℝ (fun p => commonSupportWeakConormalEndpoint a ha p-c • fixedLowRadialL-
      r • weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) x‖ ≤
      sphereSurfaceMass⁻¹*‖fixedHarmonicH1LiftL‖*
        (DA*CS+CA*DS+DA*V1+DB*D1+DQ*‖fixedHarmonicH1LiftL‖)*r^2 := by
  let E := fun p => commonSupportFullWeakEnergy a ha p
  let E1 := fun p => commonSupportFullWeakEnergy a1 ha1 p
  let E0 := TauCeti.PDE.energyFormH1L (a:=fun _ : X => c • (1:Mat)) (b:=fun _ : X => (0:X)) (c:=fun _ : X => (0:ℝ)) (flatCoefficientBound c)
  let Pa := fun p => commonSupportWeakHalfLift a ha p
  let P1 := fun p => weakFirstPoissonVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)
  let R := fun p => (sphereSobolevDualRieszL (1/2:ℝ)).comp (sphereSurfaceMass⁻¹ •
    ((E p).bilinearComp (Pa p) fixedHarmonicH1LiftL-E0.bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL-
      r • (E0.bilinearComp (P1 p) fixedHarmonicH1LiftL+(E1 p).bilinearComp fixedHarmonicH1LiftL fixedHarmonicH1LiftL)))
  have hFamily : (fun p => commonSupportWeakConormalEndpoint a ha p-c • fixedLowRadialL-
      r • weakFirstConormalVariationL c (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) = R := by
    funext p
    exact nativeWeakConormal_first_remainder_eq_energy (a:=fun z => a (p,z)) (a1:=fun z => a1 (p,z))
      (commonSupportEnergyMemLp a ha p) (commonSupportEnergyMemLp a1 ha1 p) c r
  have hNormEq := congrArg (fun f : P → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
    ‖fderiv ℝ f x‖) hFamily
  have hBound := norm_conormal_energy_taylor_derivative_le (T:=P) (H:=BallH1)
    E E1 E0 Pa P1 fixedHarmonicH1LiftL x r CA DA DB V1 D1 CS DS DQ hE hE1 hP hP1
    hr hr1 hCA hDA hDB hV1 hD1 hCS hDS hDQ hNE hDE hDiffE hNP1 hDP1 hNPQ hDPQ hDEQ
  exact hNormEq.le.trans hBound

end ShrinkingSpheres
