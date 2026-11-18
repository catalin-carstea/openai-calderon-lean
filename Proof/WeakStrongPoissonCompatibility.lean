import Proof.BoundaryPoissonTrace
import Proof.NativeWeakInverseBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeCoefficientWeakEnergyL
  OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion

/-- The low regularity and strong corrected Poisson constructions are the same
    genuine weak solution on their common boundary domain. -/
theorem nativeWeakHalfLift_eq_strongPoisson {a : X → Mat}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0)
      ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu:=(volume:Measure X))
      (Omega:=ballOpens) (a:=a) (b:=fun _ => (0:X)) (c:=fun _ => (0:ℝ)) hcoeff))
    (F : SmoothCoefficientMatrix 2)
    (hPoint : ∀ x ∈ (ballOpens : Set X),coefficientMatrixField 2 F x = a x)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    nativeWeakHalfLift a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) =
      TauCeti.Wkp.firstOrder 1 (strongPoissonL F f) := by
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U := nativeWeakHalfLift a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner g
  have hOrder : TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f) = fixedHarmonicH1LiftL g :=
    firstOrder_harmonicLiftCompletion sphereFischerInner orthogonalSphereHarmonics f
  have hMem := nativeWeakHalfLift_affine_difference a (fun _ => (0:X)) (fun _ => (0:ℝ))
    hcoeff sphereFischerInner g
  have hZero := (fixedUnitBallValueTrace_kernel (fixedHarmonicH1LiftL g-U)).2 hMem
  rw [map_sub] at hZero
  have hTrace : fixedUnitBallValueTrace.valueTraceL U =
      fixedUnitBallValueTrace.valueTraceL (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) :=
    (sub_eq_zero.mp hZero).symm.trans
      ((congrArg fixedUnitBallValueTrace.valueTraceL hOrder).symm.trans
        (strongPoissonL_valueTrace F f).symm)
  exact weak_harmonic_eq_of_valueTrace_eq hcoeff hc U
    (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f))
    (nativeWeakHalfLift_weak_solution a (fun _ => (0:X)) (fun _ => (0:ℝ)) hcoeff sphereFischerInner
      (isInvertible_of_bilinear_coercive _ hc) g)
    (strongPoissonL_weak F hPoint hInv f) hTrace

/-- The strong correction preserves the full native half-order value trace. -/
theorem fixedHalfValueTrace_strongPoisson (F : SmoothCoefficientMatrix 2)
    (f : SphereSobolev (3/2:ℝ)) :
    fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) =
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f := by
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let w : BallH1Zero := ⟨TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)-
    TauCeti.Wkp.firstOrder 1 (strongPoissonL F f),strongPoissonL_zero_boundary_difference F f⟩
  have hZero := OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL_zeroDirichlet
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace w
  change fixedHalfValueTraceL (TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f)-
    TauCeti.Wkp.firstOrder 1 (strongPoissonL F f)) = 0 at hZero
  rw [map_sub] at hZero
  have hOrder : TauCeti.Wkp.firstOrder 1 (fixedHarmonicLiftL f) = fixedHarmonicH1LiftL g :=
    firstOrder_harmonicLiftCompletion sphereFischerInner orthogonalSphereHarmonics f
  have hRight := congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => T g)
    fixedHalfValueTrace_right_inverse
  exact (sub_eq_zero.mp hZero).symm.trans ((congrArg fixedHalfValueTraceL hOrder).trans hRight)

end ShrinkingSpheres
