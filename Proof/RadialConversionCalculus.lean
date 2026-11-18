import Proof.EndpointBoundaryCalculus
import Proof.BoundaryCoefficientMultiplierAlgebra
import Proof.Archive.NativeH2ConormalCoefficientRadialConversion
import Proof.Archive.NativeBoundaryNormalMultiplierInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeBoundaryNormalMultiplierInverse

/-- Actual ellipticity supplies qualitative invertibility of the negative-half
    normal coefficient operator. The quantitative bound is proved separately
    from its small perturbation of the conformal scalar center. -/
theorem negativeNormalCoefficient_isInvertible (F : SmoothCoefficientMatrix 2)
    (A : SmoothCoefficientJets 2) (hA : coefficientSmoothData A = boundaryNormalCoefficientData F)
    (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 F) lam Lam) :
    (negativeBoundaryCoefficientMulL A).IsInvertible := by
  obtain ⟨M,hM,hm,hgm,hInv⟩ := exists_nativeBoundaryNormalMultiplier_inverse
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace F lam Lam hUE
  have hEq := referenceNegativeHalfCoefficientMultiplier_eq_of_data_eq fixedSobolevCalculus sphereFischerInner
    orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace A (boundaryNormalCoefficientData F)
      hA hM hm hgm
  have hProp := congrArg (fun T : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => T.IsInvertible) hEq
  exact hProp.mpr hInv

end ShrinkingSpheres
