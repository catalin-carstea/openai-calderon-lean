import Proof.FirstRadialCompatibility
import Proof.RadialEndpointCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
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

/-- The actual low/high radial Taylor remainders are compatible after the
    same scalar first coefficient is subtracted. This is the common canonical
    derivation used by point norm and angular derivative interpolation. -/
theorem radial_taylor_endpoints_compatible {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hCoercive : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (F0 F F1 : SmoothCoefficientMatrix 2) (c r : ℝ) (s : X → ℝ) (hc : 0 < c)
    (hFirstMem : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hPoint : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z)
    (hF0 : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hScalar : ∀ w : UnitSphere,coefficientMatrixField 2 F1 w.val = s w.val • (1:Mat))
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 c) =
      (actualLowRadialErrorL a ha F-r • lowFirstRadialVariationL c F1 hFirstMem).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hActual := actual_radial_endpoints_compatible ha hCoercive F hPoint hInv hNormal
  have hFirst : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (highFirstRadialVariationL F0 F1 c) =
      (lowFirstRadialVariationL c F1 hFirstMem).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    apply ContinuousLinearMap.ext
    intro f
    exact (lowFirstRadialVariation_high_compatible F0 F1 c hc hF0 s hScalar hFirstMem hInv0 f).symm
  have hDiff := congrArg₂ (fun A B : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A-r • B) hActual hFirst
  simpa only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp] using hDiff

end ShrinkingSpheres
