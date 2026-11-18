import Proof.RadialMultiplierRemainderGraph
import Proof.FirstMultiplierCanonicalGraph
import Proof.SmoothMultiplierDomainCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeThreeHalfCoefficientMultiplier
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier

/-- The gained half-order commutator restricts to the SAME actual midpoint
radial Taylor remainder, with its canonical bounded correction, on ALL H1
data. Density is used only after the actual high graph has been proved. -/
theorem midpoint_radial_taylor_multiplier_gain_graph (F F0 F1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (ell : X →L[ℝ] ℝ)
    (hF1 : ∀ z ∈ (ballOpens:Set X),∀ i j,coefficientValue 2 (F1 i j) z = ell z*(1:Mat) i j)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hHigh : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) =
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (Q : SmoothCoefficientJets 3) (r : ℝ) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) =
    (R-r • ((radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num)))).comp
      (oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q))-
    (coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))).comp
      (R-r • ((radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num)))) := by
  let G := radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r
  let R1 := R-r • ((radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num)))
  let M0 := coarseSphereScalarMulL (smoothSphereValue (nativeH2CoefficientSmoothData Q))
  let M1 := oneBoundaryCoefficientMulL (smoothMultiplierLowerJets Q)
  let M3 := nativeThreeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace Q
  let Mh := nativeHalfCoefficientMulL fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace (smoothMultiplierLowerJets Q)
  let I1 := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
  let Ih := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J1h := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let Jh0 := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let I0 := sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
  let T := actualHighRadialErrorL F-r • highFirstRadialVariationL F0 F1 1
  have hI (f : SphereSobolev (3/2:ℝ)) : J1h (I1 f) = Ih f :=
    congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
  have hI0 (f : SphereSobolev (3/2:ℝ)) : sphereSobolevInclusionL 1 0 (by norm_num) (I1 f) = I0 f :=
    congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => A f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 0 (by norm_num) (by norm_num))
  have hB : coarseFirstRadialVariationL 1 ell = radialCorrectionCovectorL ell := by
    simpa only [inv_one,one_smul] using coarseFirstRadialVariationL_normalized_covector 1 ell
  have hFirst (f : SphereSobolev (3/2:ℝ)) : Jh0 (highFirstRadialVariationL F0 F1 1 f) = radialCorrectionCovectorL ell (I0 f) := by
    have h := congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => A f)
      (highFirstRadialVariation_coarse_eq F0 F1 1 (by norm_num) ell hFlat hF1
        (by simpa only [one_smul] using hInv0))
    simpa only [ContinuousLinearMap.comp_apply,hB] using h
  have hT (f : SphereSobolev (3/2:ℝ)) : Jh0 (T f) = R1 (I1 f) := by
    have hR := congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => A f) hHigh
    change Jh0 (actualHighRadialErrorL F f) = R (I1 f) at hR
    change Jh0 (actualHighRadialErrorL F f-r • highFirstRadialVariationL F0 F1 1 f) =
      R (I1 f)-r • radialCorrectionCovectorL ell (sphereSobolevInclusionL 1 0 (by norm_num) (I1 f))
    rw [map_sub,map_smul,hR,hFirst,hI0]
  let L := Jh0.comp (G.comp J1h)
  let V := R1.comp M1-M0.comp R1
  have hDense := denseRange_sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)
  have hEq : (fun u : SphereSobolev 1 => L u) = (fun u : SphereSobolev 1 => V u) :=
    hDense.equalizer L.continuous V.continuous (by
      funext f
      have hGraph := radialTaylorMultiplierCommutator_high F F0 F1 ha ha0 ha1 hc hFlat hInv hInv0 Q r f
      change G (Ih f) = T (M3 f)-Mh (T f) at hGraph
      have hM1 : M1 (I1 f) = I1 (M3 f) := oneBoundaryCoefficientMulL_third_high Q f
      have hMh : Jh0 (Mh (T f)) = M0 (Jh0 (T f)) := halfBoundaryCoefficientMul_coarse Q (T f)
      change Jh0 (G (J1h (I1 f))) = R1 (M1 (I1 f))-M0 (R1 (I1 f))
      rw [hI,hGraph,map_sub,hMh,hT (M3 f),hT f,hM1])
  exact ContinuousLinearMap.ext (congrFun hEq)

end ShrinkingSpheres
