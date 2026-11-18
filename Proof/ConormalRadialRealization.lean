import Proof.ConormalRadialAdjunction
import Proof.BoundaryAngularCompatibility
import Proof.RadialEndpointCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Reconstruction from a compatible conormal operator is the genuine
    strong Poisson radial response on every high boundary datum. -/
theorem conormalRadialL_high {a : X → Mat}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (F : SmoothCoefficientMatrix 2) (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hPoint : ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F x = a x)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hPos : ∀ w : UnitSphere,0 < (boundaryNormalCoefficientData F).1 w.val)
    (hN : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp N =
      (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (f : SphereSobolev (3/2:ℝ)) :
    conormalRadialL F N (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
      sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
        (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL F f)) := by
  let u := sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f
  let g := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f
  let U := strongPoissonL F f
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  let R := Z (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace U)
  let Mn := negativeBoundaryCoefficientMulL (normalCoefficientJet F)
  let C := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))
  let T := coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  let S (h : SphereSobolev (1/2:ℝ)) := ∑ j : I,negativeBoundaryCoefficientMulL (tangentCoefficientJet F j) (fixedSphereTangentialL j h)
  have hInput : sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u = g :=
    congrArg (fun I : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => I f)
      (sphereSobolevInclusionL_trans (3/2:ℝ) 1 (1/2:ℝ) (by norm_num) (by norm_num))
  have hNValue : J (N u) = nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner g :=
    (congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u) hN).trans
      (congrArg (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner) hInput)
  have hTValue := congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A u)
    (boundaryTangential_endpoints_compatible (fun j => tangentCoefficientJet F j))
  have hS : S g = J (T u) := (congrArg S hInput).symm.trans hTValue
  have hHarm : ordinaryPrincipalL fixedSobolevCalculus 0 F U = 0 :=
    fullCoefficientOperator_strongPoissonL F hInv f
  have hLift := nativeWeakHalfLift_eq_strongPoisson ha hc F hPoint hInv f
  have hFlux := nativeWeakConormal_eq_ordinary_trace ha F hPoint g U hLift hHarm
  have hConversion := nativeH2_conormal_negativeHalf_eq_coefficient_normal_add_tangent
    fixedSobolevCalculus sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    fixedUnitBallValueTrace F (normalCoefficientJet F) (tangentCoefficientJet F)
    (coefficientSmoothData_normalCoefficientJet F) (coefficientSmoothData_tangentCoefficientJet F) U
  have hValue := fixedHalfValueTrace_strongPoisson F f
  change OAI.AnisotropicCalderon.NativeFullSharpHalfTrace.nativeHalfTraceL
    sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace
      (TauCeti.Wkp.firstOrder 1 U) = g at hValue
  have hChange := congrArg (fun h : SphereSobolev (1/2:ℝ) => Mn (J R)+S h) hValue
  have hEq : J (N u) = J (C R)+J (T u) :=
    hNValue.trans (hFlux.trans (hConversion.trans (hChange.trans
      (congrArg₂ (fun x y : SphereSobolev (-(1/2:ℝ)) => x+y)
        (negativeBoundaryCoefficientMulL_coarse (normalCoefficientJet F) R) hS))))
  have hSub : J (N u-T u) = J (C R) :=
    (J.map_sub _ _).trans (sub_eq_iff_eq_add.mpr hEq)
  have hActual : N u-T u = C R := sphereSobolevInclusionL_injective 0 (-(1/2:ℝ)) (by norm_num) hSub
  have hPosC : ∀ w : UnitSphere,0 < coefficientValue 2 (normalCoefficientJet F) w.val := by
    intro w
    exact (congrArg (fun t : ℝ => 0 < t) (congrFun (coefficientValue_normalCoefficientJet F) w.val)).mpr (hPos w)
  have hC := coarseSphereScalarMulL_isInvertible_of_pos
    (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))) hPosC
  exact (congrArg C.inverse hActual).trans (hC.inverse_apply_self R)

end ShrinkingSpheres
