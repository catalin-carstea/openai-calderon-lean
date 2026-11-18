import Proof.CommonSupportRadialAdjointRegularity
import Proof.CoarseConormalSymmetry
import Proof.CommonSupportMidpointRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The native high restriction determines the same low restriction for any
    bounded midpoint radial representative. -/
theorem midpoint_radial_low_of_high {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (F : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R =
      (actualLowRadialErrorL a ha F).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hC := actual_radial_endpoints_compatible ha hc F hField hStrong hNormal
  have hI := sphereSobolevInclusionL_eq_of_target_eq (1/2:ℝ) (-1/2:ℝ) (-(1/2:ℝ))
    (by norm_num) (by norm_num) (by ring)
  have hCompat : (actualLowRadialErrorL a ha F,actualHighRadialErrorL F) ∈ sphereSobolevCompatibleEndpoints :=
    (congrArg (fun J : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      J.comp (actualHighRadialErrorL F)) hI).trans hC
  let T := sphereSobolevMidpointL (actualLowRadialErrorL a ha F) (actualHighRadialErrorL F) hCompat
  have hRT : R = T := by
    apply continuousLinearMap_eq_of_high_restriction
    intro f
    exact (congrArg (fun L : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => L f) hR).trans
      (congrArg (fun L : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev 0 => L f)
        (sphereSobolevMidpointL_inclusion (actualLowRadialErrorL a ha F) (actualHighRadialErrorL F) hCompat)).symm
  rw [hRT]
  have hJ := sphereSobolevInclusionL_eq_of_target_eq 0 (-1/2:ℝ) (-(1/2:ℝ))
    (by norm_num) (by norm_num) (by ring)
  exact (congrArg (fun J : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => J.comp T) hJ).symm.trans
    (sphereSobolevInclusionL_midpoint (actualLowRadialErrorL a ha F) (actualHighRadialErrorL F) hCompat)

/-- Reconstructing the conormal from the genuine midpoint response recovers
    the native weak conormal, including its exact physical symmetry. -/
theorem midpoint_radial_reconstructed_conormal_weak {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (F : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)) :
    let D := R+sphereSobolevDegreeL
    let N := (coarseSphereScalarMulL (smoothSphereValue
      (coefficientSmoothData (normalCoefficientJet F)))).comp D+
        coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp N =
      (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let J := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let Ih := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let M := negativeBoundaryCoefficientMulL (normalCoefficientJet F)
  let Nw := nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner
  let T := coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  let Ts := ∑ j : I,(negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)).comp (fixedSphereTangentialL j)
  have hLow := midpoint_radial_low_of_high ha hc F hField hStrong hNormal R hR
  apply ContinuousLinearMap.ext
  intro u
  have hRVal := congrArg (fun L : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => L u) hLow
  have hDVal := congrArg (fun L : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => L u)
    fixedLowRadialL_degree_compatible
  have hTVal := congrArg (fun L : SphereSobolev 1 →L[ℝ] SphereSobolev (-(1/2:ℝ)) => L u)
    (boundaryTangential_endpoints_compatible (fun j => tangentCoefficientJet F j))
  change J (R u) = actualLowRadialErrorL a ha F (Ih u) at hRVal
  change fixedLowRadialL (Ih u) = J (sphereSobolevDegreeL u) at hDVal
  change Ts (Ih u) = J (T u) at hTVal
  change J ((coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))))
    ((R+sphereSobolevDegreeL) u)+T u) = Nw (Ih u)
  rw [map_add,← negativeBoundaryCoefficientMulL_coarse,_root_.add_apply,
    J.map_add,hRVal,← hDVal,← hTVal,M.map_add]
  change M (M.inverse (Nw (Ih u)-M (fixedLowRadialL (Ih u))-Ts (Ih u)))+
    M (fixedLowRadialL (Ih u))+Ts (Ih u) = Nw (Ih u)
  rw [hNormal.self_apply_inverse]
  abel

/-- The smooth response-adjoint formula is the true physical L2 adjoint of
    every genuine midpoint radial response for symmetric native coefficients. -/
theorem midpoint_radialAdjointFromResponse_pairing {a : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hc : IsCoercive (TauCeti.PDE.energyFormH1L0 ha))
    (hs : ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),(a z).IsSymm)
    (F : SmoothCoefficientMatrix 2)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (hPos : ∀ w : UnitSphere,0 < coefficientValue 2 (normalCoefficientJet F) w.val)
    (R : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F)) :
    ∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,
        radialAdjointFromResponseL F (R+sphereSobolevDegreeL) v⟫_ℝ := by
  let D := R+sphereSobolevDegreeL
  let C := coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))
  let T := coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)
  let N := C.comp D+T
  have hWeak := midpoint_radial_reconstructed_conormal_weak ha hc F hField hStrong hNormal R hR
  have hSym := conormal_midpoint_symmetric (nativeWeakConormalEndpoint a 0 0 ha sphereFischerInner) N hWeak
    (nativeWeakConormal_symmetric ha hc hs)
  have hD : D = conormalRadialL F N := by
    have hC := coarseSphereScalarMulL_isInvertible_of_pos
      (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))) hPos
    apply ContinuousLinearMap.ext
    intro u
    change D u = C.inverse (C (D u)+T u-T u)
    rw [add_sub_cancel_right,hC.inverse_apply_self]
  exact radialAdjointFromResponseL_pairing F D N hD hPos hSym

end ShrinkingSpheres
