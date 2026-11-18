import Proof.CommonSupportRadialAdjointRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- All four native boundary factors used by radial adjunction depend only
    on the same coefficient matrix on the actual sphere. -/
theorem radial_boundary_operators_congr_sphere (F G : SmoothCoefficientMatrix 2)
    (hFG : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = coefficientMatrixField 2 G w.val) :
    coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F))) =
      coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet G))) ∧
    oneBoundaryCoefficientMulL (normalCoefficientJet F) = oneBoundaryCoefficientMulL (normalCoefficientJet G) ∧
    coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j) =
      coarseBoundaryTangentialL (fun j => tangentCoefficientJet G j) ∧
    adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j) =
      adjointBoundaryTangentialL (fun j => tangentCoefficientJet G j) := by
  have hN : smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)) =
      smoothSphereValue (coefficientSmoothData (normalCoefficientJet G)) := by
    ext w
    exact normalCoefficientJet_value_congr_sphere F G hFG w
  have hT (j : I) : smoothSphereValue (coefficientSmoothData (tangentCoefficientJet F j)) =
      smoothSphereValue (coefficientSmoothData (tangentCoefficientJet G j)) := by
    ext w
    exact tangentCoefficientJet_value_congr_sphere F G hFG j w
  have hT1 (j : I) : oneBoundaryCoefficientMulL (tangentCoefficientJet F j) =
      oneBoundaryCoefficientMulL (tangentCoefficientJet G j) :=
    oneBoundaryCoefficientMulL_congr_sphere _ _ (tangentCoefficientJet_value_congr_sphere F G hFG j)
  refine ⟨congrArg coarseSphereScalarMulL hN,
    oneBoundaryCoefficientMulL_congr_sphere _ _ (normalCoefficientJet_value_congr_sphere F G hFG),?_,?_⟩
  · simp only [coarseBoundaryTangentialL,hT]
  · simp only [adjointBoundaryTangentialL,hT1]

theorem radialAdjointFromResponseL_congr_sphere (F G : SmoothCoefficientMatrix 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hFG : ∀ w : UnitSphere,coefficientMatrixField 2 F w.val = coefficientMatrixField 2 G w.val) :
    radialAdjointFromResponseL F D = radialAdjointFromResponseL G D := by
  obtain ⟨hM0,hM1,hT,hTd⟩ := radial_boundary_operators_congr_sphere F G hFG
  simp only [radialAdjointFromResponseL,conormalRadialAdjointL,hM0,hM1,hT,hTd]

end ShrinkingSpheres
