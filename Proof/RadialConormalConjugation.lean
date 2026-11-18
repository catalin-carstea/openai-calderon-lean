import Proof.RadialBoundaryCoefficient
import Proof.RadialConormalReconstruction
import Proof.CommonSupportRadialAdjointRegularity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

lemma conormalRadial_radial_reconstruction (F : SmoothCoefficientMatrix 2) (q : UnitSphere → ℝ)
    (hRow : ∀ w : UnitSphere,∀ j : I,∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=q w*w.val j)
    (hPos : ∀ w : UnitSphere,0 < q w) (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).comp
      (conormalRadialL F N)=N := by
  have hNormal (w : UnitSphere) : 0 < coefficientValue 2 (normalCoefficientJet F) w.val := by
    rw [coefficientValue_normalCoefficientJet,boundaryNormalCoefficient_of_radial_row F q hRow]
    exact hPos w
  have hRecon := conormal_reconstruct_from_radial F N hNormal
  rw [(radial_row_tangential_operators_zero F q hRow).1,add_zero] at hRecon
  exact hRecon

lemma conormalRadialAdjoint_radial_conjugation (F : SmoothCoefficientMatrix 2) (q : UnitSphere → ℝ)
    (hRow : ∀ w : UnitSphere,∀ j : I,∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=q w*w.val j)
    (hPos : ∀ w : UnitSphere,0 < q w) (N : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    conormalRadialAdjointL F N =
      ((coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).comp
        (conormalRadialL F N)).comp (oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse := by
  unfold conormalRadialAdjointL
  rw [(radial_row_tangential_operators_zero F q hRow).2,sub_zero,
    conormalRadial_radial_reconstruction F q hRow hPos N]
lemma radialAdjointFromResponse_radial_conjugation (F : SmoothCoefficientMatrix 2) (q : UnitSphere → ℝ)
    (hRow : ∀ w : UnitSphere,∀ j : I,∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=q w*w.val j)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    radialAdjointFromResponseL F D =
      ((coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).comp D).comp
        (oneBoundaryCoefficientMulL (normalCoefficientJet F)).inverse := by
  unfold radialAdjointFromResponseL conormalRadialAdjointL
  rw [(radial_row_tangential_operators_zero F q hRow).1,
    (radial_row_tangential_operators_zero F q hRow).2,add_zero,sub_zero]
lemma radialAdjointFromResponse_tangent_zero_flux (F : SmoothCoefficientMatrix 2)
    (hT : coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j)=0)
    (hTa : adjointBoundaryTangentialL (fun j => tangentCoefficientJet F j)=0)
    (hM : (oneBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    (radialAdjointFromResponseL F D).comp (oneBoundaryCoefficientMulL (normalCoefficientJet F))=
      (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).comp D := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [radialAdjointFromResponseL,conormalRadialAdjointL,hT,hTa,add_zero,sub_zero,
    ContinuousLinearMap.comp_apply,hM.inverse_apply_self]
end ShrinkingSpheres
