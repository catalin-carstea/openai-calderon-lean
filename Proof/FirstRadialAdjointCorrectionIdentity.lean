import Proof.FirstConormalDegreeRealization
import Proof.RadialCorrectionLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

/-- Shared identification of the first physical adjoint correction from the
    true scalar first-conormal symmetry. -/
theorem first_radial_adjoint_correction_scaled (F0 F1 : SmoothCoefficientMatrix 2)
    (c : ℝ) (hc : 0 < c) (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hF1 : ∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) z = ell z*(1:Mat) i j)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible) :
    c⁻¹ • (firstConormalOneL F1 c ell-sphereSobolevDegreeL.comp
      (oneBoundaryCoefficientMulL (normalCoefficientJet F1))) =
      (coarseFirstRadialVariationL c ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) :=
  conormal_first_adjoint_scaled _ _ _ _ c hc.ne' rfl
    (oneBoundaryCoefficientMulL_coarse (normalCoefficientJet F1))
    (coarseSphereScalarMulL_symmetric _) (firstConormalOneL_symmetric F0 F1 c hc ell hF0 hF1 ha1 hInv0)

theorem first_radial_adjoint_correction_normalized (F0 F1 : SmoothCoefficientMatrix 2)
    (ell : X →L[ℝ] ℝ)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (hF1 : ∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) z = ell z*(1:Mat) i j)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible) :
    (radialCorrectionCovectorL ell).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) =
      (radialCorrectionCovectorL ell).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
        (coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F1)))).comp sphereSobolevDegreeL-
          sphereSobolevDegreeL.comp (oneBoundaryCoefficientMulL (normalCoefficientJet F1)) := by
  have hInv : (strongDirichletOperator fixedSobolevCalculus 0 ((1:ℝ) • F0)).IsInvertible := by simpa only [one_smul] using hInv0
  have h := first_radial_adjoint_correction_scaled F0 F1 1 (by norm_num) ell hF0 hF1 ha1 hInv
  simpa only [inv_one,one_smul,firstConormalOneL,← radialCorrectionCovectorL_apply] using h.symm

end ShrinkingSpheres
