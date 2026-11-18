import Proof.CoordinateMultiplierSobolev
import Proof.RadialCorrectionDegreeCommutator
import Proof.CanonicalFirstRadialCorrection
import Proof.ScaledLogRadiusBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def firstAdjointCorrectionSobolevL (s : ℝ) (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  (radialCorrectionAdjointSobolevL s q).comp (coordinateMultiplierSobolevL s i)+
    t • radialCorrectionAdjointSobolevL s q

theorem firstAdjointCorrectionSobolevL_inclusion (s t : ℝ) (hst : t ≤ s)
    (q : X →L[ℝ] ℝ) (b : ℝ) (i : I) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (firstAdjointCorrectionSobolevL s q b i u) =
      firstAdjointCorrectionSobolevL t q b i (sphereSobolevInclusionL s t hst u) := by
  have hM := sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s t hst (axis i) u
  have hFirst := (sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s t hst (radialCorrectionVector q) (coordinateMultiplierSobolevL s i u)).trans
      (congrArg (radialCorrectionAdjointSobolevL t q) hM)
  have hLast := sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s t hst (radialCorrectionVector q) u
  have hSum := congrArg₂ (fun v w : SphereSobolev t => v+b • w) hFirst hLast
  simpa only [firstAdjointCorrectionSobolevL,_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,map_add,map_smul,radialCorrectionAdjointSobolevL,
    coordinateMultiplierSobolevL] using hSum

theorem norm_firstAdjointCorrectionSobolevL_le (s : ℝ) (q : X →L[ℝ] ℝ) (t : ℝ) (i : I) :
    ‖firstAdjointCorrectionSobolevL s q t i‖ ≤
      6*‖q‖*radialDriftSobolevBound (-s)*
        (2*(radialDriftSobolevBound s+radialDriftSobolevBound (-s))+|t|) := by
  let B := radialDriftSobolevBound (-s)
  let W := 2*(radialDriftSobolevBound s+B)+|t|
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hW : 0 ≤ W := by
    have hBs : 0 ≤ radialDriftSobolevBound s := zero_le_one.trans (le_max_left _ _)
    dsimp only [W]
    positivity
  have hP := norm_sphereSobolevAdjointCoordinateL_le sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s (radialCorrectionVector q) i
  have hR := norm_sphereSobolevRadialDriftAdjointL_le sphereFischerInner orthogonalSphereHarmonics
    denseSphereHarmonics s (radialCorrectionVector q)
  have hComp : ‖(radialCorrectionAdjointSobolevL s q).comp (coordinateMultiplierSobolevL s i)‖ ≤
      ((2*∑ j : I,|(radialCorrectionVector q) j|)*B)*
        (2*(radialDriftSobolevBound s+B)) := hP
  calc
    _ ≤ ‖(radialCorrectionAdjointSobolevL s q).comp (coordinateMultiplierSobolevL s i)‖+
        ‖t • radialCorrectionAdjointSobolevL s q‖ := norm_add_le _ _
    _ ≤ ((2*∑ j : I,|(radialCorrectionVector q) j|)*B)*(2*(radialDriftSobolevBound s+B))+
        |t| *((2*∑ j : I,|(radialCorrectionVector q) j|)*B) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add hComp (mul_le_mul_of_nonneg_left hR (abs_nonneg _))
    _ = ((2*∑ j : I,|(radialCorrectionVector q) j|)*B)*W := by dsimp only [W];ring
    _ ≤ ((2*(3*‖q‖))*B)*W :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (radialCorrectionVector_coordinate_sum_le q) (by norm_num)) hB) hW
    _ = _ := by dsimp only [W,B];ring

end ShrinkingSpheres
