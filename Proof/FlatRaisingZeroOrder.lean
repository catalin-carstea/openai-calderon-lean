import Proof.NegativeScalarCommutatorGraph
import Proof.Archive.NativeRadialDriftInclusion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The fixed order-zero term in the reordered flat raising operator.
    Its operator norms at each fixed Sobolev level are universal constants. -/
def flatRaisingZeroOrderL (s : ℝ) (i : I) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  -radialCorrectionSobolevL s (EuclideanSpace.proj (𝕜:=ℝ) i)-
    (3:ℝ) • radialCorrectionAdjointSobolevL s (EuclideanSpace.proj (𝕜:=ℝ) i)

lemma flatRaisingZeroOrderL_zero (i : I) :
    flatRaisingZeroOrderL 0 i=(2:ℝ) • coordinateMultiplierSobolevL 0 i+coordinateDegreeCommutatorL i := by
  rw [coordinateMultiplierSobolevL_radial]
  simp only [flatRaisingZeroOrderL,coordinateDegreeCommutatorL,
    radialCorrectionSobolevL_zero,radialCorrectionAdjointSobolevL_zero]
  module

lemma flatRaisingZeroOrderL_inclusion (s t : ℝ) (hts : t ≤ s) (i : I) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (flatRaisingZeroOrderL s i u)=
      flatRaisingZeroOrderL t i (sphereSobolevInclusionL s t hts u) := by
  simp only [flatRaisingZeroOrderL,_root_.sub_apply,_root_.neg_apply,_root_.smul_apply,
    radialCorrectionSobolevL,radialCorrectionAdjointSobolevL,map_neg,map_sub,map_smul,
    sphereSobolevInclusionL_radialDrift,sphereSobolevInclusionL_radialDriftAdjoint]
end ShrinkingSpheres
