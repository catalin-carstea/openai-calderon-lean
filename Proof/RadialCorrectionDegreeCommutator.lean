import Proof.RadialCorrectionSobolev
import Proof.FlatDegreeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem radialCorrectionAdjointSobolevL_single (s : ℝ) (q : X →L[ℝ] ℝ)
    (k : ℕ) (a : harmonicSphereSubspace k) :
    radialCorrectionAdjointSobolevL s q (sphereSobolevSingleL s k a) =
      sphereSobolevSingleL s (k+1) (radialDriftAdjointBlockL sphereFischerInner (radialCorrectionVector q) k a) :=
  sphereSobolevRadialDriftAdjointL_single _ _ _ s _ k a

/-- The correction lowers harmonic degree by exactly one, including its
    vanishing action on constants. The commutator is bounded on L2. -/
theorem degree_radialCorrection_commutator (q : X →L[ℝ] ℝ) :
    sphereSobolevDegreeL.comp (radialCorrectionSobolevL 1 q)-
      (radialCorrectionCovectorL q).comp sphereSobolevDegreeL =
        -(radialCorrectionCovectorL q).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  change sphereSobolevDegreeL (radialCorrectionSobolevL 1 q (sphereSobolevSingleL 1 k a))-
      radialCorrectionCovectorL q (sphereSobolevDegreeL (sphereSobolevSingleL 1 k a)) =
        -(radialCorrectionCovectorL q (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 k a)))
  rw [← radialCorrectionSobolevL_zero q]
  cases k with
  | zero => simp only [radialCorrectionSobolevL_constant,sphereSobolevDegreeL_single,
      sphereSobolevInclusionL_single,Nat.cast_zero,zero_smul,map_zero,sub_zero,neg_zero]
  | succ k =>
    simp only [radialCorrectionSobolevL_single,sphereSobolevDegreeL_single,
      sphereSobolevInclusionL_single,map_smul]
    push_cast
    module

/-- The true adjoint raises harmonic degree by one; its degree commutator
    has the opposite sign and the same bounded L2 correction. -/
theorem degree_radialCorrectionAdjoint_commutator (q : X →L[ℝ] ℝ) :
    sphereSobolevDegreeL.comp (radialCorrectionAdjointSobolevL 1 q)-
      (radialCorrectionCovectorL q).adjoint.comp sphereSobolevDegreeL =
        (radialCorrectionCovectorL q).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply sphereSobolev_clm_eq_of_single 1
  intro k a
  change sphereSobolevDegreeL (radialCorrectionAdjointSobolevL 1 q (sphereSobolevSingleL 1 k a))-
      (radialCorrectionCovectorL q).adjoint (sphereSobolevDegreeL (sphereSobolevSingleL 1 k a)) =
        (radialCorrectionCovectorL q).adjoint (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevSingleL 1 k a))
  rw [← radialCorrectionAdjointSobolevL_zero q]
  simp only [radialCorrectionAdjointSobolevL_single,sphereSobolevDegreeL_single,
    sphereSobolevInclusionL_single,map_smul]
  push_cast
  module

end ShrinkingSpheres
