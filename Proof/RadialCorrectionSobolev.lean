import Proof.RadialCorrectionLinear
import Proof.Archive.NativeRadialDriftInclusion
import Proof.Archive.SharpRadialHarmonicCoefficientCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def radialCorrectionVector (q : X →L[ℝ] ℝ) : X := WithLp.toLp 2 (fun i => q (axis i))

def radialCorrectionSobolevL (s : ℝ) (q : X →L[ℝ] ℝ) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  sphereSobolevRadialDriftL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s (radialCorrectionVector q)

def radialCorrectionAdjointSobolevL (s : ℝ) (q : X →L[ℝ] ℝ) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  sphereSobolevRadialDriftAdjointL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s (radialCorrectionVector q)

theorem radialCorrectionSobolevL_single (s : ℝ) (q : X →L[ℝ] ℝ)
    (k : ℕ) (a : harmonicSphereSubspace (k+1)) :
    radialCorrectionSobolevL s q (sphereSobolevSingleL s (k+1) a) =
      sphereSobolevSingleL s k (radialDriftBlockL sphereFischerInner (radialCorrectionVector q) k a) :=
  sphereSobolevRadialDriftL_single _ _ _ s _ k a

theorem radialCorrectionSobolevL_constant (s : ℝ) (q : X →L[ℝ] ℝ) (a : harmonicSphereSubspace 0) :
    radialCorrectionSobolevL s q (sphereSobolevSingleL s 0 a) = 0 :=
  sphereSobolevRadialDriftL_constant _ _ _ s _ a

theorem radialCorrectionSobolevL_zero (q : X →L[ℝ] ℝ) :
    radialCorrectionSobolevL 0 q = radialCorrectionCovectorL q := by
  apply sphereSobolev_clm_eq_of_single 0
  intro k a
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hR : radialCorrectionCovectorL q (sphereSobolevSingleL 0 k a) =
      Z (radialDriftTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
        (radialCorrectionVector q) (a:SphereL2)) := by
    rw [radialCorrectionCovectorL_apply]
    change (1:ℝ)⁻¹ • Z (radialDriftTraceL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
      (radialCorrectionVector q) (Z.symm (sphereSobolevSingleL 0 k a))) = _
    rw [inv_one,one_smul,← zeroEquiv_harmonic_subtype,Z.symm_apply_apply]
  rw [hR]
  cases k with
  | zero => rw [radialCorrectionSobolevL_constant,radialDriftTraceL_constant,map_zero]
  | succ k => rw [radialCorrectionSobolevL_single,radialDriftTraceL_subtype,zeroEquiv_harmonic_subtype]

theorem radialCorrectionAdjointSobolevL_zero (q : X →L[ℝ] ℝ) :
    radialCorrectionAdjointSobolevL 0 q = (radialCorrectionCovectorL q).adjoint := by
  change (sphereSobolevRadialDriftL sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    (-(0:ℝ)) (radialCorrectionVector q)).adjoint = _
  rw [neg_zero]
  exact congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => T.adjoint) (radialCorrectionSobolevL_zero q)

theorem radialCorrectionSobolevL_coarse (q : X →L[ℝ] ℝ) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (radialCorrectionSobolevL 1 q u) =
      radialCorrectionCovectorL q (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  have h := sphereSobolevInclusionL_radialDrift sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    1 0 (by norm_num) (radialCorrectionVector q) u
  exact h.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    T (sphereSobolevInclusionL 1 0 (by norm_num) u)) (radialCorrectionSobolevL_zero q))

theorem radialCorrectionAdjointSobolevL_coarse (q : X →L[ℝ] ℝ) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (radialCorrectionAdjointSobolevL 1 q u) =
      (radialCorrectionCovectorL q).adjoint (sphereSobolevInclusionL 1 0 (by norm_num) u) := by
  have h := sphereSobolevInclusionL_radialDriftAdjoint sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics
    1 0 (by norm_num) (radialCorrectionVector q) u
  exact h.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    T (sphereSobolevInclusionL 1 0 (by norm_num) u)) (radialCorrectionAdjointSobolevL_zero q))

lemma radialCorrectionVector_coordinate_sum_le (q : X →L[ℝ] ℝ) :
    (∑ i : I,|(radialCorrectionVector q) i|) ≤ 3*‖q‖ := by
  have h (i : I) : |(radialCorrectionVector q) i| ≤ ‖q‖ := by
    simpa only [radialCorrectionVector,Real.norm_eq_abs,norm_axis,mul_one] using q.le_opNorm (axis i)
  rw [Fin.sum_univ_three]
  nlinarith only [h 0,h 1,h 2]

theorem norm_radialCorrectionSobolevL_one_le (q : X →L[ℝ] ℝ) :
    ‖radialCorrectionSobolevL 1 q‖ ≤ 6*‖q‖ := by
  have h := norm_sphereSobolevRadialDriftL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics 1 (radialCorrectionVector q)
  have hB : radialDriftSobolevBound 1 = 1 := by norm_num [radialDriftSobolevBound]
  rw [hB,mul_one] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (radialCorrectionVector_coordinate_sum_le q) (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring))

theorem norm_radialCorrectionAdjointSobolevL_one_le (q : X →L[ℝ] ℝ) :
    ‖radialCorrectionAdjointSobolevL 1 q‖ ≤ 12*‖q‖ := by
  have h := norm_sphereSobolevRadialDriftAdjointL_le sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics 1 (radialCorrectionVector q)
  have hB : radialDriftSobolevBound (-1) = 2 := by norm_num [radialDriftSobolevBound]
  rw [hB] at h
  exact h.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (radialCorrectionVector_coordinate_sum_le q) (by norm_num : (0:ℝ) ≤ 2))
      (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring))

end ShrinkingSpheres
