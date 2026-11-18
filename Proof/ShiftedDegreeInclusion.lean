import Proof.DegreeCovariantGraph
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Physical degree respects genuine inclusions at every Sobolev level. -/
lemma sphereSobolevShiftedDegreeL_inclusion (s t : ℝ) (hst : t ≤ s) (u : SphereSobolev s) :
    sphereSobolevInclusionL (s-1) (t-1) (by linarith) (sphereSobolevShiftedDegreeL s u)=
      sphereSobolevShiftedDegreeL t (sphereSobolevInclusionL s t hst u) := by
  apply sphereSobolev_ext (t-1)
  intro k
  rw [sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_shiftedDegree,
    sphereSobolevCoefficientL_shiftedDegree,sphereSobolevCoefficientL_inclusion]

lemma sphereSobolevDegreeL_half (v : SphereSobolev 1) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevDegreeL v)=
      sphereSobolevShiftedDegreeL (1/2:ℝ) (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v) := by
  have h := sphereSobolevShiftedDegreeL_inclusion 1 (1/2:ℝ) (by norm_num) v
  rw [sphereSobolevShiftedDegreeL_one_eq_degree] at h
  have hI : sphereSobolevInclusionL ((1:ℝ)-1) ((1/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at h
  exact h

lemma sphereSobolevShiftedDegreeL_threehalf_high (u : SphereSobolev 2) :
    sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (sphereSobolevShiftedDegreeL 2 u)=
      sphereSobolevShiftedDegreeL (3/2:ℝ) (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  have h := sphereSobolevShiftedDegreeL_inclusion 2 (3/2:ℝ) (by norm_num) u
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at h
  exact h
end ShrinkingSpheres
