import Proof.ParallelScalarFirstHighSections
import Proof.DegreeAdjointHigherEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma shifted_degree_rotation_commute (s : ℝ) (i j : I) (u : SphereSobolev s) :
    sphereSobolevRotationL (s-1) i j (sphereSobolevShiftedDegreeL s u)=
      sphereSobolevShiftedDegreeL (s-1) (sphereSobolevRotationL s i j u) := by
  apply sphereSobolev_ext ((s-1)-1)
  intro k
  rw [sphereSobolevCoefficientL_rotation,sphereSobolevCoefficientL_shiftedDegree,
    sphereSobolevCoefficientL_shiftedDegree,sphereSobolevCoefficientL_rotation,map_smul]

/-- Degree is parallel in the genuine graded covariant derivative. -/
lemma shifted_degree_covariant_derivative (s : ℝ) (d : Data)
    (U : X → SphereSobolev s) (y a : X) (hU : DifferentiableAt ℝ U y) :
    gradedSphereSectionCovariantDerivative (s-1) d (fun x => sphereSobolevShiftedDegreeL s (U x)) y a=
      sphereSobolevShiftedDegreeL (s-1) (gradedSphereSectionCovariantDerivative s d U y a) := by
  have hD : fderiv ℝ (fun x => sphereSobolevShiftedDegreeL s (U x)) y a=
      sphereSobolevShiftedDegreeL s (fderiv ℝ U y a) := by
    have h := DFunLike.congr_fun ((sphereSobolevShiftedDegreeL s).hasFDerivAt.comp y hU.hasFDerivAt).fderiv a
    simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using h
  simp only [gradedSphereSectionCovariantDerivative,hD,map_sub,map_sum,map_smul,
    shifted_degree_rotation_commute]
  congr 1
  exact sphereSobolevShiftedDegreeL_inclusion s (s-1) (by linarith) (fderiv ℝ U y a)

lemma graded_covariant_threeHalf_eq (d : Data) (U : X → SphereSobolev (3/2:ℝ)) (y a : X) :
    gradedSphereSectionCovariantDerivative (3/2:ℝ) d U y a=halfSectionCovariantDerivativeL d U y a := by
  have hI : sphereSobolevInclusionL (3/2:ℝ) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simp only [gradedSphereSectionCovariantDerivative,halfSectionCovariantDerivativeL_apply,
    frameAngularConnectionHigherL,_root_.sum_apply,_root_.smul_apply,hI]

def scalarModelDegreeSection (U : X → SphereSobolev (5/2:ℝ)) (x : X) : SphereSobolev (3/2:ℝ) :=
  sphereSobolevShiftedDegreeL (5/2:ℝ) (U x)

def scalarModelShiftedDegreeSection (U : X → SphereSobolev (5/2:ℝ)) (x : X) : SphereSobolev (3/2:ℝ) :=
  scalarModelDegreeSection U x-sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)

lemma scalarModelDegreeSection_half_inclusion (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (scalarModelDegreeSection U y)=
      degreeHigherL (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  have h := sphereSobolevShiftedDegreeL_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simpa only [hI,scalarModelDegreeSection,degreeHigherL] using h

lemma scalarModelDegreeSection_covariant_derivative (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    halfSectionCovariantDerivativeL d (scalarModelDegreeSection U) y a=
      degreeHigherL (fiveHalfCovariantDerivative d U a y) := by
  have h := shifted_degree_covariant_derivative (5/2:ℝ) d U y a hU
  have hG : gradedSphereSectionCovariantDerivative ((5/2:ℝ)-1) d (scalarModelDegreeSection U) y a=
      gradedSphereSectionCovariantDerivative (3/2:ℝ) d (scalarModelDegreeSection U) y a := by congr 1 <;> norm_num
  have hD : sphereSobolevShiftedDegreeL ((5/2:ℝ)-1)=degreeHigherL := by
    unfold degreeHigherL
    congr 1
    norm_num
  rw [hD] at h
  change gradedSphereSectionCovariantDerivative ((5/2:ℝ)-1) d (scalarModelDegreeSection U) y a=_ at h
  rw [hG,graded_covariant_threeHalf_eq] at h
  exact h

lemma half_covariant_derivative_sub (d : Data) (U V : X → SphereSobolev (3/2:ℝ))
    (y a : X) (hU : DifferentiableAt ℝ U y) (hV : DifferentiableAt ℝ V y) :
    halfSectionCovariantDerivativeL d (fun x => U x-V x) y a=
      halfSectionCovariantDerivativeL d U y a-halfSectionCovariantDerivativeL d V y a := by
  rw [halfSectionCovariantDerivativeL_apply,halfSectionCovariantDerivativeL_apply,halfSectionCovariantDerivativeL_apply]
  have hD : fderiv ℝ (fun x => U x-V x) y a=fderiv ℝ U y a-fderiv ℝ V y a := by
    have h := DFunLike.congr_fun (fderiv_sub hU hV) a
    change fderiv ℝ (fun x => U x-V x) y a=_ at h
    simpa only [_root_.sub_apply] using h
  rw [hD,map_sub,map_sub]
  abel

lemma scalarModelShiftedDegreeSection_covariant_derivative (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y a : X) (hU : DifferentiableAt ℝ U y) :
    halfSectionCovariantDerivativeL d (scalarModelShiftedDegreeSection U) y a=
      degreeHigherL (fiveHalfCovariantDerivative d U a y)-
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U a y) := by
  change halfSectionCovariantDerivativeL d (fun x => scalarModelDegreeSection U x-
    sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y a=_
  have hD : DifferentiableAt ℝ (scalarModelDegreeSection U) y := by
    let T : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) := sphereSobolevShiftedDegreeL (5/2:ℝ)
    change DifferentiableAt ℝ (fun x => T (U x)) y
    simpa only [Function.comp_def] using T.differentiableAt.comp y hU
  have hV : DifferentiableAt ℝ (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y := by
    simpa only [Function.comp_def] using
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).differentiableAt.comp y hU
  rw [half_covariant_derivative_sub d (scalarModelDegreeSection U)
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y a hD hV,
    scalarModelDegreeSection_covariant_derivative d U y a hU,
    ← fiveHalfCovariantDerivative_half_inclusion d U y a hU]

end ShrinkingSpheres.ParallelEnergy
