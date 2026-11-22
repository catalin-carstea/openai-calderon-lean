module

public import Proof.CalderonN.SmoothTraceCommutatorBounds

import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Tactic

/-! The angular rotations form the usual Lie algebra on the common
smooth sphere core. -/

public section

noncomputable section
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem axis_entry_swap (i j : I dim) : axis i j = axis j i := by
  by_cases h : i=j
  · subst j
    rfl
  · simp [axis,PiLp.single_apply,h,Ne.symm h]

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem rotationVector_eq_axis (i j : I dim) (z : X dim) :
    rotationVector i j z = z i • axis j-z j • axis i := rfl

private theorem rotationVector_bracket (i j k l : I dim) (z : X dim) :
    VectorField.lieBracket ℝ (rotationVector i j) (rotationVector k l) z =
      axis j k • rotationVector i l z-axis i k • rotationVector j l z-
      axis j l • rotationVector i k z+axis i l • rotationVector j k z := by
  have hRot (a b : I dim) : rotationVector a b = (ballRotationGeneratorL a b : X dim → X dim) :=
    funext fun w => (ballRotationGeneratorL_apply a b w).symm
  rw [VectorField.lieBracket,hRot k l,hRot i j,ContinuousLinearMap.fderiv,ContinuousLinearMap.fderiv]
  simp only [ballRotationGeneratorL_apply,rotationVector_eq_axis]
  ext a
  simp only [PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  rw [axis_entry_swap l i,axis_entry_swap k i,axis_entry_swap l j,axis_entry_swap k j]
  ring

theorem smoothTraceRotation_comm_rotation (i j k l : I dim) :
    smoothTraceAngularComm i j (smoothSphereTraceRotation k l) =
      axis j k • smoothSphereTraceRotation i l-axis i k • smoothSphereTraceRotation j l-
      axis j l • smoothSphereTraceRotation i k+axis i l • smoothSphereTraceRotation j k := by
  ext u : 1
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let F : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  change smoothTraceAngularComm i j (smoothSphereTraceRotation k l) (smoothSphereTrace F) =
    (axis j k • smoothSphereTraceRotation i l-axis i k • smoothSphereTraceRotation j l-
      axis j l • smoothSphereTraceRotation i k+axis i l • smoothSphereTraceRotation j k) (smoothSphereTrace F)
  simp only [smoothTraceAngularComm,LinearMap.sub_apply,LinearMap.add_apply,Module.End.mul_apply,
    LinearMap.smul_apply,smoothSphereTraceRotation_apply]
  apply Subtype.ext
  funext z
  simp only [Submodule.coe_sub,Submodule.coe_add,Submodule.coe_smul,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
    smoothSphereTrace_apply]
  have hLie := VectorField.fderiv_apply_lieBracket (V:=rotationVector i j) (W:=rotationVector k l)
    (F.2.contDiffAt (x:=(z:X dim))) (by simp)
    ((contDiff_rotationVector k l).differentiable (by simp) z)
    ((contDiff_rotationVector i j).differentiable (by simp) z)
  change sphereRotationDerivative i j (sphereRotationDerivative k l F.1) z-
    sphereRotationDerivative k l (sphereRotationDerivative i j F.1) z = _
  change fderiv ℝ (fun t => fderiv ℝ F.1 t (rotationVector k l t)) (z:X dim) (rotationVector i j z)-
    fderiv ℝ (fun t => fderiv ℝ F.1 t (rotationVector i j t)) (z:X dim) (rotationVector k l z) = _
  rw [← hLie,rotationVector_bracket]
  simp only [map_add,map_sub,map_smul,smul_eq_mul,sphereRotationDerivative]

omit [Nontrivial (Fin dim)] in
private theorem abs_axis_entry_le_one (i j : I dim) : |axis i j| ≤ 1 := by
  by_cases h : i=j
  · subst j; simp [axis]
  · simp [axis,PiLp.single_apply,h,Ne.symm h]

theorem smoothTraceRotation_comm_rotation_bound (hn : 3 ≤ dim) (i j k l : I dim) :
    SmoothTraceAngularBound hn 1 (8*(dim:ℝ)) (smoothTraceAngularComm i j (smoothSphereTraceRotation k l)) := by
  rw [smoothTraceRotation_comm_rotation]
  have hC : 0 ≤ (2*(dim:ℝ)) := by positivity
  have h (a b c d : I dim) : SmoothTraceAngularBound hn 1 (2*(dim:ℝ))
      (axis a b • smoothSphereTraceRotation c d) :=
    ((smoothTraceRotation_angularBound hn c d).const_smul (axis a b)).enlarge
      ((mul_le_mul_of_nonneg_right (abs_axis_entry_le_one a b) hC).trans_eq (one_mul _))
  exact ((((h j k i l).sub (h i k j l)).sub (h j l i k)).add (h i l j k)).enlarge (by ring_nf; rfl)

end CalderonN
